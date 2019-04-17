// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package backend

import (
	"bytes"
	"crypto/ecdsa"
	"encoding/json"
	"io/ioutil"
	"math/big"
	"os"
	"sync"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/istanbul"
	istanbulCore "github.com/ethereum/go-ethereum/consensus/istanbul/core"
	"github.com/ethereum/go-ethereum/consensus/istanbul/validator"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/event"
	"github.com/ethereum/go-ethereum/log"
	lru "github.com/hashicorp/golang-lru"
)

const (
	// fetcherID is the ID indicates the block is from Istanbul engine
	fetcherID = "istanbul"
)

var validatorFilePath = "/home/david/pruebas/validator-pool.json"

var catchups map[common.Address]uint8
var validatorPoolMap map[common.Address]bool
var validatorPoolSlice []common.Address

var validatorSubstitutions map[common.Address]common.Address

var emptyAddress = common.HexToAddress("0x0000000000000000000000000000000000000000")

// New creates an Ethereum backend for Istanbul core engine.
func New(config *istanbul.Config, privateKey *ecdsa.PrivateKey, db ethdb.Database) consensus.Istanbul {
	// Allocate the snapshot caches and create the engine
	recents, _ := lru.NewARC(inmemorySnapshots)
	recentMessages, _ := lru.NewARC(inmemoryPeers)
	knownMessages, _ := lru.NewARC(inmemoryMessages)
	backend := &backend{
		config:           config,
		istanbulEventMux: new(event.TypeMux),
		privateKey:       privateKey,
		address:          crypto.PubkeyToAddress(privateKey.PublicKey),
		logger:           log.New(),
		db:               db,
		commitCh:         make(chan *types.Block, 1),
		recents:          recents,
		candidates:       make(map[common.Address]bool),
		coreStarted:      false,
		recentMessages:   recentMessages,
		knownMessages:    knownMessages,
	}
	backend.core = istanbulCore.New(backend, backend.config)

	catchups = make(map[common.Address]uint8)
	validatorSubstitutions = make(map[common.Address]common.Address)
	validatorPoolMap, validatorPoolSlice = backend.loadValidatorPool(validatorFilePath)

	return backend
}

// ----------------------------------------------------------------------------

type backend struct {
	config           *istanbul.Config
	istanbulEventMux *event.TypeMux
	privateKey       *ecdsa.PrivateKey
	address          common.Address
	core             istanbulCore.Engine
	logger           log.Logger
	db               ethdb.Database
	chain            consensus.ChainReader
	currentBlock     func() *types.Block
	hasBadBlock      func(hash common.Hash) bool

	// the channels for istanbul engine notifications
	commitCh          chan *types.Block
	proposedBlockHash common.Hash
	sealMu            sync.Mutex
	coreStarted       bool
	coreMu            sync.RWMutex

	// Current list of candidates we are pushing
	candidates map[common.Address]bool
	// Protects the signer fields
	candidatesLock sync.RWMutex
	// Snapshots for recent block to speed up reorgs
	recents *lru.ARCCache

	// event subscription for ChainHeadEvent event
	broadcaster consensus.Broadcaster

	recentMessages *lru.ARCCache // the cache of peer's messages
	knownMessages  *lru.ARCCache // the cache of self messages

	txCachUp event.Feed
}

// zekun: HACK
func (sb *backend) CalcDifficulty(chain consensus.ChainReader, time uint64, parent *types.Header) *big.Int {
	return new(big.Int)
}

// Address implements istanbul.Backend.Address
func (sb *backend) Address() common.Address {
	return sb.address
}

// Validators implements istanbul.Backend.Validators
func (sb *backend) Validators(proposal istanbul.Proposal) istanbul.ValidatorSet {
	return sb.getValidators(proposal.Number().Uint64(), proposal.Hash())
}

// Broadcast implements istanbul.Backend.Broadcast
func (sb *backend) Broadcast(valSet istanbul.ValidatorSet, payload []byte) error {
	// send to others
	sb.Gossip(valSet, payload)
	// send to self
	msg := istanbul.MessageEvent{
		Payload: payload,
	}
	go sb.istanbulEventMux.Post(msg)
	return nil
}

// Broadcast implements istanbul.Backend.Gossip
func (sb *backend) Gossip(valSet istanbul.ValidatorSet, payload []byte) error {
	hash := istanbul.RLPHash(payload)
	sb.knownMessages.Add(hash, true)

	targets := make(map[common.Address]bool)
	for _, val := range valSet.List() {
		if val.Address() != sb.Address() {
			targets[val.Address()] = true
		}
	}

	if sb.broadcaster != nil && len(targets) > 0 {
		ps := sb.broadcaster.FindPeers(targets)
		for addr, p := range ps {
			ms, ok := sb.recentMessages.Get(addr)
			var m *lru.ARCCache
			if ok {
				m, _ = ms.(*lru.ARCCache)
				if _, k := m.Get(hash); k {
					// This peer had this event, skip it
					continue
				}
			} else {
				m, _ = lru.NewARC(inmemoryMessages)
			}

			m.Add(hash, true)
			sb.recentMessages.Add(addr, m)

			go p.Send(istanbulMsg, payload)
		}
	}
	return nil
}

// Commit implements istanbul.Backend.Commit
func (sb *backend) Commit(proposal istanbul.Proposal, seals [][]byte) error {
	// Check if the proposal is a valid block
	block := &types.Block{}
	block, ok := proposal.(*types.Block)
	if !ok {
		sb.logger.Error("Invalid proposal, %v", proposal)
		return errInvalidProposal
	}

	h := block.Header()
	// Append seals into extra-data
	err := writeCommittedSeals(h, seals)
	if err != nil {
		return err
	}
	// update block's header
	block = block.WithSeal(h)

	sb.logger.Info("Committed", "address", sb.Address(), "hash", proposal.Hash(), "number", proposal.Number().Uint64())
	// - if the proposed and committed blocks are the same, send the proposed hash
	//   to commit channel, which is being watched inside the engine.Seal() function.
	// - otherwise, we try to insert the block.
	// -- if success, the ChainHeadEvent event will be broadcasted, try to build
	//    the next block and the previous Seal() will be stopped.
	// -- otherwise, a error will be returned and a round change event will be fired.
	if sb.proposedBlockHash == block.Hash() {
		// feed block hash to Seal() and wait the Seal() result
		sb.commitCh <- block
		return nil
	}

	if sb.broadcaster != nil {
		sb.broadcaster.Enqueue(fetcherID, block)
	}
	return nil
}

// EventMux implements istanbul.Backend.EventMux
func (sb *backend) EventMux() *event.TypeMux {
	return sb.istanbulEventMux
}

// Verify implements istanbul.Backend.Verify
func (sb *backend) Verify(proposal istanbul.Proposal) (time.Duration, error) {
	// Check if the proposal is a valid block
	block := &types.Block{}
	block, ok := proposal.(*types.Block)
	if !ok {
		sb.logger.Error("Invalid proposal, %v", proposal)
		return 0, errInvalidProposal
	}

	// check bad block
	if sb.HasBadProposal(block.Hash()) {
		return 0, core.ErrBlacklistedHash
	}

	// check block body
	txnHash := types.DeriveSha(block.Transactions())
	uncleHash := types.CalcUncleHash(block.Uncles())
	if txnHash != block.Header().TxHash {
		return 0, errMismatchTxhashes
	}
	if uncleHash != nilUncleHash {
		return 0, errInvalidUncleHash
	}

	// verify the header of proposed block
	err := sb.VerifyHeader(sb.chain, block.Header(), false)
	// ignore errEmptyCommittedSeals error because we don't have the committed seals yet
	if err == nil || err == errEmptyCommittedSeals {
		return 0, nil
	} else if err == consensus.ErrFutureBlock {
		return time.Unix(block.Header().Time.Int64(), 0).Sub(now()), consensus.ErrFutureBlock
	}
	return 0, err
}

// Sign implements istanbul.Backend.Sign
func (sb *backend) Sign(data []byte) ([]byte, error) {
	hashData := crypto.Keccak256([]byte(data))
	return crypto.Sign(hashData, sb.privateKey)
}

// CheckSignature implements istanbul.Backend.CheckSignature
func (sb *backend) CheckSignature(data []byte, address common.Address, sig []byte) error {
	signer, err := istanbul.GetSignatureAddress(data, sig)
	if err != nil {
		log.Error("Failed to get signer address", "err", err)
		return err
	}
	// Compare derived addresses
	if signer != address {
		return errInvalidSignature
	}
	return nil
}

// HasPropsal implements istanbul.Backend.HashBlock
func (sb *backend) HasPropsal(hash common.Hash, number *big.Int) bool {
	return sb.chain.GetHeader(hash, number.Uint64()) != nil
}

// GetProposer implements istanbul.Backend.GetProposer
func (sb *backend) GetProposer(number uint64) common.Address {
	if h := sb.chain.GetHeaderByNumber(number); h != nil {
		a, _ := sb.Author(h)
		return a
	}
	return common.Address{}
}

// ParentValidators implements istanbul.Backend.GetParentValidators
func (sb *backend) ParentValidators(proposal istanbul.Proposal) istanbul.ValidatorSet {
	if block, ok := proposal.(*types.Block); ok {
		return sb.getValidators(block.Number().Uint64()-1, block.ParentHash())
	}
	return validator.NewSet(nil, sb.config.ProposerPolicy)
}

func (sb *backend) getValidators(number uint64, hash common.Hash) istanbul.ValidatorSet {
	snap, err := sb.snapshot(sb.chain, number, hash, nil)
	if err != nil {
		return validator.NewSet(nil, sb.config.ProposerPolicy)
	}
	return snap.ValSet
}

func (sb *backend) LastProposal() (istanbul.Proposal, common.Address) {
	block := sb.currentBlock()

	var proposer common.Address
	if block.Number().Cmp(common.Big0) > 0 {
		var err error
		proposer, err = sb.Author(block.Header())
		if err != nil {
			sb.logger.Error("Failed to get block proposer", "err", err)
			return nil, common.Address{}
		}
	}

	// Return header only block here since we don't need block body
	return block, proposer
}

func (sb *backend) HasBadProposal(hash common.Hash) bool {
	if sb.hasBadBlock == nil {
		return false
	}
	return sb.hasBadBlock(hash)
}

func (sb *backend) SubscribeCatchUpEvent(ch chan<- istanbul.CatchUpEvent) event.Subscription {
	return sb.txCachUp.Subscribe(ch)
}

func (sb *backend) SendCatchUp(catchUp istanbul.CatchUpEvent) {
	// sb.logger.Warn("Address", "address", catchUp.Data.Address)
	// sb.logger.Warn("Old Proposer", "oldProposer", catchUp.Data.OldProposer)
	// sb.logger.Warn("New Proposer", "newProposer", catchUp.Data.NewProposer)
	// sb.logger.Warn("Validator set", "set", catchUp.Data.ValidatorSet)
	// sb.logger.Warn("Candidates", "list", sb.candidates)

	validatorPoolMap, validatorPoolSlice = sb.loadValidatorPool("/home/david/pruebas/validator-pool.json")

	address := *catchUp.Data.NewProposer

	for _, validatorAddress := range validatorPoolSlice {
		validatorPoolMap[validatorAddress] = false
	}

	for _, validator := range catchUp.Data.ValidatorSet.List() {
		validatorPoolMap[validator.Address()] = true
	}

	sb.candidatesLock.Lock()
	sb.candidates = make(map[common.Address]bool)
	sb.candidatesLock.Unlock()

	for addressToExit, addressToEnter := range validatorSubstitutions {
		sb.logger.Info("Proposing validator to enter", "address", addressToEnter)
		sb.propose(addressToEnter, true)
		if contains(catchUp.Data.ValidatorSet.List(), addressToEnter) {
			sb.logger.Info("Removing validator", "address", address)
			sb.propose(address, false)

			if !contains(catchUp.Data.ValidatorSet.List(), addressToExit) {
				sb.logger.Info("Cleaning substitution", "addressToExit", addressToExit, "addressToEnter", addressToEnter)
				delete(validatorSubstitutions, addressToExit)
				catchups[address] = 0
				index := find(validatorPoolSlice, address)
				if index < 0 {
					sb.logger.Error("Validator not in pool", "validator", address)
				}
				validatorPoolSlice = append(validatorPoolSlice[:index], validatorPoolSlice[index+1:]...)
				validatorPoolSlice = append(validatorPoolSlice, address)
				sb.writeValidatorPool(validatorFilePath, validatorPoolSlice)
			}
		}

	}

	catchups[address] = catchups[address] + 1

	// sb.logger.Warn("Pool", "map", validatorPoolMap)
	if catchups[address] >= 5 {
		sb.logger.Info("Validator substitution", "remove", address, "add", validatorSubstitutions[address])
		if bytes.Compare(validatorSubstitutions[address].Bytes(), emptyAddress.Bytes()) == 0 {
			for _, possibleValidatorAddress := range validatorPoolSlice {
				sb.logger.Info("Possible validator to enter", "address", possibleValidatorAddress)
				addressInUse := false
				for _, addressInSubstitution := range validatorSubstitutions {
					if bytes.Compare(possibleValidatorAddress.Bytes(), addressInSubstitution.Bytes()) == 0 {
						addressInUse = true
						break
					}
				}
				if !validatorPoolMap[possibleValidatorAddress] && !addressInUse && bytes.Compare(validatorSubstitutions[address].Bytes(), emptyAddress.Bytes()) == 0 {
					sb.logger.Info("Adding validator", "address", possibleValidatorAddress)
					// sb.propose(possibleValidatorAddress, true)
					validatorSubstitutions[address] = possibleValidatorAddress
					break
				}
			}
		}
	}

	sb.logger.Info("Number of catchups", "address", address, "number", catchups[address])
	// sb.logger.Warn("Candidates", "list", sb.candidates)

	sb.txCachUp.Send(catchUp)
}

// Read validator addresses from local list
// TODO try to get them with RPC and validator-nodes.json
func (sb *backend) loadValidatorPool(filepath string) (map[common.Address]bool, []common.Address) {
	// Open our jsonFile
	jsonFile, err := os.Open(filepath)
	defer jsonFile.Close()
	// if we os.Open returns an error then handle it
	if err != nil {
		sb.logger.Error("Error opening file", "err", err)
	}
	byteValue, err := ioutil.ReadAll(jsonFile)
	if err != nil {
		sb.logger.Error("Error reading file", "err", err)
	}
	sb.logger.Info("List of validators in poll", "validators", string(byteValue))

	var stringPool []string
	var addressPool []common.Address

	json.Unmarshal(byteValue, &stringPool)

	var pool = make(map[common.Address]bool)

	for _, addressStr := range stringPool {
		address := common.HexToAddress(addressStr)
		addressPool = append(addressPool, address)
		pool[address] = false
	}

	return pool, addressPool
}

func (sb *backend) writeValidatorPool(filepath string, addressList []common.Address) {
	addressString := "{"
	for index, address := range addressList {
		if index == 0 {
			addressString += "\"" + address.String() + "\""
		} else {
			addressString += ",\"" + address.String() + "\""
		}
	}
	addressString += "}"
	ioutil.WriteFile(filepath, []byte(addressString), 0644)
}

func (sb *backend) propose(address common.Address, auth bool) {
	sb.candidatesLock.Lock()
	defer sb.candidatesLock.Unlock()
	sb.candidates[address] = auth
}

func contains(s []istanbul.Validator, e common.Address) bool {
	for _, a := range s {
		if bytes.Compare(a.Address().Bytes(), e.Bytes()) == 0 {
			return true
		}
	}
	return false
}

func find(slice []common.Address, address common.Address) int {
	for i, v := range slice {
		if bytes.Compare(v.Bytes(), address.Bytes()) == 0 {
			return i
		}
	}
	return -1
}
