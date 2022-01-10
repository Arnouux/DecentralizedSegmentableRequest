// Code based on solution from student 58 to pass tests of HW2

package impl

import (
	"crypto"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/rs/xid"
	"github.com/rs/zerolog/log"
	"go.dedis.ch/cs438/peer"
	"go.dedis.ch/cs438/storage"
	"go.dedis.ch/cs438/transport"
	"go.dedis.ch/cs438/transport/channel"
	"go.dedis.ch/cs438/types"
	"golang.org/x/xerrors"

	z "go.dedis.ch/cs438/internal/testing"
)

// NewPeer creates a new peer
func NewPeer(conf peer.Configuration) peer.Peer {
	table := make(peer.RoutingTable)
	table[conf.Socket.GetAddress()] = conf.Socket.GetAddress()

	n := &node{
		conf:           conf,
		running:        false,
		stop:           make(chan bool),
		socketTimeout:  time.Second * 1,
		router:         SafeRoutingTable{table: table},
		peers:          Peers{peersSet: *NewSet()},
		rumorHistory:   RumorHistory{rumorMap: make(map[string][]types.Rumor)},
		ackChannels:    AckChannels{channelsMap: make(map[string]chan bool)},
		dataChannels:   DataChannels{channelsMap: make(map[string]chan *types.DataReplyMessage)},
		searchChannels: SearchChannels{channelsMap: make(map[string]chan string)},
		peersCatalog:   PeersCatalog{catalog: make(peer.Catalog)}}

	// Paxos
	n.tlcAccumulator = make(map[uint]int)
	n.step_to_last_value = make(map[uint]types.BlockchainBlock)
	n.TLCSent = make(map[uint]bool)
	n.eventAcceptedChan = make(chan types.PaxosAcceptMessage)
	n.tlc_change = make(chan uint)
	n.currentPaxos = n.newPaxos()

	conf.MessageRegistry.RegisterMessageCallback(&types.ChatMessage{}, n.ChatMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.RumorsMessage{}, n.RumorsMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.StatusMessage{}, n.StatusMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.AckMessage{}, n.AckMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.EmptyMessage{}, n.EmptyMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.PrivateMessage{}, n.PrivateMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.DataReplyMessage{}, n.DataReplyMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.DataRequestMessage{}, n.DataRequestMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.SearchReplyMessage{}, n.SearchReplyMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(&types.SearchRequestMessage{}, n.SearchRequestMessageExec)
	conf.MessageRegistry.RegisterMessageCallback(types.PaxosPrepareMessage{}, n.ExecPaxosPrepareMessage)
	conf.MessageRegistry.RegisterMessageCallback(types.PaxosProposeMessage{}, n.ExecPaxosProposeMessage)
	conf.MessageRegistry.RegisterMessageCallback(types.PaxosPromiseMessage{}, n.ExecPaxosPromiseMessage)
	conf.MessageRegistry.RegisterMessageCallback(types.PaxosAcceptMessage{}, n.ExecPaxosAcceptMessage)
	conf.MessageRegistry.RegisterMessageCallback(types.TLCMessage{}, n.ExecTLCMessage)
	return n
}

// node implements a peer to build a Peerster system
//
// - implements peer.Peer
type node struct {
	peer.Peer

	conf           peer.Configuration
	running        bool
	stop           chan bool
	socketTimeout  time.Duration
	router         SafeRoutingTable
	peers          Peers
	rumorHistory   RumorHistory
	ackChannels    AckChannels
	dataChannels   DataChannels
	searchChannels SearchChannels
	peersCatalog   PeersCatalog // FIXME: maybe should be thread-safe

	// Paxos
	maxID         uint
	TagIsDoneChan chan string

	currentPaxos             Paxos
	cpt                      uint
	currentPaxox_mutex       sync.RWMutex
	tlc_change               chan uint
	eventAcceptedChan        chan types.PaxosAcceptMessage
	logicalClock             uint
	tagging_mutex            sync.RWMutex
	TLCSent_mutex            sync.RWMutex
	tagging                  bool
	TLCSent                  map[uint]bool
	maxID_mutex              sync.RWMutex
	logicalClock_mutex       sync.RWMutex
	tlcacc_mutex             sync.RWMutex
	step_to_last_value_mutex sync.RWMutex
	step_to_last_value       map[uint]types.BlockchainBlock
	tlcAccumulator           map[uint]int
}

// Broadcasts HeartbeatMessage at regular interval
func (n *node) StartHeartbeat() {
	if n.conf.HeartbeatInterval == 0 {
		return
	}

	heartbeatMsg, err := n.conf.MessageRegistry.MarshalMessage(types.EmptyMessage{})
	if err != nil {
		log.Error().Msgf("<[peer.Peer.StartHeartbeat] Marshal error >: <%s>", err.Error())
		return
	}

	ticker := time.NewTicker(n.conf.HeartbeatInterval)
	for {
		select {
		case <-n.stop:
			ticker.Stop()
			return
		case <-ticker.C:
			err = n.Broadcast(heartbeatMsg)
			if err != nil {
				log.Error().Msgf("<[peer.Peer.StartHeartbeat] Broadcast >: <%s>", err.Error())
			}
		}
	}

}

// sends StatusMessage to one random neighbour at regular interval
func (n *node) StartAntiEntropy() {
	if n.conf.AntiEntropyInterval == 0 {
		return
	}

	ticker := time.NewTicker(n.conf.AntiEntropyInterval)
	for {
		select {
		case <-n.stop:
			ticker.Stop()
			return
		case <-ticker.C:
			statusMsg := types.StatusMessage(n.rumorHistory.GetView())
			dest := n.peers.GetRandomPeer(NewSet(n.conf.Socket.GetAddress()))
			if dest == "" {
				continue
			}

			err := n.DirectSend(dest, statusMsg)
			if err != nil {
				log.Error().Msgf("<[peer.Peer.Start] Send to random neighbour error>: <%s>", err.Error())
			}
		}
	}
}

// Start implements peer.Service
func (n *node) Start() error {
	n.running = true

	if n.conf.HeartbeatInterval != 0 { // Heartbeat
		heartbeatMsg, err := n.conf.MessageRegistry.MarshalMessage(types.EmptyMessage{})
		if err != nil {
			log.Error().Msgf("<[peer.Peer.Start] Heartbeat Marshal error >: <%s>", err.Error())
		} else {
			err = n.Broadcast(heartbeatMsg)
			if err != nil {
				log.Error().Msgf("<[peer.Peer.Start] Heartbeat Broadcast error >: <%s>", err.Error())
			}
		}

		go n.StartHeartbeat()
	}

	if n.conf.AntiEntropyInterval != 0 {
		go n.StartAntiEntropy()
	}

	go func() { // recv loop
		for {
			select {
			case <-n.stop:
				return
			default:
				pkt, err := n.conf.Socket.Recv(n.socketTimeout)
				if errors.Is(err, transport.TimeoutErr(0)) {
					continue
				}
				//fmt.Println(n.conf.Socket.GetAddress(), "received", pkt.Msg.Type)

				go func() { // process packet
					dest := pkt.Header.Destination

					if dest == n.conf.Socket.GetAddress() { // for this node
						err := n.conf.MessageRegistry.ProcessPacket(pkt)
						if err != nil {
							log.Error().Msgf("<[peer.Peer.Start] ProcessPacket error>: <%s>", err.Error())
						}
					} else { // relay
						pkt.Header.RelayedBy = n.conf.Socket.GetAddress()
						pkt.Header.TTL--

						relayTo := n.router.Get(dest)
						if relayTo == "" {
							log.Error().Msg("<[peer.Peer.Start] Relay error>: <destination not found in routing table>")
							return
						}

						err := n.conf.Socket.Send(relayTo, pkt, n.socketTimeout)
						if err != nil {
							log.Error().Msgf("<[peer.Peer.Start] Relay error>: <%s>", err.Error())
						}
					}
				}()
			}
		}
	}()
	return nil
}

// Stop implements peer.Service
func (n *node) Stop() error {
	if n.running {
		n.stop <- true
	}
	n.running = false
	return nil
}

// Marshals and sends given message directly to dest using Socket.Send
// (doesn't check routing table)
func (n *node) DirectSend(dest string, msg types.Message) error {
	transportMsg, err := n.conf.MessageRegistry.MarshalMessage(msg)
	if err != nil {
		return err
	}
	header := transport.NewHeader(n.conf.Socket.GetAddress(), n.conf.Socket.GetAddress(), dest, 0)
	pkt := transport.Packet{Header: &header, Msg: &transportMsg}
	return n.conf.Socket.Send(dest, pkt, n.socketTimeout)
}

// Unicast implements peer.Messaging
func (n *node) Unicast(dest string, msg transport.Message) error {
	header := transport.NewHeader(n.conf.Socket.GetAddress(), n.conf.Socket.GetAddress(), dest, 0)
	pkt := transport.Packet{Header: &header, Msg: &msg}

	relayTo := n.router.Get(dest)
	if relayTo == "" {
		return errors.New("[Unicast] peer not found")
	}
	return n.conf.Socket.Send(relayTo, pkt, n.socketTimeout)
}

// sends rumor to given dest
// returns pktID of the packet sent through the socket(used for ACK)
func (n *node) SendRumor(dest string, rumor types.Rumor) (string, error) {
	rumorsMsg := types.RumorsMessage{Rumors: []types.Rumor{rumor}}
	transportRumorsMsg, err := n.conf.MessageRegistry.MarshalMessage(rumorsMsg)
	if err != nil {
		return "", err
	}

	header := transport.NewHeader(n.conf.Socket.GetAddress(), n.conf.Socket.GetAddress(),
		dest, 0)
	pkt := transport.Packet{Header: &header, Msg: &transportRumorsMsg}

	err = n.conf.Socket.Send(dest, pkt, n.socketTimeout)
	if err != nil {
		return "", err
	}

	return pkt.Header.PacketID, nil
}

func (n *node) Broadcast(msg transport.Message) error {
	rumor := n.rumorHistory.AddNewRumor(msg, n.conf.Socket.GetAddress())

	go func() { // process rumor
		header := transport.NewHeader(n.conf.Socket.GetAddress(), n.conf.Socket.GetAddress(),
			n.conf.Socket.GetAddress(), 0)
		pkt := transport.Packet{Header: &header, Msg: &msg}
		err := n.conf.MessageRegistry.ProcessPacket(pkt)
		if err != nil {
			log.Error().Msgf("<[peer.Peer.Broadcast] Process rumor >: <%s> ", err)
		}
	}()

	dest := n.peers.GetRandomPeer(NewSet(n.conf.Socket.GetAddress()))
	if dest == "" {
		log.Info().Msgf("[peer.peer.Broadcast] No random peers to send to")
		return nil
	}

	pktID, err := n.SendRumor(dest, rumor)
	if err != nil {
		return err
	}

	go n.WaitForAck(pktID, rumor, NewSet(n.conf.Socket.GetAddress(), dest))

	return nil
}

// Waits for Ack of pktID. If timeout is reached,
// sends rumor to one random peer outside the ignorePeers set
func (n *node) WaitForAck(pktID string, rumor types.Rumor, ignorePeers *Set) {
	channel := n.ackChannels.Set(pktID, make(chan bool, 1))
	defer close(channel)
	defer n.ackChannels.Delete(pktID)

	if n.conf.AckTimeout == 0 {
		<-channel // wait forever
	} else {
		timer := time.NewTimer(n.conf.AckTimeout)
		defer timer.Stop()

		select {
		case <-channel: // Ack received!
			return
		case <-timer.C:
			newDest := n.peers.GetRandomPeer(ignorePeers)
			if newDest == "" {
				log.Info().Msgf("[peer.peer.Broadcast][Ack] No random peers to send to")
				return
			}

			newPktID, err := n.SendRumor(newDest, rumor)
			if err != nil {
				log.Error().Msgf("<[peer.Peer.Broadcast][Ack] Send to random neighbour error>: %s <%s>",
					newDest, err.Error())
				return
			}

			n.WaitForAck(newPktID, rumor, ignorePeers.Add(newDest))
		}
	}
}

// AddPeer implements peer.Service
func (n *node) AddPeer(addr ...string) {
	for _, s := range addr {
		n.router.Set(s, s)
		n.peers.Add(s)
	}
}

// GetRoutingTable implements peer.Service
func (n *node) GetRoutingTable() peer.RoutingTable {
	copyTable := make(peer.RoutingTable)

	n.router.Lock()
	for k, v := range n.router.table {
		copyTable[k] = v
	}
	n.router.Unlock()

	return copyTable
}

// SetRoutingEntry implements peer.Service
func (n *node) SetRoutingEntry(origin, relayAddr string) {
	if relayAddr == "" {
		n.router.Delete(origin)
	} else {
		n.router.Set(origin, relayAddr)
	}
}

func (n *node) Upload(data io.Reader) (metahash string, err error) {
	chunk := make([]byte, n.conf.ChunkSize)
	var metafile []byte
	var metafileKey []byte
	h := crypto.SHA256.New()

	for {
		num_bytes, err := data.Read(chunk)
		if err == io.EOF {
			break
		}

		_, err = h.Write(chunk[:num_bytes])
		if err != nil {
			return "", err
		}

		chunkHash := h.Sum(nil)
		chunkKey := hex.EncodeToString(chunkHash)

		slice_copy := make([]byte, num_bytes)
		copy(slice_copy, chunk[:num_bytes])

		n.conf.Storage.GetDataBlobStore().Set(chunkKey, slice_copy)

		metafileKey = append(metafileKey, chunkHash...)

		// append to metafile
		if len(metafile) == 0 {
			metafile = append(metafile, chunkKey...)
		} else {
			metafile = append(metafile, []byte(peer.MetafileSep)...)
			metafile = append(metafile, chunkKey...)
		}

		h.Reset()
	}

	_, err = h.Write(metafileKey)
	if err != nil {
		return "", err
	}
	metahash = hex.EncodeToString(h.Sum(nil))
	n.conf.Storage.GetDataBlobStore().Set(metahash, metafile)

	return metahash, nil
}

func (n *node) GetCatalog() peer.Catalog {
	n.peersCatalog.Lock()
	defer n.peersCatalog.Unlock()
	copy := make(peer.Catalog)

	for chunkKey, set := range n.peersCatalog.catalog {
		copy[chunkKey] = make(map[string]struct{})
		for peer := range set {
			copy[chunkKey][peer] = struct{}{}
		}
	}

	return copy
}

func (n *node) UpdateCatalog(key string, peer string) {
	n.peersCatalog.Lock()
	defer n.peersCatalog.Unlock()

	if n.peersCatalog.catalog[key] == nil {
		n.peersCatalog.catalog[key] = make(map[string]struct{})
	}
	n.peersCatalog.catalog[key][peer] = struct{}{}
}

// Waits for reply whose ID is associated with given DataRequestMessage.
// Uses back-off strategy if peer is unresponsive.
func (n *node) WaitForReply(dataReqMsg types.DataRequestMessage, dest string) (*types.DataReplyMessage, error) {
	channel := n.dataChannels.Set(dataReqMsg.RequestID, make(chan *types.DataReplyMessage, 1))
	defer close(channel)
	defer n.ackChannels.Delete(dataReqMsg.RequestID)

	transportDataReqMsg, err := n.conf.MessageRegistry.MarshalMessage(dataReqMsg)
	if err != nil {
		return nil, err
	}

	var r uint = 0
	var f uint = 1

	for r < n.conf.BackoffDataRequest.Retry {
		timer := time.NewTimer(n.conf.BackoffDataRequest.Initial * time.Duration(f))

		select {
		case reply := <-channel:
			timer.Stop()
			return reply, nil
		case <-timer.C:
			// retransmit
			err = n.Unicast(dest, transportDataReqMsg)
			if err != nil {
				return nil, err
			}
		}
		timer.Stop()
		r++
		f *= n.conf.BackoffDataRequest.Factor
	}

	return nil, fmt.Errorf("[peer.WaitForReply] backoff timeout: can't reach peer %s", dest)
}

// Fetches value associated with given key from a random peer known to have it.
// Uses back-off strategy if peer is unresponsive.
func (n *node) FetchFromPeers(key string) ([]byte, error) {
	dest := n.peersCatalog.GetRandomPeer(key)
	if dest == "" {
		return nil, fmt.Errorf("[peer.FetchFromPeers] no known peers hold key %s", key)
	}

	// Create DataRequestMessage
	dataReqMsg := types.DataRequestMessage{RequestID: xid.New().String(), Key: key}
	transportDataReqMsg, err := n.conf.MessageRegistry.MarshalMessage(dataReqMsg)
	if err != nil {
		return nil, err
	}

	// Send DataRequestMessage to random peer from Catalog
	err = n.Unicast(dest, transportDataReqMsg)
	if err != nil {
		return nil, err
	}

	reply, err := n.WaitForReply(dataReqMsg, dest)
	if err != nil {
		return nil, err
	}

	if len(reply.Value) == 0 {
		return nil, fmt.Errorf("[peer.FetchFromPeers] remote peer returned empty value")
	}

	if reply.Key != key {
		return nil, fmt.Errorf(`[peer.FetchFromPeers] key mishmatch:
									received reply with key %s, expeceted key: %s`, reply.Key, key)
	}

	return reply.Value, nil
}

// Fetches resource identified by given key, either from local store or from peers.
// Updates local DataBlobStore in case the resource is fetched from peers.
func (n *node) FetchResource(key string) ([]byte, error) {
	// check locally
	resource := n.conf.Storage.GetDataBlobStore().Get(key)

	if resource == nil { // fetch from peers
		fetchedResource, err := n.FetchFromPeers(key)
		if err != nil {
			return nil, err
		}
		n.conf.Storage.GetDataBlobStore().Set(key, fetchedResource)
		resource = fetchedResource
	}

	return resource, nil
}

func (n *node) Download(metahash string) ([]byte, error) {
	metafile, err := n.FetchResource(metahash)
	if err != nil {
		return nil, err
	}

	chunkKeys := strings.Split(string(metafile), peer.MetafileSep)

	var file []byte

	for _, chunkKey := range chunkKeys {
		chunk, err := n.FetchResource(chunkKey)
		if err != nil {
			return nil, err
		}

		file = append(file, chunk...)
	}

	return file, nil
}

func (n *node) Tag(name string, mh string) error {
	if n.conf.Storage.GetNamingStore().Get(name) != nil {
		return xerrors.Errorf("name already taken")
	}
	if n.conf.TotalPeers <= 1 {
		n.conf.Storage.GetNamingStore().Set(name, []byte(mh))
		return nil
	}
	println(n.conf.Socket.GetAddress(), "start Taging Process")
	id := n.conf.PaxosID
	println("here")
	p := n.getPaxos()
	n.resetPhase(p)
	msg := n.getPrepMsg(id)
	trans := n.transPrep(msg)
	/*header := transport.NewHeader(n.GetAddress(), n.GetAddress(), n.GetAddress(), 0)
	pck := transport.Packet{
		Header: &header,
		Msg:    &trans,
	}*/
	go n.Broadcast(trans)
	//n.HandlePkt(pck)
	n.waitForPromises(p, id, name, mh, time.Now())
	n.SetIsTagging(true) //taging->True
	println("tagging =", n.getIsTagging())
	<-n.TagIsDoneChan
	n.SetIsTagging(false)
	return nil
}

func (n *node) Resolve(name string) string {
	return string(n.conf.Storage.GetNamingStore().Get(name))
}

func (n *node) SearchAll(reg regexp.Regexp, budget uint, timeout time.Duration) ([]string, error) {
	var peers []string

	if n.peers.Len() > int(budget) {
		peers = n.peers.GetNRandomPeers(int(budget), NewSet())
	} else {
		peers = n.peers.GetAllPeers(NewSet())
	}

	var wg sync.WaitGroup

	leftPeers := len(peers)
	leftBudget := budget

	for _, peer := range peers {
		peerBudget := leftBudget / uint(leftPeers)
		if peerBudget == 0 {
			continue
		}

		req := types.SearchRequestMessage{
			RequestID: xid.New().String(),
			Origin:    n.conf.Socket.GetAddress(),
			Pattern:   reg.String(),
			Budget:    peerBudget}

		wg.Add(1)
		go func(peer string, req types.SearchRequestMessage) {
			defer wg.Done()

			err := n.DirectSend(peer, req)
			if err != nil {
				log.Error().Msgf("[peer.Peer.SearchAll] Send to peer error>: <%s>", err.Error())
			}

			timer := time.NewTimer(timeout)
			<-timer.C // wait full timeout
			timer.Stop()
		}(peer, req)

		leftPeers--
		leftBudget -= peerBudget
	}

	wg.Wait()

	var matchingFilenames []string

	n.conf.Storage.GetNamingStore().ForEach(func(key string, val []byte) bool {
		if reg.Match([]byte(key)) {
			matchingFilenames = append(matchingFilenames, key)
		}
		return true
	})

	return matchingFilenames, nil
}

func (n *node) SearchFirst(pattern regexp.Regexp, conf peer.ExpandingRing) (string, error) {
	name := ""

	n.conf.Storage.GetNamingStore().ForEach(func(key string, val []byte) bool {
		if pattern.Match([]byte(key)) {
			metafile := n.conf.Storage.GetDataBlobStore().Get(string(val))

			if metafile != nil {
				chunkKeys := strings.Split(string(metafile), peer.MetafileSep)

				for _, chunkKey := range chunkKeys {
					chunk := n.conf.Storage.GetDataBlobStore().Get(chunkKey)

					if chunk == nil {
						return true // missing chunk
					}
				}
				// found file with all chunks
				name = key
				return false // stop iteration
			}
		}
		return true
	})

	if name != "" { // found localy
		return name, nil
	}

	budget := conf.Initial

	for i := 0; i < int(conf.Retry); i++ {
		var peers []string

		if n.peers.Len() > int(budget) {
			peers = n.peers.GetNRandomPeers(int(budget), NewSet())
		} else {
			peers = n.peers.GetAllPeers(NewSet())
		}

		var wg sync.WaitGroup
		fullMatch := make(chan string)

		leftPeers := len(peers)
		leftBudget := budget

		for _, peer := range peers {
			peerBudget := leftBudget / uint(leftPeers)
			if peerBudget == 0 {
				continue
			}

			req := types.SearchRequestMessage{
				RequestID: xid.New().String(),
				Origin:    n.conf.Socket.GetAddress(),
				Pattern:   pattern.String(),
				Budget:    peerBudget}

			wg.Add(1)
			go func(peer string, req types.SearchRequestMessage) {
				defer wg.Done()

				err := n.DirectSend(peer, req)
				if err != nil {
					log.Error().Msgf("[SearchFirst] Send to peer error>: <%s>", err.Error())
				}

				channel := n.searchChannels.Set(req.RequestID, make(chan string, 1))
				defer n.ackChannels.Delete(req.RequestID)
				defer close(channel)

				timer := time.NewTimer(conf.Timeout)

				select {
				case <-timer.C:
				case fullMatchName := <-channel:
					fullMatch <- fullMatchName
				}

				timer.Stop()
			}(peer, req)

			leftPeers--
			leftBudget -= peerBudget
		}

		timeout := make(chan bool)
		go func() {
			wg.Wait()
			timeout <- true
		}()

		select {
		case name := <-fullMatch:
			return name, nil
		case <-timeout: // expand ring
		}

		budget *= conf.Factor
	}

	return name, nil
}

/* ==== SafeRoutingTable ==== */

// Thread-safe wrapper for the routing table
type SafeRoutingTable struct {
	sync.Mutex
	table peer.RoutingTable
}

func (r *SafeRoutingTable) Set(key, val string) {
	r.Lock()
	defer r.Unlock()

	r.table[key] = val
}

func (r *SafeRoutingTable) Delete(key string) {
	r.Lock()
	defer r.Unlock()

	delete(r.table, key)
}

// Returns empty string if key doesn't exist in the routing table
func (r *SafeRoutingTable) Get(key string) string {
	r.Lock()
	defer r.Unlock()

	return r.table[key]
}

/* ========== AckChannels ========== */

// Thread-safe map which maps pktID -> channel
// Used for asynchronous notification
// When we process an AckMessage we send a signal to the corresponding packets channel
type AckChannels struct {
	sync.Mutex
	channelsMap map[string]chan bool
}

func (r *AckChannels) Set(key string, val chan bool) chan bool {
	r.Lock()
	defer r.Unlock()

	r.channelsMap[key] = val
	return val
}

func (r *AckChannels) Get(key string) (chan bool, bool) {
	r.Lock()
	defer r.Unlock()

	val, ok := r.channelsMap[key]
	return val, ok
}

func (r *AckChannels) Delete(key string) {
	r.Lock()
	defer r.Unlock()

	delete(r.channelsMap, key)
}

/* ========== SearchChannels ========== */

// Thread-safe map which maps requestID -> channel
// Used for asynchronous notification of full matched filenames
// When we process an SearchReplyMessage we send a filename (only if its fully matched) to the corresponding channel
type SearchChannels struct {
	sync.Mutex
	channelsMap map[string]chan string
}

func (r *SearchChannels) Set(key string, val chan string) chan string {
	r.Lock()
	defer r.Unlock()

	r.channelsMap[key] = val
	return val
}

func (r *SearchChannels) Get(key string) (chan string, bool) {
	r.Lock()
	defer r.Unlock()

	val, ok := r.channelsMap[key]
	return val, ok
}

func (r *SearchChannels) Delete(key string) {
	r.Lock()
	defer r.Unlock()

	delete(r.channelsMap, key)
}

/* ========== DataChannels ========== */

// Thread-safe map which maps requestID -> channel
// Used for asynchronous notification
// When we process an DataReplyMessage we send a pointer to it to the corresponding channel
type DataChannels struct {
	sync.Mutex
	channelsMap map[string]chan *types.DataReplyMessage
}

func (r *DataChannels) Set(key string, val chan *types.DataReplyMessage) chan *types.DataReplyMessage {
	r.Lock()
	defer r.Unlock()

	r.channelsMap[key] = val
	return val
}

func (r *DataChannels) Get(key string) (chan *types.DataReplyMessage, bool) {
	r.Lock()
	defer r.Unlock()

	val, ok := r.channelsMap[key]
	return val, ok
}

func (r *DataChannels) Delete(key string) {
	r.Lock()
	defer r.Unlock()

	delete(r.channelsMap, key)
}

/* ======== Set ========= */

// Simple set implementation - not thread-safe
type Set struct {
	set map[string]struct{}
}

func NewSet(elems ...string) *Set {
	s := &Set{set: make(map[string]struct{})}
	for _, elem := range elems {
		s.Add(elem)
	}
	return s
}

func (s *Set) Add(elem string) *Set {
	s.set[elem] = struct{}{}
	return s
}

func (s *Set) Delete(elem string) {
	delete(s.set, elem)
}

func (s *Set) Contains(elem string) bool {
	_, ok := s.set[elem]
	return ok
}

func (s *Set) Len() int {
	return len(s.set)
}

/* ======== Peers ======== */

// Stores all known peers:
// thread-safe wrapper over Set
type Peers struct {
	sync.Mutex
	peersSet Set
}

func (p *Peers) Add(peer string) {
	p.Lock()
	defer p.Unlock()

	p.peersSet.Add(peer)
}

func (p *Peers) Delete(peer string) {
	p.Lock()
	defer p.Unlock()

	p.peersSet.Delete(peer)
}

func (p *Peers) Contains(peer string) bool {
	p.Lock()
	defer p.Unlock()

	return p.peersSet.Contains(peer)
}

func (p *Peers) Len() int {
	p.Lock()
	defer p.Unlock()
	return p.peersSet.Len()
}

// Returns random peer (empty string if there are none)
// ignorePeers: peers to be ignored
func (p *Peers) GetRandomPeer(ignorePeers *Set) string {
	peers := p.GetAllPeers(ignorePeers)

	if len(peers) == 0 {
		return ""
	}

	return peers[rand.Intn(len(peers))]
}

func (p *Peers) GetAllPeers(ignorePeers *Set) []string {
	p.Lock()
	defer p.Unlock()

	peers := make([]string, 0)

	for key := range p.peersSet.set {
		if !ignorePeers.Contains(key) {
			peers = append(peers, key)
		}
	}

	return peers
}

// Return n random peers, if len(known peers) < n ~> returns all known peers
func (p *Peers) GetNRandomPeers(n int, ignorePeers *Set) []string {
	peers := p.GetAllPeers(ignorePeers)
	if len(peers) < n {
		return peers
	}

	nPeers := make([]string, 0)
	len := len(peers)

	for i := 0; i < n; i++ {
		randIndex := rand.Intn(len)
		nPeers = append(nPeers, peers[randIndex])
		peers[randIndex], peers[len-1] = peers[len-1], peers[randIndex]
		len--
	}

	return nPeers
}

/* ======== RumorHistory ======== */
type RumorHistory struct {
	sync.Mutex
	rumorMap map[string][]types.Rumor
}

func (r *RumorHistory) AddRumor(rumor types.Rumor) bool {
	r.Lock()
	defer r.Unlock()

	expected := uint(len(r.rumorMap[rumor.Origin])) + 1
	if rumor.Sequence != expected {
		return false
	}

	r.rumorMap[rumor.Origin] = append(r.rumorMap[rumor.Origin], rumor)
	return true
}

func (r *RumorHistory) GetRumor(origin string, sequence uint) (types.Rumor, error) {
	r.Lock()
	defer r.Unlock()

	rumors := r.rumorMap[origin]
	if uint(len(rumors)) > sequence {
		return types.Rumor{}, fmt.Errorf("no rumor with sequence %d found for peer %s",
			sequence, origin)
	}
	return rumors[sequence-1], nil
}

// Returns all received rumors from origin with sequence numbers >= startSeq
func (r *RumorHistory) GetRumorsRange(origin string, startSeq uint) ([]types.Rumor, error) {
	r.Lock()
	defer r.Unlock()

	if startSeq < 1 {
		return make([]types.Rumor, 0), fmt.Errorf("invalid startSeq: %d", startSeq)
	}

	rumors := r.rumorMap[origin]

	return rumors[startSeq-1:], nil
}

func (r *RumorHistory) GetLastSeq(origin string) uint {
	r.Lock()
	defer r.Unlock()

	rumors := r.rumorMap[origin]
	if len(rumors) == 0 {
		return 0
	}
	return rumors[len(rumors)-1].Sequence
}

// Creates rumor from given msg and adds it to history before returning it
func (r *RumorHistory) AddNewRumor(msg transport.Message, origin string) types.Rumor {
	r.Lock()
	defer r.Unlock()

	expected := uint(len(r.rumorMap[origin])) + 1
	rumor := types.Rumor{
		Origin:   origin,
		Sequence: expected,
		Msg:      &msg}

	r.rumorMap[origin] = append(r.rumorMap[origin], rumor)

	return rumor
}

// Returns map: origin -> sequence number of the last rumor received by this origin
func (r *RumorHistory) GetView() map[string]uint {
	r.Lock()
	defer r.Unlock()
	view := make(map[string]uint)

	for origin, rumors := range r.rumorMap {
		view[origin] = rumors[len(rumors)-1].Sequence
	}

	return view
	// FIXME: maybe keep view in struct instead of dynamically computing it
}

/* ======== PeersCatalog ======== */
type PeersCatalog struct {
	sync.Mutex
	catalog peer.Catalog
}

func (p *PeersCatalog) GetRandomPeer(key string) string {
	p.Lock()
	defer p.Unlock()
	peers := p.catalog[key]

	if len(peers) == 0 {
		return ""
	}

	randomIndex := rand.Intn(len(peers))
	i := 0

	for k := range peers {
		if i == randomIndex {
			return k
		}
		i++
	}
	return ""
}

// ChatMessageExec implements registry.Exec
func (n *node) ChatMessageExec(msg types.Message, pkt transport.Packet) error {
	log.Info().Msgf("[ChatMessageExec] Received packet: <%s>", pkt)
	return nil
}

// RumorsMessageExec implements registry.Exec
func (n *node) RumorsMessageExec(msg types.Message, pkt transport.Packet) error {
	rumors, ok := msg.(*types.RumorsMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	expected := false

	for _, rumor := range rumors.Rumors {
		if expected = n.rumorHistory.AddRumor(rumor); expected {

			if !n.peers.Contains(rumor.Origin) { //update routing table
				n.router.Set(rumor.Origin, pkt.Header.RelayedBy)
			}

			rumorPkt := transport.Packet{Header: pkt.Header, Msg: rumor.Msg}
			go func() { // process rumor
				err := n.conf.MessageRegistry.ProcessPacket(rumorPkt)
				if err != nil {
					log.Error().Msgf("<[impl.RumorsMessageExec] Process rumor error>: <%s>", err.Error())
				}
			}()

		} else {
			log.Info().Msg("unexpected Rumor sequence number ~> ignore Rumor")
		}
	}

	{ // send AckMessage to the source
		ack := types.AckMessage{
			AckedPacketID: pkt.Header.PacketID,
			Status:        types.StatusMessage(n.rumorHistory.GetView())}
		err := n.DirectSend(pkt.Header.Source, ack)
		if err != nil {
			log.Error().Msgf("<[impl.RumorsMessageExec] Send Ack error>: <%s>", err.Error())
		}
	}

	if expected { // send to random neighbour
		dest := n.peers.GetRandomPeer(NewSet(n.conf.Socket.GetAddress(), pkt.Header.Source))
		if dest == "" {
			return nil
		}

		err := n.DirectSend(dest, rumors)
		if err != nil {
			log.Error().Msgf("<[impl.RumorsMessageExec] Send to random neighbour error>: <%s>", err.Error())
		}
	}

	return nil
}

func (n *node) StatusMessageExec(msg types.Message, pkt transport.Packet) error {
	remoteView, ok := msg.(*types.StatusMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	localView := n.rumorHistory.GetView()
	newRemoteRumors := false
	newLocalRumors := false
	rumors := make([]types.Rumor, 0)
	cnt := 0 // how many local rumors are present in remoteView

	for origin, seq := range localView {
		if remoteSeq, exists := (*remoteView)[origin]; exists {
			cnt++

			if seq > remoteSeq { // I have new rumors
				newLocalRumors = true

				newRumors, err := n.rumorHistory.GetRumorsRange(origin, remoteSeq+1)
				if err != nil {
					log.Error().Msgf("<[impl.StatusMessageExec] GetRumorsRange error>: <%s>", err.Error())
					continue
				}
				rumors = append(rumors, newRumors...)
			} else if seq < remoteSeq { // remote has new rumors
				newRemoteRumors = true
			}
		} else { // I have new rumors (from an origin that remote didn't get any rumors from)
			newLocalRumors = true

			newRumors, err := n.rumorHistory.GetRumorsRange(origin, 1)
			if err != nil {
				log.Error().Msgf("<[impl.StatusMessageExec] GetRumorsRange error>: <%s>", err.Error())
				continue
			}
			rumors = append(rumors, newRumors...)
		}
	}

	if cnt < len(*remoteView) {
		newRemoteRumors = true
	}

	if newRemoteRumors { // send Status (1)
		statusMsg := types.StatusMessage(localView)
		err := n.DirectSend(pkt.Header.Source, statusMsg)
		if err != nil {
			log.Error().Msgf("<[impl.StatusMessageExec] Send status error>: <%s>", err.Error())
		}
	}

	if newLocalRumors { // send rumors, ignore Ack if it arrives (2)
		rumorsMsg := types.RumorsMessage{Rumors: rumors}
		err := n.DirectSend(pkt.Header.Source, rumorsMsg)
		if err != nil {
			log.Error().Msgf("<[impl.StatusMessageExec] Send rumors error>: <%s>", err.Error())
		}
	}

	if !newRemoteRumors && !newLocalRumors { // ContinueMongering (4)
		if rand.Float64() < n.conf.ContinueMongering {
			statusMsg := types.StatusMessage(localView)
			dest := n.peers.GetRandomPeer(NewSet(n.conf.Socket.GetAddress(), pkt.Header.Source))
			if dest == "" {
				return nil
			}

			err := n.DirectSend(dest, statusMsg)
			if err != nil {
				log.Error().Msgf("<[impl.StatusMessageExec] ContinueMongering error>: <%s>", err.Error())
			}
		}
	}

	return nil
}

func (n *node) AckMessageExec(msg types.Message, pkt transport.Packet) error {
	ack, ok := msg.(*types.AckMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	if channel, ok := n.ackChannels.Get(ack.AckedPacketID); ok {
		channel <- true
	}

	transportStatusMsg, err := n.conf.MessageRegistry.MarshalMessage(ack.Status)
	if err != nil {
		return err
	}
	statusPkt := transport.Packet{Header: pkt.Header, Msg: &transportStatusMsg}
	err = n.conf.MessageRegistry.ProcessPacket(statusPkt)
	if err != nil {
		return err
	}

	return nil
}

func (n *node) PrivateMessageExec(msg types.Message, pkt transport.Packet) error {
	privateMsg, ok := msg.(*types.PrivateMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	if _, ok := privateMsg.Recipients[n.conf.Socket.GetAddress()]; ok {
		embeddedPkt := transport.Packet{Header: pkt.Header, Msg: privateMsg.Msg}
		n.conf.MessageRegistry.ProcessPacket(embeddedPkt)
	}

	return nil
}

func (n *node) EmptyMessageExec(msg types.Message, pkt transport.Packet) error {
	return nil
}

func (n *node) DataReplyMessageExec(msg types.Message, pkt transport.Packet) error {
	reply, ok := msg.(*types.DataReplyMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	if channel, ok := n.dataChannels.Get(reply.RequestID); ok {
		channel <- reply
	}

	return nil
}

func (n *node) DataRequestMessageExec(msg types.Message, pkt transport.Packet) error {
	req, ok := msg.(*types.DataRequestMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	val := n.conf.Storage.GetDataBlobStore().Get(req.Key)
	reply := types.DataReplyMessage{RequestID: req.RequestID, Key: req.Key, Value: val}

	transportMsg, err := n.conf.MessageRegistry.MarshalMessage(reply)
	if err != nil {
		return err
	}
	return n.Unicast(pkt.Header.Source, transportMsg)
}

func (n *node) SearchReplyMessageExec(msg types.Message, pkt transport.Packet) error {
	reply, ok := msg.(*types.SearchReplyMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	noMissingChunks := true
	for _, fileInfo := range reply.Responses {
		n.conf.Storage.GetNamingStore().Set(fileInfo.Name, []byte(fileInfo.Metahash))
		n.UpdateCatalog(fileInfo.Metahash, pkt.Header.Source)
		for _, chunkKey := range fileInfo.Chunks {
			if chunkKey != nil {
				n.UpdateCatalog(string(chunkKey), pkt.Header.Source)
			} else {
				noMissingChunks = false
			}
		}

		if noMissingChunks {
			if channel, ok := n.searchChannels.Get(reply.RequestID); ok {
				channel <- fileInfo.Name // forward full match
			}
		}
	}

	return nil
}

// constructs types.FileInfo object
func (n *node) ConstructFileInfo(name, metahash string) (types.FileInfo, error) {
	metafile := n.conf.Storage.GetDataBlobStore().Get(string(metahash))
	if metafile == nil {
		return types.FileInfo{}, errors.New("[ConstructFileInfo] metafile not found in blobe store")
	}

	chunkKeys := strings.Split(string(metafile), peer.MetafileSep)
	var chunks [][]byte

	for _, chunkKey := range chunkKeys {
		if n.conf.Storage.GetDataBlobStore().Get(chunkKey) != nil {
			chunks = append(chunks, []byte(chunkKey))
		} else {
			chunks = append(chunks, nil)
		}
	}

	return types.FileInfo{Name: name, Metahash: metahash, Chunks: chunks}, nil
}

func (n *node) SearchRequestMessageExec(msg types.Message, pkt transport.Packet) error {
	req, ok := msg.(*types.SearchRequestMessage)
	if !ok {
		return fmt.Errorf("wrong type: %T", msg)
	}

	go func() { // forward request
		// decrease budget
		req.Budget--
		if req.Budget == 0 {
			return
		}

		// get random peers
		var peers []string
		if n.peers.Len() > int(req.Budget) {
			peers = n.peers.GetNRandomPeers(int(req.Budget), NewSet(pkt.Header.Source))
		} else {
			peers = n.peers.GetAllPeers(NewSet(pkt.Header.Source))
		}

		leftPeers := len(peers)
		leftBudget := req.Budget

		// divide budget and send to each peer
		for _, peer := range peers {
			peerBudget := leftBudget / uint(leftPeers)
			if peerBudget == 0 {
				continue
			}

			req.Budget = peerBudget
			err := n.DirectSend(peer, req)
			if err != nil {
				log.Error().Msgf("[SearchRequestMessageExec] Forward search request error>: <%s>", err.Error())
			}
		}
	}()

	// process localy
	var fileInfos []types.FileInfo
	reg := regexp.MustCompile(req.Pattern)

	// construct fileInfos from matching files
	n.conf.Storage.GetNamingStore().ForEach(func(key string, val []byte) bool {
		if reg.Match([]byte(key)) {
			fileInfo, err := n.ConstructFileInfo(key, string(val))
			if err == nil {
				fileInfos = append(fileInfos, fileInfo)
			}
		}
		return true
	})

	// send reply
	reply := types.SearchReplyMessage{RequestID: req.RequestID, Responses: fileInfos}
	transportReply, err := n.conf.MessageRegistry.MarshalMessage(reply)
	if err != nil {
		return err
	}
	header := transport.NewHeader(n.conf.Socket.GetAddress(), n.conf.Socket.GetAddress(), req.Origin, 0)
	replyPkt := transport.Packet{Header: &header, Msg: &transportReply}
	return n.conf.Socket.Send(pkt.Header.Source, replyPkt, n.socketTimeout)
}

/**
func (n *node) ExecTLCMessage(msg types.Message, pkt transport.Packet) error {
	tlc := msg.(*types.TLCMessage)

	if n.TLCMessagesSaved[tlc.Step] == nil {
		n.TLCMessagesSaved[tlc.Step] = make([]types.TLCMessage, 0)
	}
	n.TLCMessagesSaved[tlc.Step] = append(n.TLCMessagesSaved[tlc.Step], *tlc)

	if tlc.Step != n.currentStep {
		return nil
	}

	threshold := n.conf.PaxosThreshold(n.conf.TotalPeers)
	if len(n.TLCMessagesSaved[n.currentStep]) >= threshold {
		// checks if already broadcasted
		n.TLCThreshold(*tlc, n.TLCBroadcasted)
		n.TLCBroadcasted = true

		n.currentStep += 1

		// Catchup
		for range n.TLCMessagesSaved {
			if len(n.TLCMessagesSaved[n.currentStep]) >= threshold {
				fmt.Println(n.TLCMessagesSaved[n.currentStep][0])
				n.TLCThreshold(n.TLCMessagesSaved[n.currentStep][0], n.TLCBroadcasted)
				n.currentStep += 1
			} else {
				break
			}
		}
	}

	return nil
}
**/

func (n *node) ExecPaxosPrepareMessage(msg types.Message, pkt transport.Packet) error {
	println("in procpremmessg on ", n.conf.Socket.GetAddress())
	m := msg.(*types.PaxosPrepareMessage)
	if m.Step != n.getLogicalClock() {
		println("wrong LogClock in procPrepMsg")
		return nil
	}
	if m.ID <= n.getMaxID() {
		println("small id in procPrepMsg")
		return nil
	}

	p := n.getPaxos()
	n.setMaxID(m.ID)
	println("setting", m.ID, "as max ID")

	if !p.hasAccepted {
		println(n.conf.Socket.GetAddress(), "accepting ID=")
		p.acceptedID = m.ID
	}
	println("looking 4 log ")
	promiseMsg := p.getPromiseMsg(m.ID, m.Step)
	println("got promessmsg")
	transmsg := n.transPromiseMsg(&promiseMsg)
	//in a PrivMsg
	dest := m.Source
	recipients := make(map[string]struct{}, 1)
	recipients[dest] = struct{}{}
	privMsg := types.PrivateMessage{
		Recipients: recipients,
		Msg:        &transmsg}
	//that we need to broadcast
	transPrivMsg := n.transPrivMsg(&privMsg)
	//println("sending")
	//go n.waitForAccepts(p, m.ID, time.Now(), make(map[string]uint))
	println(n.conf.Socket.GetAddress(), "is sending Promises")
	println(privMsg.Msg.Type, n.getPaxos().acceptedID, n.getPaxos().acceptedValue)
	go n.Broadcast(transPrivMsg)
	println("sent")
	return nil
}

func (n *node) ExecPaxosProposeMessage(msg types.Message, pkt transport.Packet) error {
	//println(n.GetAddress(), "in propose")
	m := msg.(*types.PaxosProposeMessage)
	if m.Step != n.getLogicalClock() { //TODO perhaps lock access?
		println("wrong LogClock in procPrepMsg")
		return nil
	}
	if m.ID != n.getMaxID() {
		println("wrong id in procPrepMsg")
		return nil
	}
	p := n.getPaxos()
	p.hasAccepted = true
	p.acceptedValue = &m.Value
	//unlock
	//println(n.GetAddress(), "accepting", p.acceptedID)
	acptM := p.getAcceptMsg(m.Step, m.ID, &m.Value)
	tracpt := n.transAcpt(&acptM)
	//go n.waitForAccepts(p, acptM.ID, time.Now(), make(map[string]uint)) //probably not but hey
	println("broadcasting Accept from", n.conf.Socket.GetAddress())
	n.Broadcast(tracpt) //wait resp here :
	println("done")
	return nil
}

//- as proposer

func (n *node) ExecPaxosPromiseMessage(msg types.Message, pkt transport.Packet) error {
	m := msg.(*types.PaxosPromiseMessage)
	if m.Step != n.getLogicalClock() {
		println("wrong LogClock in procPrepMsg")
		return nil
	}
	if n.getPaxos().getPhase() != 1 {
		println("wrong phase when receiving promise msg")
		return nil
	}
	n.getPaxos().incPromises()
	println("got a ...Promise")
	n.getPaxos().PromisesChannel <- *m
	println("logged Promise")
	return nil
}

func (n *node) waitForPromises(p *Paxos, id uint, name string, mh string, initTime time.Time) {
	for {
		if n.conf.PaxosProposerRetry-time.Since(initTime) <= 0 {
			println("TIMEOUT IN wait4Promise")
			n.cpt++
			n.retryPhase1(n.cpt*n.conf.PaxosID, name, mh)
			return
		}
		if p != n.getPaxos() {
			return
		}
		select {
		case promise := <-p.PromisesChannel:
			if promise.AcceptedValue != nil {
				p.otherAccepts = append(p.otherAccepts, promise)
			}
			if p.getPromises() >= uint(n.conf.PaxosThreshold(n.conf.TotalPeers)) {
				println("thresold reached in promises")
				p.incPhase()
				//go n.waitForAccepts(p, id, time.Now(), make(map[string]uint))
				n.Propose(id, name, mh)
				return
			}
		case <-time.After(time.Millisecond * 5):
			continue
		}
	}
}

func (n *node) retryPhase1(id uint, name string, mh string) {
	if n.getIsTagging() {
		n.currentPaxox_mutex.Lock()
		n.currentPaxos = n.newPaxos()
		n.currentPaxox_mutex.Unlock()
	}

	n.resetPhase(n.getPaxos())
	msg := n.getPrepMsg(id)
	trans := n.transPrep(msg)
	n.Broadcast(trans)
	println("after broadcast")
	//n.HandlePkt(pck)
	n.waitForPromises(n.getPaxos(), id, name, mh, time.Now())
}

func (n *node) Propose(id uint, name string, mh string) {
	println("in phase2")
	g_id, msg := n.getPaxos().getProposeMsg(id, name, mh)
	id_Acpt := uint(0)
	var value *types.PaxosValue
	value = nil
	for _, val := range n.getPaxos().otherAccepts {
		if val.AcceptedID >= uint(id_Acpt) {
			value = val.AcceptedValue
			id_Acpt = val.AcceptedID
		}
	}
	if value != nil { //if someone already accepted ->change val in propose
		msg.Value = types.PaxosValue{UniqID: g_id, Filename: value.Filename, Metahash: value.Metahash}
	}
	println("ready to accpt")
	trsp := n.transPropose(msg)
	n.Broadcast(trsp)
	println("sent Broadcast")
	initTime := time.Now()
	for {
		select {
		case s := <-n.tlc_change:
			if s == msg.Step {
				return
			}
		case <-time.After(n.conf.PaxosProposerRetry - time.Since(initTime)):
			println("TIMEOUT waiting 4 accepts&TLC")
			n.retryPhase1(msg.ID+n.conf.PaxosID, name, mh)
			return
		}
	}
}

func (n *node) ExecPaxosAcceptMessage(msg types.Message, pkt transport.Packet) error {
	println("receving accept, phase=", n.getPaxos().getPhase(), "ip=", n.conf.Socket.GetAddress())
	m := msg.(*types.PaxosAcceptMessage)
	if m.Step != n.getLogicalClock() {
		println("wrong Logclock in procPrepMsg")
		return nil
	}
	p := n.getPaxos()
	p.incAccept()
	n.eventAcceptedChan <- *m
	println("accept from", pkt.Header.Source, "logged on", n.conf.Socket.GetAddress())
	return nil
}

func (n *node) waitForAccepts() {
	map_ids := make(map[string]uint)
	for {
		var m types.PaxosAcceptMessage
		select {
		case k := <-n.eventAcceptedChan:
			m = k
			//break
		case <-time.After(time.Millisecond * 5):
			continue
		}
		println("counting +1 for group=", m.Value.UniqID, "on", n.conf.Socket.GetAddress())
		map_ids[m.Value.UniqID] = map_ids[m.Value.UniqID] + 1
		if map_ids[m.Value.UniqID] >= uint(n.conf.PaxosThreshold(n.conf.TotalPeers)) {
			println("threshold reached in accepts detected on", n.conf.Socket.GetAddress())
			msg := n.getTLCMsg(m.Step, m.ID, &m.Value)
			transmsg := n.transTLCMsg(&msg)
			n.setTLCsent(m.Step, true)
			n.Broadcast(transmsg)
			println("after send of TLC on", n.conf.Socket.GetAddress())
		}
	}
}

func (n *node) addBlock(b types.BlockchainBlock) {
	raw, err := b.Marshal()
	if err != nil {
		println("couln't mashall block")
		return
	}
	n.conf.Storage.GetBlockchainStore().Set(storage.LastBlockKey, b.Hash)
	n.conf.Storage.GetBlockchainStore().Set(hex.EncodeToString(b.Hash), raw)
}

//- also in acepter

func (n *node) ExecTLCMessage(msg types.Message, pkt transport.Packet) error {
	m := msg.(*types.TLCMessage)
	println("begin: ",
		"step=", m.Step,
		"nb=", n.GetTLCnb(n.getLogicalClock()),
		"threshold=", n.conf.PaxosThreshold(n.conf.TotalPeers),
		"by", n.conf.Socket.GetAddress())
	if m.Step < n.getLogicalClock() {
		return nil
	}
	n.SetTLC(m.Step, n.GetTLCnb(m.Step)+1) //packet saved in counter
	n.SetStepToVal(m.Step, m.Block)        // val saved

	l1 := n.getLogicalClock()
	println("b4 update: ",
		"step=", m.Step,
		"nb=", n.GetTLCnb(l1),
		"threshold=", n.conf.PaxosThreshold(n.conf.TotalPeers),
		"by", n.conf.Socket.GetAddress())
	if n.GetTLCnb(n.getLogicalClock()) >= n.conf.PaxosThreshold(n.conf.TotalPeers) {
		println("addingBLock& TLC++ 111", n.conf.Socket.GetAddress())
		block := n.GetStepValue(l1) //get stocked name/mh
		n.addBlock(block)
		n.conf.Storage.GetNamingStore().Set(block.Value.Filename, []byte(block.Value.Metahash)) //add to registery
		n.incLogicalClock()
		n.tlc_change <- l1 //Paxos accepted => TLC++
		tlcMsg := types.TLCMessage{
			Step:  l1,
			Block: block,
		}
		println("broacasting TCL from", n.conf.Socket.GetAddress())
		if !n.getTLCSent(l1) {
			n.Broadcast(n.transTLCMsg(&tlcMsg)) //if we send the
			n.setTLCsent(l1, true)
		}
		println("end broadcast")
		if n.getIsTagging() { //If we were proposing, we're done
			println("ToDoneChan", block.Value.Filename)
			n.TagIsDoneChan <- block.Value.Filename
			close(n.TagIsDoneChan)
		}
		n.currentPaxox_mutex.Lock()
		n.currentPaxos = n.newPaxos()
		n.currentPaxox_mutex.Unlock()
		//catchup if we can:

		/*
			n.currentPaxox_mutex.Lock()
			n.currentPaxos = n.newPaxos()
			n.currentPaxox_mutex.Unlock()*/
	}
	for {
		println("in for")
		println("after li")
		nb := n.GetTLCnb(n.getLogicalClock())
		println("after nb")
		if nb >= n.conf.PaxosThreshold(n.conf.TotalPeers) {
			println(n.conf.Socket.GetAddress(), "is CatchingUp")
			block := n.GetStepValue(n.logicalClock)
			println("CATCHUP===> addingBLock& TLC++ on",
				n.conf.Socket.GetAddress(),
				block.Value.Filename,
				block.Value.Metahash,
			)
			n.addBlock(block)
			n.conf.Storage.GetNamingStore().Set(block.Value.Filename,
				[]byte(block.Value.Metahash))
			n.incLogicalClock()
			println("Clock++ on", n.conf.Socket.GetAddress())
			/*if n.getIsTagging() {
				n.tlc_change <- m.Step // ->needed only if proposing
			} //check if we leave that:*/

		} else {
			println("done with Catching Up")
			if n.getIsTagging() {
				close(n.TagIsDoneChan)
			}
			return nil
		}
	}
	return nil
}

type Paxos struct {
	instance_number   uint
	address           string
	MaxID             uint
	hasAccepted       bool
	acceptedValue     *types.PaxosValue
	acceptedID        uint
	phase             uint
	phase_mutex       sync.RWMutex
	promises          uint
	promises_mutex    sync.RWMutex
	PromisesChannel   chan types.PaxosPromiseMessage
	otherAccepts      []types.PaxosPromiseMessage
	eventAcceptedChan chan types.PaxosAcceptMessage
	accepts           uint
	accepts_mutex     sync.RWMutex
	tlcs              uint
	tlcs_mutex        sync.RWMutex
	eventTLCChan      chan types.TLCMessage
}

func (n *node) newPaxos() Paxos {
	println("HEY CHANGING PAXOSINSTANCE")
	n.currentPaxos.phase_mutex.Lock()
	defer n.currentPaxos.phase_mutex.Unlock()
	return Paxos{
		instance_number:   n.getLogicalClock(),
		address:           n.conf.Socket.GetAddress(),
		MaxID:             0,
		hasAccepted:       false,
		phase:             0,
		promises:          0,
		PromisesChannel:   make(chan types.PaxosPromiseMessage, 100),
		otherAccepts:      make([]types.PaxosPromiseMessage, 100),
		eventAcceptedChan: make(chan types.PaxosAcceptMessage),
		eventTLCChan:      make(chan types.TLCMessage),
		tlcs:              0,
		tlcs_mutex:        sync.RWMutex{},
	}
}

func (n *node) getPrepMsg(id uint) *types.PaxosPrepareMessage {
	msg := types.PaxosPrepareMessage{
		Step:   n.getLogicalClock(),
		ID:     id,
		Source: n.conf.Socket.GetAddress(),
	}
	return &msg
}

func (p *Paxos) getPromises() uint {
	p.promises_mutex.RLock()
	defer p.promises_mutex.RUnlock()
	return p.promises
}

func (p *Paxos) incPromises() {
	p.promises_mutex.Lock()
	defer p.promises_mutex.Unlock()
	p.promises += 1
}
func (p *Paxos) getTLSnb() uint {
	p.tlcs_mutex.RLock()
	defer p.tlcs_mutex.RUnlock()
	return p.tlcs
}

func (p *Paxos) incTLSnb() {
	p.tlcs_mutex.Lock()
	defer p.tlcs_mutex.Unlock()
	p.promises += 1
}

func (p *Paxos) getAccept() uint {
	p.accepts_mutex.RLock()
	defer p.accepts_mutex.RUnlock()
	return p.accepts
}

func (p *Paxos) incAccept() {
	p.accepts_mutex.Lock()
	defer p.accepts_mutex.Unlock()
	p.accepts += 1
}

func (p *Paxos) getPhase() uint {
	p.phase_mutex.RLock()
	defer p.phase_mutex.RUnlock()
	return p.phase
}
func (p *Paxos) incPhase() {
	p.phase_mutex.Lock()
	defer p.phase_mutex.Unlock()
	println("goingPhase2")
	p.phase = 2
}
func (n *node) getIsTagging() bool {
	n.tagging_mutex.RLock()
	defer n.tagging_mutex.RUnlock()
	return n.tagging
}
func (n *node) SetIsTagging(val bool) {
	n.tagging_mutex.Lock()
	defer n.tagging_mutex.Unlock()
	n.tagging = val
}
func (n *node) getTLCSent(c uint) bool {
	n.TLCSent_mutex.RLock()
	defer n.TLCSent_mutex.RUnlock()
	return n.TLCSent[c]
}
func (n *node) setTLCsent(key uint, val bool) {
	n.TLCSent_mutex.Lock()
	defer n.TLCSent_mutex.Unlock()
	n.TLCSent[key] = val
}
func (n *node) resetPhase(p *Paxos) {
	p.phase_mutex.Lock()
	n.currentPaxox_mutex.Lock()
	defer n.currentPaxox_mutex.Unlock()
	defer p.phase_mutex.Unlock()
	n.currentPaxos.phase = 1
}

func (p *Paxos) getPromiseMsg(id uint, step uint) types.PaxosPromiseMessage {
	msg := types.PaxosPromiseMessage{
		Step: step,
		ID:   id,
	}
	if !p.hasAccepted {
		return msg
	}
	if p.acceptedID != 0 {
		msg.AcceptedID = p.acceptedID
	}
	msg.AcceptedValue = p.acceptedValue
	return msg
}

func (p *Paxos) getProposeMsg(id uint, filename string, metahash string) (string, *types.PaxosProposeMessage) {
	uid := xid.New().String()
	msg := types.PaxosProposeMessage{
		Step: p.instance_number,
		ID:   id,
		Value: types.PaxosValue{
			UniqID:   uid,
			Filename: filename,
			Metahash: metahash,
		},
	}
	return uid, &msg
}

func (p *Paxos) getAcceptMsg(step uint, id uint, value *types.PaxosValue) types.PaxosAcceptMessage {
	msg := types.PaxosAcceptMessage{
		Step:  step,
		ID:    id,
		Value: *value,
	}
	return msg
}

func (n *node) getTLCMsg(step uint, id uint, value *types.PaxosValue) types.TLCMessage {
	return types.TLCMessage{Step: step, Block: n.makeBlock(step, value)}
}

func (n *node) makeBlock(step uint, value *types.PaxosValue) types.BlockchainBlock {
	blockchainstore := n.conf.Storage.GetBlockchainStore()
	prevhash := blockchainstore.Get(storage.LastBlockKey)
	if prevhash == nil {
		prevhash = make([]byte, 32)
	}
	//buf := blockchainstore.Get(hex.EncodeToString(hash))
	//var block types.BlockchainBlock
	//err := block.Unmarshal(buf)
	/*if err != nil {
		println("error while unmarshalling block in blockchain", err.Error())
	}*/
	stuff := make([]byte, 0)
	stuff = append(stuff, []byte(strconv.Itoa(int(step)))...)
	stuff = append(stuff, []byte(value.UniqID)...)
	stuff = append(stuff, []byte(value.Filename)...)
	stuff = append(stuff, []byte(value.Metahash)...)
	stuff = append(stuff, prevhash...)
	retblock := types.BlockchainBlock{
		Index:    step,
		Hash:     get_hash(stuff),
		Value:    *value,
		PrevHash: prevhash,
	}
	return retblock
}

func (n *node) getMaxID() uint {
	n.maxID_mutex.RLock()
	defer n.maxID_mutex.RUnlock()
	return n.maxID
}

func (n *node) setMaxID(val uint) {
	n.maxID_mutex.Lock()
	defer n.maxID_mutex.Unlock()
	n.maxID = val
}
func (n *node) getLogicalClock() uint {
	n.logicalClock_mutex.RLock()
	defer n.logicalClock_mutex.RUnlock()
	return n.logicalClock
}

func (n *node) incLogicalClock() {
	n.logicalClock_mutex.Lock()
	defer n.logicalClock_mutex.Unlock()
	n.logicalClock += 1
}
func (n *node) setLogicalClock(val uint) {
	n.logicalClock_mutex.Lock()
	defer n.logicalClock_mutex.Unlock()
	if val < n.logicalClock {
		println("ERRORR TRying to decrease TLC...")
		return
	}
	n.logicalClock = val
}

func (n *node) resetMaxID(val uint) {
	n.setMaxID(0)
}

func (n *node) getPaxos() *Paxos {
	n.currentPaxox_mutex.RLock()
	defer n.currentPaxox_mutex.RUnlock()
	return &n.currentPaxos
}

/*
func (n *node) trans(m *types.Message) transport.Message {
	res, err := n.conf.MessageRegistry.MarshalMessage(*m)
	if err != nil {
		println("can't marshall msg", err)
	}
	return res
}*/

func (n *node) transPromiseMsg(m *types.PaxosPromiseMessage) transport.Message {
	res, err := n.conf.MessageRegistry.MarshalMessage(m)
	if err != nil {
		println("can't marshall msg", err)
	}
	return res
}
func (n *node) transTLCMsg(m *types.TLCMessage) transport.Message {
	res, err := n.conf.MessageRegistry.MarshalMessage(m)
	if err != nil {
		println("can't marshall msg", err)
	}
	return res
}

func (n *node) transPrivMsg(m *types.PrivateMessage) transport.Message {
	res, err := n.conf.MessageRegistry.MarshalMessage(m)
	if err != nil {
		println("can't marshall msg", err)
	}
	return res
}

func (n *node) transAcpt(m *types.PaxosAcceptMessage) transport.Message {
	res, err := n.conf.MessageRegistry.MarshalMessage(m)
	if err != nil {
		println("can't marshall msg", err)
	}
	return res
}

func (n *node) transPrep(m *types.PaxosPrepareMessage) transport.Message {
	res, err := n.conf.MessageRegistry.MarshalMessage(m)
	if err != nil {
		println("can't marshall msg", err)
	}
	return res
}

func (n *node) transPropose(m *types.PaxosProposeMessage) transport.Message {
	res, err := n.conf.MessageRegistry.MarshalMessage(m)
	if err != nil {
		println("can't marshall msg", err)
	}
	return res
}

func (n *node) SetTLC(step uint, nb int) {
	n.tlcacc_mutex.Lock()
	defer n.tlcacc_mutex.Unlock()
	n.tlcAccumulator[step] = nb
}

func (n *node) GetTLCnb(step uint) int {
	n.tlcacc_mutex.RLock()
	defer n.tlcacc_mutex.RUnlock()
	return n.tlcAccumulator[step]
}

func (n *node) SetStepToVal(step uint, val types.BlockchainBlock) {
	n.step_to_last_value_mutex.Lock()
	defer n.step_to_last_value_mutex.Unlock()
	n.step_to_last_value[step] = val
}

func (n *node) GetStepValue(step uint) types.BlockchainBlock {
	n.step_to_last_value_mutex.RLock()
	defer n.step_to_last_value_mutex.RUnlock()
	return n.step_to_last_value[step]
}

func get_hash(s []byte) []byte {
	h := crypto.SHA256.New()
	h.Write(s)
	metahashSlice := h.Sum(nil)
	//h.Reset()
	return metahashSlice
}

func (n *node) SendPrepDwnldResp(dest string, relays map[uint]string) error {
	//TODO send PrepareDownloadReply to dest &&
	//Todo: stats on how fast get data from url server (no more than upperbound bytes)

	var client = http.Client{
		Timeout: 2 * time.Second,
	}

	time := time.Now()
	// Ping the server
	// ping artepweb-vh.akamaihd.net
	url := "artepweb-vh.akamaihd.net"
	req, err := http.NewRequest("HEAD", url, nil)
	if err != nil {
		return err
	}
	resp, err := client.Do(req)
	if err != nil {
		return err
	}
	resp.Body.Close()
	fmt.Println(resp.StatusCode)
	fmt.Println(time)

	//either m3u8 homemade or:
	// mp4 or other using:
	//https://stackoverflow.com/questions/27844307/how-to-download-only-the-beginning-of-a-large-file-with-go-http-client-and-app
	//=>implying dynamical size of chunks, to add in route calculationsé & dwnld requests (& type) -> need to decide quickly

	return nil
}

func NewNode(conf peer.Configuration) *node {
	node := &node{conf: conf}

	return node
}

var peerFac peer.Factory = impl.NewPeer
func Test_sendPrepDwnldResp(t *testing.T) {
	transp := channel.NewTransport()

	conf := peer.Configuration{}
	node := NewNode(conf)

	node1 := z.NewTestNode(t, peerFac, transp, "127.0.0.1:0", z.WithChunkSize(3), z.WithAutostart(false))
	defer node1.Stop()

	node.SendPrepDwnldResp(node1.GetAddr(), nil)
}
