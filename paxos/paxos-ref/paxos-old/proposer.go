package paxos

import (
	"context"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"log"
	pb "paxos/message"
	"time"
)

type Proposer struct {
	id        int32 // server id
	round     int32 // current proposer known max round
	number    int32 // proposal number = (round, server id)
	acceptors []int // acceptor id list
}

func (p *Proposer) Propose(v int) int {
	p.round++
	p.number = p.proposalNumber()

	// Prepare Phase
	prepareCount := 0
	maxNumber := 0
	for _, aid := range p.acceptors {
		client, conn := p.connectToAcceptor(aid)
		defer conn.Close()

		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		args := &pb.MsgArgs{
			Number: int32(p.number),
			From:   int32(p.id),
			To:     int32(aid),
		}

		reply, err := client.Prepare(ctx, args)
		if err != nil {
			log.Printf("Prepare request failed: %v", err)
			continue
		}

		if reply.Ok {
			prepareCount++
			if int(reply.Number) > maxNumber {
				maxNumber = int(reply.Number)
				v = int(reply.Value)
			}
		}

		if prepareCount == p.majority() {
			break
		}
	}

	// Accept Phase
	acceptCount := 0
	if prepareCount >= p.majority() {
		for _, aid := range p.acceptors {
			client, conn := p.connectToAcceptor(aid)
			defer conn.Close()

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			args := &pb.MsgArgs{
				Number: int32(p.number),
				Value:  int32(v),
				From:   int32(p.id),
				To:     int32(aid),
			}

			reply, err := client.Accept(ctx, args)
			if err != nil {
				log.Printf("Accept requeset failaed: %v", err)
				continue
			}

			if reply.Ok {
				acceptCount++
			}
		}
	}

	if acceptCount >= p.majority() {
		return v
	}
	return -1
}

func (p *Proposer) majority() int {
	return len(p.acceptors)/2 + 1
}

// round, server id
func (p *Proposer) proposalNumber() int32 {
	return p.round<<32 | p.id
}

func (p *Proposer) connectToAcceptor(aid int) (pb.AcceptorClient, *grpc.ClientConn) {

	// Set up a connection to the server.
	conn, err := grpc.Dial("localhost:50051", grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		log.Fatalf("proposer did not connect: %v", err)
	}

	client := pb.NewAcceptorClient(conn)
	return client, conn
}
