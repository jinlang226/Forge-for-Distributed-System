package paxos

import (
	"context"
	"log"
	"net"
	"time"

	"google.golang.org/grpc"
	pb "paxos/message"
)

type Acceptor struct {
	pb.UnimplementedAcceptorServer
	lis            net.Listener
	id             int   //server id
	minProposal    int   //proposal id, 0 means no prepare message received
	acceptedNumber int   //accepted proposal id, 0 means no accepted proposal
	acceptedValue  int   //accepted value
	learners       []int //learner id list
}

func newAcceptor(id int, learners []int) *Acceptor {
	acceptor := &Acceptor{
		id:       id,
		learners: learners,
	}
	acceptor.startServer()
	return acceptor
}

func (a *Acceptor) Prepare(ctx context.Context, args *pb.MsgArgs) (*pb.MsgReply, error) {
	reply := &pb.MsgReply{}
	if args.Number > int32(a.minProposal) {
		a.minProposal = int(args.Number)
		reply.Number = int32(a.acceptedNumber)
		reply.Value = int32(a.acceptedValue) // Ensure type conversion is correct
		reply.Ok = true
	} else {
		reply.Ok = false
	}
	return reply, nil
}

func (a *Acceptor) Accept(ctx context.Context, args *pb.MsgArgs) (*pb.MsgReply, error) {
	reply := &pb.MsgReply{}
	if args.Number >= int32(a.minProposal) {
		a.minProposal = int(args.Number)
		a.acceptedNumber = int(args.Number)
		a.acceptedValue = int(args.Value)
		reply.Ok = true
		// Forward accepted proposals to learners in the background
		for _, lid := range a.learners {
			go a.forwardToLearner(lid, args)
		}
	} else {
		reply.Ok = false
	}
	return reply, nil
}

func (a *Acceptor) forwardToLearner(learnerID int, args *pb.MsgArgs) {
	client, conn := a.connectToLearner(learnerID)
	defer conn.Close()

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	_, err := client.Learn(ctx, args)
	if err != nil {
		log.Printf("Learn request failed: %v", err)
	}
}

func (p *Proposer) connectToLearner(aid int) (pb., *grpc.ClientConn) {


}


func (a *Acceptor) startServer() {
	lis, err := net.Listen("tcp", ":50051")
	if err != nil {
		log.Fatalf("acceptor did not connect: %v", err)
	}
	s := grpc.NewServer()
	pb.RegisterAcceptorServer(s, a)
	if err := s.Serve(lis); err != nil {
		log.Fatalf("could not RegisterAcceptorServer: %v", err)
	}
}

func (a *Acceptor) close() {
	a.lis.Close()
}
