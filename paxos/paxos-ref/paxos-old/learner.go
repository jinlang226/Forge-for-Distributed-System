package paxos

import (
	"context"
	"log"
	"net"

	"google.golang.org/grpc"
	pb "paxos/message"
)

type Learner struct {
	pb.UnimplementedLearnerServer
}

func (l *Learner) Learn(ctx context.Context, args *pb.MsgArgs) (*pb.MsgReply, error) {

}

func (l *Learner) StartServer() {
	lis, err := net.Listen("tcp", ":50052")
	if err != nil {
		log.Fatalf("learner did not connect: %v", err)
	}
	s := grpc.NewServer()
	pb.RegisterLearnerServer(s, l)
	if err := s.Serve(lis); err != nil {
		log.Fatalf("could not RegisterLearnerServer: %v", err)
	}
}
