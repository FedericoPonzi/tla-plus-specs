https://github.com/ongardie/raft.tla/blob/master/raft.tla


---- MODULE raft ----
EXTENDS TLC
CONSTANTS Nodes, Quorum

baitinv == TRUE
\*baitinv ==  TLCGet("level") < 14
TypeOk == TRUE
FOLLOWER == "Follower"
LEADER == "Leader"
CANDIDATE == "Candidate"




(* --algorithm raft {

    define {
        
    }

process (node \in Nodes) 
variable 
    state = FOLLOWER,
    term = 0;  {
NODE:
    WHILE(TRUE){
        \* Timeout - Start a new round of leader election.
        either {
            await state \e {FOLLOWER};
            

        } or {
        \* Vote in a term 

        } or {

        }
        } or {
        \* notify the followers of committed message


        }

    }
}

process (client \in Client){

}


}*)


====