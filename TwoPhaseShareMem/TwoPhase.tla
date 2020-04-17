------------------------------ MODULE TwoPhase ------------------------------

\* Playing around with: 
\* https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla


\* There is a set of resource managers; we can think of them as backups in the primary-backup
\* replication paradigm.
CONSTANT RM

VARIABLES
    rmState,    \* For each resource manager, we capture the state.
    tmState,    \* The state of the transactional manager. 
    tmPrepared, \* Capture the set of RMs that sent a $Prepare$.
    msgs


Message ==
    [type : {"Prepared"}, rm : RM ] \cup [ type : {"Commit", "Abort"} ]

    
\* Type invariant. For all variables in our spec, define their valid data types.
TypeInv ==
    \* RMs and the TM can pass through various states.    
    /\ rmState \in [ RM -> { "working", "prepared", "committed", "aborted"} ]
    /\ tmState \in {"init", "committed", "aborted"}
    /\ tmPrepared \subseteq RM
    /\ msgs \subseteq Message
    
    
\* Now model all the actions in our protocol.
\* For each RM: it can Prepare, Abort, and handle Commit or Abort messages
RMPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ [ type |-> "Abort" ] \notin msgs
    /\ rmState' = [ rmState EXCEPT ![rm] = "prepared" ]
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
    /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ]
    /\ UNCHANGED <<tmState, msgs, tmPrepared>>
    
RMHandleCommitMsg(rm) ==
    /\ [ type |-> "Commit" ] \in msgs
    /\ rmState[rm] = "working"
    /\ rmState' = [ rmState EXCEPT ![rm] = "committed" ]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMHandleAbortMsgs(rm) ==
    /\ [ type |-> "Abort" ] \in msgs
    /\ rmState[rm] = "working"
    /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ]
    /\ UNCHANGED <<tmState, msgs, tmPrepared>>


\* The TM has the following state transitions: handling a Prepared message, and
\* sending a Commit or Abort message.
TMHandlePreparedMsg(rm) ==
    /\ tmState = "init"
    /\ [ type |-> "Prepared", rm |-> rm] \in msgs
    /\ rm \notin tmPrepared
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED <<rmState, tmState, msgs>>
    
TMSendCommitMsg ==
    /\ tmState = "init"
    /\ tmState' = "committed"
    /\ tmPrepared = RM
    /\ msgs' = msgs \cup { [ type |-> "Commit" ] }
    /\ UNCHANGED <<rmState, tmPrepared>>

TMSendAbortMsg ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \cup { [ type |-> "Abort" ] }
    /\ UNCHANGED <<rmState, tmPrepared>>


    
\* The initial predicate defining our protocol.
Init ==
    \* Associate to each variable an initial state.
    /\ rmState = [ rm \in RM |-> "working" ]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}
    
Next == 
    \/ TMSendCommitMsg \/ TMSendAbortMsg
    \/ \E rm \in RM :
        TMHandlePreparedMsg(rm) 
        \/ RMPrepare(rm)
        \/ RMChooseToAbort(rm)
        \/ RMHandleCommitMsg(rm)
        \/ RMHandleAbortMsgs(rm)

Spec ==
    Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>


\* We assert that our spec respects the type invariant defined above.
THEOREM Spec => []TypeInv

\*TC == INSTANCE TCommit
\*
\*THEOREM Spec => TC!TCSpec

=============================================================================
\* Modification History
\* Last modified Fri Apr 17 10:25:28 CEST 2020 by adi
\* Created Thu Apr 16 10:16:46 CEST 2020 by adi
