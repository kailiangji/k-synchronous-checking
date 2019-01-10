/* Replication Storage Protocol */

#define K 1

pid CID, MID, TID, N1ID, N2ID;

mtype = { store, timeOut, report, synchRequest };

/* protocol message type */
typedef ptype {
  mtype op;
  chan sender;
  byte val;
  byte ts
}

chan T  = [K] of { mtype, pid, byte }
chan N1 = [K] of { mtype, pid, byte }
chan N2 = [K] of { mtype, pid, byte }
chan M  = [K] of { mtype, pid, byte }
chan R  = [K] of { mtype, pid, byte } 

active proctype Client() {
  CID = _pid; MID = run Manager(); N1ID = run Node1();
  N2ID = run Node2(); TID = run Timer(); run Report();

Loop:
  M!store,CID,0;
  goto Loop
}

proctype Timer() {

Loop:
  if
    :: M!timeOut,TID,0; goto Loop
    :: N1!timeOut,TID,0; goto Loop
    :: N2!timeOut,TID,0; goto Loop
  fi
}

proctype Node1() {
  byte node_ts;
  
Start:
  if
    :: N1?store,_,node_ts -> goto Start
    :: N1?synchRequest,_,_ -> goto SendReport
    :: N1?timeOut,_,_ -> goto SendReport
  fi

SendReport:
  R!report,N1ID,node_ts;
  goto Start
}

proctype Node2() {
  byte node_ts;
  
Start:
  if
    :: N2?store,_,node_ts -> goto Start
    :: N2?synchRequest,_,_ -> goto SendReport
    :: N2?timeOut,_,_ -> goto SendReport
  fi

SendReport:
  R!report,N2ID,node_ts;
  goto Start
}

byte ts;

proctype Manager() {
  
Start:
  if
    :: M?store,_,_ -> goto ClientReq
    :: M?timeOut,_,_ -> goto RepairNodes
    //:: M?report,sender,node_ts -> goto ProcessReport
  fi

ClientReq:
  N1!store,MID,ts;
  N2!store,MID,ts;
  ts++
  goto Start
  
RepairNodes:
  N1!synchRequest,MID,0;
  N2!synchRequest,MID,0;
  goto Start
}

proctype Report() {
  byte node_ts;
  pid sender;
  goto ReceiveReport;

ReceiveReport:
  R?report,sender,node_ts -> goto ProcessReport;

ProcessReport:
  if
    :: node_ts != ts ->
       if
	 :: sender == N1ID -> N1!store,MID,ts
	 :: sender == N2ID -> N2!store,MID,ts
       fi
    :: else -> skip
  fi
  goto ReceiveReport;
}