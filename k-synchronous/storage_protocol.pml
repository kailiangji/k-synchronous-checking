// Replication Storage Protocol

#define N 7 // number of processes
#define K 1 // K-synchronous

#define MAX_SEND_NUM 200
#define MAX_TS 10

#define BITV_8 byte

#define ALL_1S          2147483647
#define SET_0(bv,i)     bv=bv&(~(1<<i))
#define SET_1(bv,i)     bv=bv|(1<<i)
#define SET_ALL_0(bv)   bv=0
#define SET_ALL_1(bv,n) bv=ALL_1S>>(31-n)
#define IS_MEM(bv,i)    (bv>>i)%2
//#define IS_0(bv,i)      (!(bv&(1<<i)))
//#define IS_1(bv,i)      (bv&(1<<i))

// assume N <= 8
// 01234567:0 bit to store matched field,
// 234 to store sid, 567 to store rid
#define TSENDER                 byte
#define SET_MATCHED(ts,matched) ts=ts|(matched<<7)
#define SET_SID(ts,sid)         ts=ts|(sid<<3)
#define SET_RID(ts,rid)         ts=ts|rid
#define IS_MATCHED(ts)          ts>>7
#define GET_SID(ts)             (ts>>3)%8
#define GET_RID(ts)             ts%8

// pid for each process
#define CID   0
#define MID   1
#define N1ID  2
#define N2ID  3
#define TID   4
#define RID   5
#define PIID  6
// pid CID, TID, N1ID, N2ID, MID, PRRD, PIID;

pid receiver = N

mtype = { store, timeOut, report, synchRequest };

chan N1     = [K] of { mtype, pid, byte };
chan N2     = [K] of { mtype, pid, byte };
chan M      = [K] of { mtype, pid, byte };
chan R      = [K] of { mtype, pid, byte };
chan PICHAN = [0] of { mtype, pid, byte };

TSENDER sArr[K];
byte sindex = 0;

// assume N <= 8
BITV_8 B[N];

// addB renews the should_be_blocked_processes of each process
inline addB(_FROM, _TO) {
  d_step{
    if
      :: IS_MEM(B[0], _FROM) -> SET_1(B[0], _TO)
      :: else -> skip
    fi
    if
      :: IS_MEM(B[1], _FROM) -> SET_1(B[1], _TO)
      :: else -> skip
    fi
    if
      :: IS_MEM(B[2], _FROM) -> SET_1(B[2], _TO)
      :: else -> skip
    fi
    if
      :: IS_MEM(B[3], _FROM) -> SET_1(B[3], _TO)
      :: else -> skip
    fi
    if
      :: IS_MEM(B[4], _FROM) -> SET_1(B[4], _TO)
      :: else -> skip
    fi
    if
      :: IS_MEM(B[5], _FROM) -> SET_1(B[5], _TO)
      :: else -> skip
    fi
    if
      :: IS_MEM(B[6], _FROM) -> SET_1(B[6], _TO)
      :: else -> skip
    fi }
  /*byte i = 0;
  do
    :: d_step{ i < N ->
	       if
		 :: B[i].mem[_FROM] -> B[i].mem[_TO] = true
		 :: !(B[i].mem[_FROM]) -> skip
	       fi
	       i++ }
    :: i >= N -> break
  od*/
}

chan flag = [1] of { bool };

// setFlag randomly set flag to true or false
inline setFlag() {
  if
    :: flag!true
    :: flag!false
  fi 
}

inline changeFlag() {
  if
    :: empty(N1)  && empty(N2)  && empty(M)  && empty(R) -> Mcausal(); flag!false 
    :: nempty(N1) || nempty(N2) || nempty(M) || nempty(R) -> flag!true
  fi
}

inline StoreSender(_FROM, _TO, _MATCHED) {
  sindex < K ->
  d_step{ sArr[sindex] = 0;
	  SET_SID(sArr[sindex], _FROM);
	  SET_RID(sArr[sindex], _TO);
	  SET_MATCHED(sArr[sindex], _MATCHED);
	  sindex++ } 
}

byte numSend;

inline SendActionToChannel(_FROM, _TO, _CHANNEL, _OP, _SENDER, _TS) {
  numSend < MAX_SEND_NUM ->
  flag?false ->
  if
    :: !IS_MEM(B[_TO], _FROM) ->
       if
	 :: _FROM != PIID ->
	    if
	      ::_CHANNEL!_OP,_SENDER,_TS; StoreSender(_FROM, _TO, true);
		 setFlag();
	      :: empty(N1) && empty(N2) && empty(M) && empty(R) ->
		 PICHAN!_OP,_SENDER,_TS; receiver = _TO;
		 StoreSender(_FROM, PIID, true); Mcausal(); flag!false
	    fi
	 :: else ->
	    empty(N1) && empty(N2) && empty(M) && empty(R)->
	    _CHANNEL!_OP,_SENDER,_TS; StoreSender(_FROM, _TO, true);
	    flag!true;
       fi 
    :: SET_1(B[_TO], _FROM); StoreSender(_FROM, _TO, false); setFlag()
  fi
  addB(_FROM, _TO);
  numSend++
}

// SendAction sends the behavior to a channel which belongs to
// process *to*
inline SendAction(_FROM, _TO, _OP, _SENDER, _TS) {
  if
    :: _TO == N1ID ->
       SendActionToChannel(_FROM, _TO, N1, _OP, _SENDER, _TS)
    :: _TO == N2ID ->
       SendActionToChannel(_FROM, _TO, N2, _OP, _SENDER, _TS)
    :: _TO == MID ->
       SendActionToChannel(_FROM, _TO, M, _OP, _SENDER, _TS)
    :: _TO == RID ->
       SendActionToChannel(_FROM, _TO, R, _OP, _SENDER, _TS)
  fi
}

pid conflict = N;
bool sawRS;
byte count;

bool cone[N];

byte i, j;
bool lastIsRec;

inline CountMinusOne(_COUNT) {
  if
    :: _COUNT > 0 -> _COUNT--
    :: else -> skip
  fi
}

inline Mcausal() {
 // byte i, j;
  d_step{ i = 0; j = 0 };
  do
    :: i < sindex ->
       if
	 :: GET_SID(sArr[i]) == PIID ->
	    do
	      :: j < N -> d_step{cone[j] = false; j++}
	      :: else -> goto Mviol
	    od
	 :: else -> i++
       fi
    :: else -> d_step{i = 0; j= 0}; break
  od
       
  do
    :: i < sindex ->
       if
	 :: GET_RID(sArr[i]) == PIID ->
	    d_step{cone[GET_SID(sArr[i])] = true; i = 0; j = 0};
	    goto Mviol	    
	 :: else -> i++
       fi
    :: else -> i= 0; break
  od
  
  do
    :: j < sindex ->
       if
	 :: IS_MATCHED(sArr[j]) && cone[GET_SID(sArr[j])] ->
	    cone[GET_RID(sArr[j])] = true;
	    GET_RID(sArr[j]) != receiver		 
	 :: else -> skip
       fi
       
       do
	 :: i < j ->
	    if
	      :: cone[GET_RID(sArr[i])]&&GET_SID(sArr[i]) == GET_SID(sArr[j]) ->
		 cone[GET_RID(sArr[j])] = true;
		 GET_RID(sArr[j]) != receiver;
		 j++;
		 break
	      :: else -> i++
	    fi
       	 :: else -> d_step{i = 0; j++}; break
       od
    :: else -> break
  od
  
Mviol:
  i = 0;
  //lastIsRec = false;
  do
    :: i < sindex ->
       if
	 :: GET_RID(sArr[i]) == PIID ->
	    IS_MATCHED(sArr[i]) ->
	    d_step{conflict = GET_SID(sArr[i]); count = K}
	 :: GET_SID(sArr[i]) == PIID ->
	    IS_MATCHED(sArr[i]) ->
	    assert(conflict != GET_RID(sArr[i]) || (count > 0 && !sawRS))
	 :: else ->
	    if
	      :: IS_MATCHED(sArr[i])&&(conflict == GET_SID(sArr[i])||conflict == GET_RID(sArr[i])) ->
		 if
		   :: lastIsRec ->
		      if
			:: conflict == GET_SID(sArr[i]) ->
			   sawRS = true;
			:: else -> skip;
		      fi
		   :: else -> skip
		 fi
		 if
		   :: conflict = GET_SID(sArr[i]);
		      lastIsRec = false
		   :: conflict = GET_RID(sArr[i]);
		      if
			:: i == (sindex - 1) -> lastIsRec = true
			:: else -> lastIsRec = false
		      fi
		 fi;
		 CountMinusOne(count)
	      :: IS_MATCHED(sArr[i])==0 && conflict == GET_SID(sArr[i]) ->
		 d_step{CountMinusOne(count); lastIsRec = false}
	      :: skip
	    fi
       fi
       i++
    :: else -> sindex = 0; break
  od
}

//----------------state machine-------------------------------
active proctype Client() {
  atomic{ run Manager(); run Node1(); run Node2(); run Timer(); run Report(); run Pi();
	  flag!false }
  
Loop:
  atomic{ SendActionToChannel(_pid, MID, M, store, CID, 0); goto Loop }
}

proctype Timer() {

Loop:
  atomic{
    if
      :: SendActionToChannel(_pid, MID, M, timeOut, TID, 0); goto Loop
      :: SendActionToChannel(_pid, N1ID, N1, timeOut, TID, 0); goto Loop
      :: SendActionToChannel(_pid, N2ID, N2, timeOut, TID, 0); goto Loop
    fi }
}

proctype Node1() {
  byte node_ts;
  //goto SendReport;
Start:
  atomic{ flag?true ->
	  if
	    :: N1?store,_,node_ts -> changeFlag(); goto Start
	    :: N1?synchRequest,_,_ -> changeFlag(); goto SendReport
	    :: N1?timeOut,_,_ -> changeFlag(); goto SendReport
	  fi }
  
SendReport:
  //atomic{ SendActionToChannel(_pid, MID, M, report, N1ID, node_ts); goto Start }
  atomic{ SendActionToChannel(_pid, RID, M, report, N1ID, node_ts); goto Start }
}

proctype Node2() {
  byte node_ts;
  //goto SendReport;
Start:
  atomic{ flag?true ->
	  if
	    :: N2?store,_, node_ts -> changeFlag(); goto Start
	    :: N2?synchRequest,_,_ -> changeFlag(); goto SendReport
	    :: N2?timeOut,_,_ -> changeFlag(); goto SendReport
	  fi }
  
SendReport:
  //atomic{ SendActionToChannel(_pid, MID, M, report, N2ID, node_ts); goto Start }
  atomic{ SendActionToChannel(_pid, RID, M, report, N2ID, node_ts); goto Start }
}

byte ts;

proctype Manager() {
  
Start:
  atomic{ flag?true ->
	  if
	    :: M?store,_,_ -> changeFlag(); goto ClientReq
	    :: M?timeOut,_,_ -> changeFlag(); goto RepairNodes
	    //:: M?report,sender,node_ts -> changeFlag(); goto ProcessReport
	  fi }
  
ClientReq:
  atomic{ SendActionToChannel(_pid, N1ID, N1, store, MID, ts) };
  atomic{ SendActionToChannel(_pid, N2ID, N2, store, MID, ts);
	  ts++;
	  ts < MAX_TS -> goto Start }
  
RepairNodes:
  atomic{ SendActionToChannel(_pid, N1ID, N1, synchRequest, MID, 0) };
  atomic{ SendActionToChannel(_pid, N2ID, N2, synchRequest, MID, 0);
	  goto Start }
/*  
ProcessReport:
  atomic{ if
	    :: node_ts != ts ->
	       SendAction(_pid, sender, store, MID, ts); goto Start
	    :: else -> goto Start
	  fi }
 */
}

proctype Report() {
  byte node_ts;
  pid sender;
  goto ReceiveReport;

ReceiveReport:
  atomic{ flag?true ->
	  R?report,sender,node_ts -> changeFlag(); goto ProcessReport;}

ProcessReport:
  atomic{
    if
      :: node_ts != ts ->
	 SendAction(_pid, sender, store, RID, node_ts); goto ReceiveReport;
      :: else -> goto ReceiveReport;
    fi }
}

// Pi process
proctype Pi() {
  mtype op;
  pid sender;
  byte node_ts;
  
Receive:
  atomic{ PICHAN?op,sender, node_ts -> goto Send }
  
Send:
  atomic{ SendAction(_pid, receiver, op, sender, node_ts) };
}