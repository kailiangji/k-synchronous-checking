// Commit Protocol

#define N 5 // number of processes
#define K 1 // K-synchronous

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
// 01234567:0 bit to store matched field, 234 to store sid, 567 to
// store rid
#define TSENDER                 byte
#define SET_MATCHED(ts,matched) ts=ts|(matched<<7)
#define SET_SID(ts,sid)         ts=ts|(sid<<3)
#define SET_RID(ts,rid)         ts=ts|rid
#define IS_MATCHED(ts)          ts>>7
#define GET_SID(ts)             (ts>>3)%8
#define GET_RID(ts)             ts%8

// message type
mtype = { update, OK }

// pid for each process
#define CID  0
#define MID  1
#define N1ID 2
#define N2ID 3
#define PIID 4

pid receiver = N;
chan PICHAN = [0] of { mtype }; 
chan M      = [K] of { mtype };
chan C      = [K] of { mtype };
chan N1     = [K] of { mtype };
chan N2     = [K] of { mtype };

TSENDER sArr[K];
byte sindex = 0;

// assume N <= 8
BITV_8 B[N];

// addB renews the should_be_blocked_processes of each process
inline addB(_FROM, _TO) {
  d_step{ if
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
	  fi }
  
  /* byte idx;
  idx = 0;
  do
    :: idx < N ->
       d_step{
	 if
	   :: IS_MEM(B[idx], _FROM) -> SET_1(B[idx], _TO)
	   :: else -> skip
	 fi;
	 idx++ }
    :: else -> break
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

// changeFlag sends *false* to flag while all the channels are empty,
// *true* otherwise
inline changeFlag() {
  if
    :: empty(M) && empty(C) && empty(N1) && empty(N2)->
       Mcausal(); flag!false
    :: nempty(M) || nempty(C) || nempty(N1) || nempty(N2) -> flag!true
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

inline SendActionToChannel(_FROM, _TO, _CHANNEL, _ACT) {
  flag?false ->
  if
    :: !IS_MEM(B[_TO], _FROM) ->
       if
	 :: _FROM != PIID ->
	    if
	      :: _CHANNEL!_ACT;
		 StoreSender(_FROM, _TO, true);
		 setFlag();
	      :: empty(M) && empty(C) && empty(N1) && empty(N2) ->
		 PICHAN!_ACT;
		 receiver = _TO;
		 StoreSender(_FROM, PIID, true);
		 Mcausal(); flag!false
	    fi
	 :: else ->
	    empty(M) && empty(C) && empty(N1) && empty(N2) ->
	    _CHANNEL!_ACT;
	    StoreSender(_FROM, _TO, true);
	    flag!true;
       fi 
    :: SET_1(B[_TO], _FROM);
       StoreSender(_FROM, _TO, false);
       setFlag()
  fi
  addB(_FROM, _TO)
}

inline SendAction(_FROM, _TO, _ACT) {
  if
    :: _TO == MID  -> SendActionToChannel(_FROM, _TO, M, _ACT)
    :: _TO == CID  -> SendActionToChannel(_FROM, _TO, C, _ACT)
    :: _TO == N1ID -> SendActionToChannel(_FROM, _TO, N1, _ACT)
    :: _TO == N2ID -> SendActionToChannel(_FROM, _TO, N2, _ACT)
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

// Manager process
proctype Manager() {
  
Start:
  atomic{ flag?true ->
	  M?update -> changeFlag(); goto Send1 }

Send1:
  atomic{ SendActionToChannel(_pid, N1ID, N1, update); goto Send2 }

Send2:
  atomic{ SendActionToChannel(_pid, N2ID, N2, update); goto Rec1 }

Rec1:
  atomic{ flag?true ->
	  M?OK -> changeFlag(); goto Rec2 }

Rec2:
  atomic{ flag?true ->
	  M?OK -> changeFlag(); goto Rec3 }

Rec3:
  atomic{ SendActionToChannel(_pid, CID, C, OK); goto Start }
}

/* The Client process */
active proctype Client() {
  atomic{ run Manager(); run Node1(); run Node2(); run Pi(); flag!false }

Send:
  atomic{ SendActionToChannel(_pid, MID, M, update); goto Ack }

Ack:
  atomic{ flag?true ->
	  C?OK -> changeFlag(); goto Send }
}

// Node n1
proctype Node1() {
  
Send:
  atomic{ flag?true ->
	  N1?update -> changeFlag(); goto Ack }
  
Ack:
  atomic{ SendActionToChannel(_pid, MID, M, OK); goto Send }
}

// Node n2
proctype Node2() {
  
Send:
  atomic{ flag?true ->
	  N2?update -> changeFlag(); goto Ack }
  
Ack:
  atomic{ SendActionToChannel(_pid, MID, M, OK); goto Send }
}

// Pi process
proctype Pi() {
  mtype m;
  
Receive:
  atomic{ PICHAN?m -> changeFlag(); goto Send}
  
Send:
  atomic{ SendAction(_pid, receiver, m) };
}
