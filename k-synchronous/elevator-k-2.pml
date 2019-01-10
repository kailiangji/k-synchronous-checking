// Elevator State Machine

#define N 4 // number of processes
#define K 2 // K-synchronous

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
#define UID 0
#define EID 1
#define DID 2
#define PIID 3
//pid UID, EID, DID, PIID; 

// message type
mtype = { openDoor, closeDoor, reset, stop, open, close,
	  doorOpened, doorClosed, doorStopped };

chan PICHAN = [0] of { mtype };
chan E = [K] of { mtype }; /* elevator channel */
chan D = [K] of { mtype }; /* door channel */

TSENDER sArr[K];
byte sindex = 0;

pid receiver = N;

// assume N <=8
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

inline changeFlag() {
  if
    :: empty(E) && empty(D) -> Mcausal(); flag!false 
    :: nempty(E) || nempty(D) -> flag!true
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
	      :: empty(E) && empty(D) ->
		 PICHAN!_ACT;
		 receiver = _TO;
		 StoreSender(_FROM, PIID, true);
		 Mcausal();
		 flag!false
	    fi
	 :: else ->
	    empty(E) && empty(D) ->
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
    :: _TO == EID -> SendActionToChannel(_FROM, _TO, E, _ACT)
    :: _TO == DID -> SendActionToChannel(_FROM, _TO, D, _ACT)
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

/* Elevator process */
proctype Elevator() {
  
Closed1:
  atomic{ SendActionToChannel(_pid, DID, D, reset); goto Closed2 }
  
Closed2:
  flag?true ->
  atomic{
    if
      :: E?closeDoor -> changeFlag(); goto Closed2
      :: E?openDoor -> changeFlag(); goto Opening1
    fi } 
  
Opening1:
  atomic{ SendActionToChannel(_pid, DID, D, open); goto Opening2 }
  
Opening2:
  flag?true ->
  atomic{ E?doorOpened -> changeFlag(); goto Opened }
  
Opened:
  atomic{ SendActionToChannel(_pid, DID, D, reset); goto Closing1 }

Closing1:
  atomic{ SendActionToChannel(_pid, DID, D, close); goto Closing2 }
  
Closing2:
  flag?true ->
  atomic{
    if
      :: E?doorClosed -> changeFlag(); goto Closed1
      :: E?openDoor -> changeFlag(); goto Stopping1
    fi } 
  
Stopping1:
  atomic{ SendActionToChannel(_pid, DID, D, stop); goto Stopping2 }
  
Stopping2:
  flag?true ->
  atomic{
    if
      :: E?openDoor -> changeFlag(); goto Stopping2
      :: E?doorClosed -> changeFlag(); goto Closed1
      :: E?doorStopped -> changeFlag(); goto Opening1
    fi } 
}

// Door process
proctype Door() {

Start:
  flag?true ->
  if
    :: atomic{ D?reset -> changeFlag(); goto Start }
    :: atomic{ D?stop -> changeFlag(); goto Start }
    :: atomic{ D?open -> changeFlag(); goto OpenDoor }
    :: atomic{ D?close -> changeFlag(); goto Closing }
  fi 
  
OpenDoor:
  atomic{ SendActionToChannel(_pid, EID, E, doorOpened); goto ResetDoor }
  
ResetDoor:
  flag?true ->
  if
    :: atomic{ D?open -> changeFlag(); goto ResetDoor }
    :: atomic{ D?close -> changeFlag(); goto ResetDoor }
    //:: atomic{ D?stop -> changeFlag(); goto ResetDoor }
    :: atomic{ D?reset -> changeFlag(); goto Start }
  fi 
  
StopDoor:
  atomic{ SendActionToChannel(_pid, EID, E, doorStopped); goto OpenDoor }
  
Closing:
  if
    :: flag?true -> atomic{ D?stop -> changeFlag(); goto StopDoor }
    :: atomic{ SendActionToChannel(_pid, EID, E, doorClosed); goto ResetDoor }
  fi  
}

// User process
active proctype User() {
  atomic{ run Elevator(); run Door(); run Pi(); flag!false }
Loop:
  atomic{
    if
      :: SendActionToChannel(_pid, EID, E, openDoor); goto Loop;
      :: SendActionToChannel(_pid, EID, E, closeDoor); goto Loop;
    fi }
}

// Pi process
proctype Pi() {
  mtype m;
Receive:
  atomic{ PICHAN?m -> goto Send }
  
Send:
  atomic{ SendAction(_pid, receiver, m) };
}