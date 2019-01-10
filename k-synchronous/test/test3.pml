#define N 4
#define K 6

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

#define P3ID 0
#define P2ID 1
#define P1ID 2
#define PIID 3

mtype = { Hello1, Hello2, Hello3 }

chan PICHAN = [0] of {mtype};
chan C1 = [K] of {mtype}
chan C2 = [K] of {mtype}
chan C3 = [K] of {mtype}

TSENDER sArr[K];
byte sindex = 0;
pid receiver = N;

// assume N <=8
BITV_8 B[N];

/* addB renews the should_be_blocked_processes of each process */
inline addB(_FROM, _TO) {
  d_step{if
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
	 fi}
}

chan flag = [1] of { bool };

/* setFlag randomly set flag to true or false */
inline setFlag() {
  if
    :: flag!true
    :: flag!false
  fi 
}

/* changeFlag sets flag and flagPI to false while all the channels are empty */
inline changeFlag() {
  if
    :: empty(C1) && empty(C2) && empty(C3) -> Mcausal(); flag!false 
    :: nempty(C1) || nempty(C2) || nempty(C3) -> flag!true
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
	      :: empty(C1) && empty(C2) && empty(C3) ->
		 PICHAN!_ACT;
		 receiver = _TO;
		 StoreSender(_FROM, PIID, true);
		 Mcausal();
		 flag!false
	    fi
	 :: else ->
	    empty(C1) && empty(C2) && empty(C3) ->
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

/* SendAction sends the behavior to a channel which belongs to
process *to* */
inline SendAction(_FROM, _TO, _ACT) {
  if
    :: _TO == P1ID -> SendActionToChannel(_FROM, _TO, C1, _ACT)
    :: _TO == P2ID -> SendActionToChannel(_FROM, _TO, C2, _ACT)
    :: _TO == P3ID -> SendActionToChannel(_FROM, _TO, C3, _ACT)
  fi
}

pid conflict = N;
byte count;
bool sawRS;
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

proctype P1() {

Send1:
  atomic{ SendActionToChannel(_pid, P2ID, C2, Hello1); goto Send2 }

Send2:
  atomic{ SendActionToChannel(_pid, P3ID, C3, Hello1); goto Rec1 }
  
Rec1:
  atomic{ flag?true ->
	  C1?Hello2 -> changeFlag(); goto Rec2}

Rec2:
  atomic{ flag?true ->
	  C1?Hello3 -> changeFlag()}
}

proctype P2() {

Send1:
  atomic{ SendActionToChannel(_pid, P1ID, C1, Hello2); goto Send2 }

Send2:
  atomic{ SendActionToChannel(_pid, P3ID, C3, Hello2); goto Rec1 }
  
Rec1:
  atomic{ flag?true ->
	  C2?Hello1 -> changeFlag(); goto Rec2}

Rec2:
  atomic{ flag?true ->
	  C2?Hello3 -> changeFlag()}
}

active proctype P3() {
  atomic{ flag!false; run P2(); run P1(); run Pi() };
  
Send1:
  atomic{ SendActionToChannel(_pid, P1ID, C1, Hello3); goto Send2 }

Send2:
  atomic{ SendActionToChannel(_pid, P2ID, C2, Hello3); goto Rec1 }
  
Rec1:
  atomic{ flag?true ->
	  C3?Hello1 -> changeFlag(); goto Rec2}

Rec2:
  atomic{ flag?true ->
	  C3?Hello2 -> changeFlag()}
}

/* Pi process */
proctype Pi() {
  mtype m;
  
Receive:
  atomic{ PICHAN?m -> goto Send }
  
Send:
  atomic{ SendAction(_pid, receiver, m) };
  /*goto Receive*/
}