// German

#define N 6
#define K 1

#define MAX_SEND_NUM 10
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
#define HID   0
#define C1ID  1
#define C2ID  2
#define C3ID  3
#define CPUID 4
#define PIID  5
// pid HID, C1ID, C2ID, C3ID, CPUID, PIID;

pid receiver = N;

mtype = { req_share,
	  req_excl,
	  //need_invalidate,
	  invalidate_ack,
	  grant,
	  ask_share,
	  ask_excl,
	  invalidate,
	  grant_excl,
	  grant_share,
	  //normal,
	  //wait,
	  //invalidate_sharers,
	  //sharer_id
};

chan H      = [K] of { mtype, pid };
chan C1     = [K] of { mtype };
chan C2     = [K] of { mtype };
chan C3     = [K] of { mtype };
chan PICHAN = [0] of { mtype, pid };

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
    :: empty(H) && empty(C1) && empty(C2) && empty(C3) ->
       Mcausal(); flag!false
    :: nempty(H) || nempty(C1) || nempty(C2) || nempty(C3) ->
       flag!true
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

byte sendNum;

inline SendActionToChannel(_FROM, _TO, _CHANNEL, _ACT, _SENDER) {
  sendNum < MAX_SEND_NUM ->
  flag?false ->
  if
    :: !IS_MEM(B[_TO], _FROM) ->
       if
	 :: _FROM != PIID ->
	    if
	      ::_CHANNEL!_ACT,_SENDER; StoreSender(_FROM, _TO, true);
		 setFlag();
	      :: empty(H) && empty(C1) && empty(C2) && empty(C3) ->
		 PICHAN!_ACT,_SENDER; receiver = _TO;
		 StoreSender(_FROM, PIID, true);
		 Mcausal(); flag!false
	    fi
	 :: else ->
	    empty(H) && empty(C1) && empty(C2) && empty(C3) ->
	    _CHANNEL!_ACT,_SENDER; StoreSender(_FROM, _TO, true);
	    flag!true
       fi 
    :: SET_1(B[_TO], _FROM); StoreSender(_FROM, _TO, false);
       setFlag()
  fi
  addB(_FROM, _TO);
  sendNum++
}

inline SendActionToClientChannel(_FROM, _TO, _CHANNEL, _ACT) {
  sendNum < MAX_SEND_NUM ->
  flag?false ->
  if
    :: !IS_MEM(B[_TO], _FROM) ->
       if
	 :: _FROM != PIID ->
	    if
	      :: _CHANNEL!_ACT; StoreSender(_FROM, _TO, true);
		 setFlag();
	      :: empty(H) && empty(C1) && empty(C2) && empty(C3) ->
		 PICHAN!_ACT,N; receiver = _TO;
		 StoreSender(_FROM, PIID, true);
		 Mcausal(); flag!false
	    fi
	 :: else ->
	    empty(H) && empty(C1) && empty(C2) && empty(C3) ->
	    _CHANNEL!_ACT; StoreSender(_FROM, _TO, true);
	    flag!true
       fi 
    :: SET_1(B[_TO], _FROM); StoreSender(_FROM, _TO, false);
       setFlag()
  fi
  addB(_FROM, _TO);
  sendNum++
}

inline SendAction(_FROM, _TO, _ACT, _SENDER) {
  if
    :: _TO == HID ->
       SendActionToChannel(_FROM, _TO, H, _ACT, _SENDER)
    :: _TO == C1ID ->
       SendActionToClientChannel(_FROM, _TO, C1, _ACT)
    :: _TO == C2ID ->
       SendActionToClientChannel(_FROM, _TO, C2, _ACT)
    :: _TO == C3ID ->
       SendActionToClientChannel(_FROM, _TO, C3, _ACT)
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

// chan sharer_list = [3] of { pid };

active proctype Host() {
  BITV_8 sharer_list;
  pid curr_client;
  //pid curr_cpu;
  BITV_8 ce;
  // bool is_curr_req_excl;
  // bool is_excl_granted;
  // byte idx, s;
  // pid temp;
  atomic{ run Client1(); run Client2(); run Client3(); run CPU(); run Pi();
	  flag!false };

ReceiveState:
  atomic{ flag?true ->
	  if
	    :: H?req_share,curr_client -> changeFlag(); goto ShareRequest
	    :: H?req_excl,curr_client  -> changeFlag(); goto ExclRequest
	  fi }
  
ShareRequest:
  atomic{ SET_0(ce, 1); goto ProcessReq };
  
ExclRequest:
  atomic{ SET_1(ce, 1); goto ProcessReq };
  
ProcessReq:
  atomic{ if
	    :: IS_MEM(ce, 1) || IS_MEM(ce, 0) -> goto Inv
	    :: else -> goto GrantAccess
	  fi }

Inv:
  atomic{ if
	    :: !IS_MEM(sharer_list, 1)&&!IS_MEM(sharer_list, 2)&&!IS_MEM(sharer_list, 3) ->
	       goto GrantAccess
	    :: else ->
	       if
		 :: IS_MEM(sharer_list, 1) ->
		    SendActionToClientChannel(_pid, C1ID, C1, invalidate)
		 :: else -> skip
	       fi
	       if
	       	 :: IS_MEM(sharer_list, 2) ->
		    SendActionToClientChannel(_pid, C2ID, C2, invalidate)
		 :: else -> skip
	       fi
	       if
	       	 :: IS_MEM(sharer_list, 3) ->
		    SendActionToClientChannel(_pid, C3ID, C3, invalidate)
		 :: else -> skip
	       fi
	  fi }
  
  atomic{ flag?true ->
	  if
	    :: H?invalidate_ack,_ ->
	       changeFlag();
	       /* do rec_ack */
	       IS_MEM(sharer_list, 1) || IS_MEM(sharer_list, 2) || IS_MEM(sharer_list, 3) ->
	       if
		 :: IS_MEM(sharer_list, 1) ->
		    SET_0(sharer_list, 1);
		    if
		      :: !IS_MEM(sharer_list, 2) && !IS_MEM(sharer_list, 3) ->
			 goto GrantAccess
		      :: else -> skip
		    fi
		 :: IS_MEM(sharer_list, 2) ->
		    SET_0(sharer_list, 2);
		    if
		      :: !IS_MEM(sharer_list, 1) && !IS_MEM(sharer_list, 3) ->
			 goto GrantAccess
		      :: else -> skip
		    fi
		 :: IS_MEM(sharer_list, 3) ->
		    SET_0(sharer_list, 3);
		    if
		      :: !IS_MEM(sharer_list, 1) && !IS_MEM(sharer_list, 2) ->
			 goto GrantAccess
		      :: else -> skip
		    fi
	       fi
	    :: H?grant,_ -> changeFlag(); goto GrantAccess
	  fi }

GrantAccess:
  atomic{ if
	    :: IS_MEM(ce, 1) ->
	       SET_1(ce, 0);
	       SendAction(_pid, curr_client, grant_excl, _pid)
	    :: else ->
	       SendAction(_pid, curr_client, grant_share, _pid)
	  fi;
	  SET_1(sharer_list, curr_client); goto ReceiveState }
}

BITV_8 pending;

proctype Client1() {
  //bool pending;

Start:
  atomic{ SET_0(pending, 1); goto Invalid };
  
Invalid:
  atomic{ flag?true ->
	  if
	    :: C1?ask_share -> changeFlag(); goto Asked_share;
	    :: C1?ask_excl -> changeFlag(); goto Asked_excl;
	    :: C1?invalidate -> changeFlag(); goto Invalidating;
	    :: C1?grant_excl -> changeFlag(); goto Exclusive;
	    :: C1?grant_share -> changeFlag(); goto Sharing;
	  fi }

Asked_share:
  atomic{ SendActionToChannel(_pid, HID, H, req_share, _pid);
	  SET_1(pending, 1); goto Invalid_wait };
  
Asked_excl:
  atomic{ SendActionToChannel(_pid, HID, H, req_excl, _pid);
	  SET_1(pending, 1); goto Invalid_wait };
  
Invalid_wait:
  atomic{ flag?true ->
	  if
	    :: C1?invalidate -> changeFlag(); goto Invalidating
	    :: C1?grant_excl -> changeFlag(); goto Exclusive
	    :: C1?grant_share -> changeFlag(); goto Sharing
	  fi }
  
Asked_ex2:
  atomic{ SendActionToChannel(_pid, HID, H, req_excl, _pid);
	  SET_1(pending, 1); goto Sharing_wait };
  
Sharing:
  SET_0(pending, 1);
  atomic{ flag?true ->
	  if
	    :: C1?invalidate -> changeFlag(); goto Invalidating
	    :: C1?grant_share -> changeFlag(); goto Sharing
	    :: C1?grant_excl -> changeFlag(); goto Exclusive
	    :: C1?ask_share -> changeFlag(); goto Sharing
	    :: C1?ask_excl -> changeFlag(); goto Asked_ex2
	  fi }
  
Sharing_wait:
  atomic{ flag?true ->
	  if
	    :: C1?invalidate -> changeFlag(); goto Invalidating
	    :: C1?grant_share -> changeFlag(); goto Sharing_wait
	    :: C1?grant_excl -> changeFlag(); goto Exclusive
	  fi }
  
Exclusive:
  SET_0(pending, 1);
Exclusive1:
  atomic{ flag?true ->
	  if
	    :: C1?ask_share -> changeFlag(); goto Exclusive1
	    :: C1?ask_excl -> changeFlag(); goto Exclusive1
	    :: C1?invalidate -> changeFlag(); goto Invalidating
	    :: C1?grant_share -> changeFlag(); goto Sharing_wait
	    :: C1?grant_excl -> changeFlag(); goto Exclusive
	  fi }
  
Invalidating:
  atomic{ SendActionToChannel(_pid, HID, H, invalidate, _pid);
	  if
	    :: IS_MEM(pending, 1) -> goto Invalid_wait
	    :: else -> goto Invalid
	  fi }
}

proctype Client2() {
  //bool pending[1];

Start:
  atomic{ SET_0(pending, 2); goto Invalid };
  
Invalid:
  atomic{ flag?true ->
	  if
	    :: C2?ask_share -> changeFlag(); goto Asked_share;
	    :: C2?ask_excl -> changeFlag(); goto Asked_excl;
	    :: C2?invalidate -> changeFlag(); goto Invalidating;
	    :: C2?grant_excl -> changeFlag(); goto Exclusive;
	    :: C2?grant_share -> changeFlag(); goto Sharing;
	  fi }

Asked_share:
  atomic{ SendActionToChannel(_pid, HID, H, req_share, _pid);
	  SET_1(pending, 2); goto Invalid_wait };
  
Asked_excl:
  atomic{ SendActionToChannel(_pid, HID, H, req_excl, _pid);
	  SET_1(pending, 2); goto Invalid_wait };
  
Invalid_wait:
  atomic{ flag?true ->
	  if
	    :: C2?invalidate -> changeFlag(); goto Invalidating
	    :: C2?grant_excl -> changeFlag(); goto Exclusive
	    :: C2?grant_share -> changeFlag(); goto Sharing
	  fi }
  
Asked_ex2:
  atomic{ SendActionToChannel(_pid, HID, H, req_excl, _pid);
	  SET_1(pending, 2); goto Sharing_wait };
  
Sharing:
  SET_0(pending, 2);
  atomic{ flag?true ->
	  if
	    :: C2?invalidate -> changeFlag(); goto Invalidating
	    :: C2?grant_share -> changeFlag(); goto Sharing
	    :: C2?grant_excl -> changeFlag(); goto Exclusive
	    :: C2?ask_share -> changeFlag(); goto Sharing
	    :: C2?ask_excl -> changeFlag(); goto Asked_ex2
	  fi }
  
Sharing_wait:
  atomic{ flag?true ->
	  if
	    :: C2?invalidate -> changeFlag(); goto Invalidating
	    :: C2?grant_share -> changeFlag(); goto Sharing_wait
	    :: C2?grant_excl -> changeFlag(); goto Exclusive
	  fi }
  
Exclusive:
  SET_0(pending, 2);
Exclusive1:
  atomic{ flag?true ->
	  if
	    :: C2?ask_share -> changeFlag(); goto Exclusive1
	    :: C2?ask_excl -> changeFlag(); goto Exclusive1
	    :: C2?invalidate -> changeFlag(); goto Invalidating
	    :: C2?grant_share -> changeFlag(); goto Sharing_wait
	    :: C2?grant_excl -> changeFlag(); goto Exclusive
	  fi }
  
Invalidating:
  atomic{ SendActionToChannel(_pid, HID, H, invalidate, _pid);
	  if
	    :: IS_MEM(pending, 2) -> goto Invalid_wait
	    :: else -> goto Invalid
	  fi }
}

proctype Client3() {
  //bool pending[2];

Start:
  atomic{ SET_0(pending, 3); goto Invalid };
  
Invalid:
  atomic{ flag?true ->
	  if
	    :: C3?ask_share -> changeFlag(); goto Asked_share;
	    :: C3?ask_excl -> changeFlag(); goto Asked_excl;
	    :: C3?invalidate -> changeFlag(); goto Invalidating;
	    :: C3?grant_excl -> changeFlag(); goto Exclusive;
	    :: C3?grant_share -> changeFlag(); goto Sharing;
	  fi }

Asked_share:
  atomic{ SendActionToChannel(_pid, HID, H, req_share, _pid);
	  SET_1(pending, 3); goto Invalid_wait };
  
Asked_excl:
  atomic{ SendActionToChannel(_pid, HID, H, req_excl, _pid);
	  SET_1(pending, 3); goto Invalid_wait };
  
Invalid_wait:
  atomic{ flag?true ->
	  if
	    :: C3?invalidate -> changeFlag(); goto Invalidating
	    :: C3?grant_excl -> changeFlag(); goto Exclusive
	    :: C3?grant_share -> changeFlag(); goto Sharing
	  fi }
  
Asked_ex2:
  atomic{ SendActionToChannel(_pid, HID, H, req_excl, _pid);
	  SET_1(pending, 3); goto Sharing_wait };
  
Sharing:
  SET_0(pending, 3);
  atomic{ flag?true ->
	  if
	    :: C3?invalidate -> changeFlag(); goto Invalidating
	    :: C3?grant_share -> changeFlag(); goto Sharing
	    :: C3?grant_excl -> changeFlag(); goto Exclusive
	    :: C3?ask_share -> changeFlag(); goto Sharing
	    :: C3?ask_excl -> changeFlag(); goto Asked_ex2
	  fi }
  
Sharing_wait:
  atomic{ flag?true ->
	  if
	    :: C3?invalidate -> changeFlag(); goto Invalidating
	    :: C3?grant_share -> changeFlag(); goto Sharing_wait
	    :: C3?grant_excl -> changeFlag(); goto Exclusive
	  fi }
  
Exclusive:
  SET_0(pending, 3);
Exclusive1:
  atomic{ flag?true ->
	  if
	    :: C3?ask_share -> changeFlag(); goto Exclusive1
	    :: C3?ask_excl -> changeFlag(); goto Exclusive1
	    :: C3?invalidate -> changeFlag(); goto Invalidating
	    :: C3?grant_share -> changeFlag(); goto Sharing_wait
	    :: C3?grant_excl -> changeFlag(); goto Exclusive
	  fi }
  
Invalidating:
  atomic{ SendActionToChannel(_pid, HID, H, invalidate, _pid);
	  if
	    :: IS_MEM(pending, 3) -> goto Invalid_wait
	    :: else -> goto Invalid
	  fi }
}

proctype CPU() {

MakeReq:
  atomic{ if
	    :: SendActionToClientChannel(_pid, C1ID, C1, ask_share)
	    :: SendActionToClientChannel(_pid, C1ID, C1, ask_excl)
	    :: SendActionToClientChannel(_pid, C2ID, C2, ask_share)
	    :: SendActionToClientChannel(_pid, C2ID, C2, ask_excl)
	    :: SendActionToClientChannel(_pid, C3ID, C3, ask_share)
	    :: SendActionToClientChannel(_pid, C3ID, C3, ask_excl)
	  fi }
  goto MakeReq
}

// Pi process
proctype Pi() {
  mtype m;
  pid sender;
Receive:
  atomic{ PICHAN?m,sender -> goto Send }
  
Send:
  atomic{ SendAction(_pid, receiver, m, sender) };
}
