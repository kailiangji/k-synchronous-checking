// OSR

#define N 5
#define K 1

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
// 01234567:0 bit to store matched field, 234 to store sid, 567 to store rid
#define TSENDER                 byte
#define SET_MATCHED(ts,matched) ts=ts|(matched<<7)
#define SET_SID(ts,sid)         ts=ts|(sid<<3)
#define SET_RID(ts,rid)         ts=ts|rid
#define IS_MATCHED(ts)          ts>>7
#define GET_SID(ts)             (ts>>3)%8
#define GET_RID(ts)             ts%8

// pid for each process
#define UMID   0
#define OSRDID 1
#define LEDMID 2
#define SMID   3
#define PIID   4
// pid SMID, LEDMID, OSRDID, UMID, PIID;

pid receiver = N;

mtype = { eD0Entry,
	  eD0Exit,
	  //eTimerFired,
	  eSwitchStatusChange,
	  eTransferSuccess,
	  eTransferFailure,
	  //eStopTimer,
	  eUpdateBarGraphStateUsingControlTransfer,
	  eSetLedStateToUnstableUsingControlTransfer,
	  //eStartDebounceTimer,
	  eSetLedStateToStableUsingControlTransfer,
	  eStoppingSuccess,
	  eStoppingFailure,
	  eOperationSuccess,
	  eOperationFailure,
	  //eTimerStopped,
	  //eYes,
	  //eNo,
	  //eUnit
};

chan PICHAN = [0] of { mtype };
chan UM = [K] of { mtype };
chan OSRD = [K] of { mtype };
chan SM = [K] of { mtype };
chan LED = [K] of { mtype };

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
    fi }
}

chan flag = [1] of { bool };

// setFlag randomly set flag to true or false
inline setFlag() {
  if
    :: flag!true
    :: flag!false
  fi 
}

inline changeFlag()
{
  if
    :: empty(UM)&&empty(OSRD)&&empty(SM)&&empty(LED) ->
       Mcausal(); flag!false 
    :: nempty(UM)||nempty(OSRD)||nempty(SM)||nempty(LED) ->
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
	      :: empty(UM) && empty(OSRD) && empty(SM) && empty(LED) ->
		 PICHAN!_ACT;
		 receiver = _TO;
		 StoreSender(_FROM, PIID, true);
		 Mcausal();
		 flag!false
	    fi
	 :: else ->
	    empty(UM) && empty(OSRD) && empty(SM) && empty(LED) ->
	    _CHANNEL!_ACT;
	    StoreSender(_FROM, _TO, true);
	    flag!true
       fi 
    :: SET_1(B[_TO], _FROM);
       StoreSender(_FROM, _TO, false);
       setFlag()
  fi
  addB(_FROM, _TO)
}

// SendAction sends the behavior to a channel which belongs to
// process *to*
inline SendAction(_FROM, _TO, _ACT) {
  if
    :: _TO == UMID -> SendActionToChannel(_FROM, _TO, UM, _ACT)
    :: _TO == OSRDID -> SendActionToChannel(_FROM, _TO, OSRD, _ACT)
    :: _TO == LEDMID -> SendActionToChannel(_FROM, _TO, LED, _ACT)
    :: _TO == SMID -> SendActionToChannel(_FROM, _TO, SM, _ACT)
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

/*------------------state machine--------------------------*/
proctype SwitchMachine() {

ChangeSwitchStatus:
  atomic{ SendActionToChannel(_pid, OSRDID, OSRD, eSwitchStatusChange);
	  goto ChangeSwitchStatus }
}

proctype LEDMachine() {

LED_Init:
  flag?true ->
  if
    :: atomic{ LED?eUpdateBarGraphStateUsingControlTransfer ->
	       changeFlag(); goto ProcessUpdateLED }
    :: atomic{ LED?eSetLedStateToUnstableUsingControlTransfer ->
	       changeFlag(); goto UnstableLED }
    :: atomic{ LED?eSetLedStateToStableUsingControlTransfer ->
	       changeFlag(); goto StableLED }
  fi

ProcessUpdateLED:
  atomic{
    if
      :: SendActionToChannel(_pid, OSRDID, OSRD, eTransferSuccess)
      :: SendActionToChannel(_pid, OSRDID, OSRD, eTransferFailure)
    fi; 
    goto LED_Init }

UnstableLED:
  atomic{ SendActionToChannel(_pid, OSRDID, OSRD, eTransferSuccess) };

  flag?true ->
  if
    :: atomic{ LED?eSetLedStateToStableUsingControlTransfer ->
	       changeFlag(); goto LED_Init }
    :: atomic{ LED?eUpdateBarGraphStateUsingControlTransfer ->
	       changeFlag(); goto ProcessUpdateLED }
  fi

StableLED:
  atomic{ SendActionToChannel(_pid, OSRDID, OSRD, eTransferSuccess);
	  goto LED_Init }
}

proctype OSRDriverMachine() {
  
sDxDriver:
  flag?true -> 
  if
    :: atomic{ OSRD?eD0Exit -> changeFlag();
	       goto sDxDriver }
    :: atomic{ OSRD?eD0Entry -> changeFlag();
	       goto sCompleteD0EntryDriver }
  fi
  
sCompleteD0EntryDriver:
  // CompleteDStateTransition();
  goto  sWaitingForSwitchStatusChangeDriver;

sWaitingForSwitchStatusChangeDriver:
  flag?true ->
  if
    :: atomic{ OSRD?eD0Entry -> changeFlag();
	       goto sWaitingForSwitchStatusChangeDriver }
    :: atomic{ OSRD?eD0Exit -> changeFlag();
	       goto sCompletingD0ExitDriver }
    :: atomic{ OSRD?eSwitchStatusChange -> changeFlag();
	       goto sStoringSwitchAndCheckingIfStateChangedDriver }
  fi

sCompletingD0ExitDriver:
  // CompleteDStateTransition();
  goto sDxDriver;
  
sStoringSwitchAndCheckingIfStateChangedDriver:
  // StoreSwitchAndEnableSwitchStatusChange();
  if
    :: goto sUpdatingBarGraphStateDriver
    :: goto sWaitingForTimerDriver
  fi
  
sUpdatingBarGraphStateDriver:
  atomic{ SendActionToChannel(_pid, LEDMID, LED,
			      eUpdateBarGraphStateUsingControlTransfer) };

sUpdatingBarGraphStateDriver1:
  flag?true ->
  if
    :: atomic{ OSRD?eD0Entry -> changeFlag();
	       goto sUpdatingBarGraphStateDriver1 }
    :: atomic{ OSRD?eTransferSuccess -> changeFlag();
	       goto sUpdatingLedStateToUnstableDriver }
    :: atomic{ OSRD?eTransferFailure -> changeFlag();
	       goto sUpdatingLedStateToUnstableDriver }
  fi
  
sUpdatingLedStateToUnstableDriver:
  atomic{ SendActionToChannel(_pid, LEDMID, LED,
			      eSetLedStateToStableUsingControlTransfer) };

sUpdatingLedStateToUnstableDriver1:
  flag?true ->
  if
    :: atomic{ OSRD?eD0Entry -> changeFlag();
	       goto sUpdatingLedStateToUnstableDriver1 }
    :: atomic{ OSRD?eTransferSuccess -> changeFlag();
	       goto sWaitingForTimerDriver }
  fi
  
sWaitingForTimerDriver:
  flag?true ->
  if
    :: atomic{ OSRD?eD0Entry -> changeFlag();
	       goto sWaitingForTimerDriver}
    :: atomic{ OSRD?eSwitchStatusChange -> changeFlag();
	       goto sStoppingTimerOnStatusChangeDriver }
    :: atomic{ OSRD?eD0Exit -> changeFlag();
	       goto sStoppingTimerOnD0ExitDriver }
  fi

sUpdatingLedStateToStableDriver:
  atomic{ SendActionToChannel(_pid, LEDMID, LED,
			      eSetLedStateToUnstableUsingControlTransfer) };

sUpdatingLedStateToStableDriver1:
  flag?true ->
  if
    :: atomic{ OSRD?eD0Entry -> changeFlag() }
    :: atomic{ OSRD?eTransferSuccess -> changeFlag();
	       goto sWaitingForSwitchStatusChangeDriver }
  fi
  
sStoppingTimerOnStatusChangeDriver:
  // TBD

sStoppingTimerOnD0ExitDriver:
  // TBD

sStoppingTimerDriver:
  // TBD

sWaitingForTimerToFlushDriver:
  // TBD

sReturningTimerStoppedDriver:
  // TBD
}

active proctype UserMachine() {
  atomic{ run OSRDriverMachine();
	  run LEDMachine();
	  run SwitchMachine();
	  run Pi();
	  flag!false };

S0:
  atomic{ SendActionToChannel(_pid, OSRDID, OSRD, eD0Entry);
	  goto S1 }
  
S1:
  atomic{ SendActionToChannel(_pid, OSRDID, OSRD, eD0Exit);
	  goto S0 }
}

// Pi process
proctype Pi() {
  mtype m;
Receive:
  atomic{ PICHAN?m -> goto Send }
  
Send:
  atomic{ SendAction(_pid, receiver, m) };
}