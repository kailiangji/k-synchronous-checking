/*OSR*/

#define K 2

mtype = { eD0Entry,
	  eD0Exit,
	  eTimerFired,
	  eSwitchStatusChange,
	  eTransferSuccess,
	  eTransferFailure,
	  eStopTimer,
	  eUpdateBarGraphStateUsingControlTransfer,
	  eSetLedStateToUnstableUsingControlTransfer,
	  eStartDebounceTimer,
	  eSetLedStateToStableUsingControlTransfer,
	  eStoppingSuccess,
	  eStoppingFailure,
	  eOperationSuccess,
	  eOperationFailure,
	  eTimerStopped,
	  eYes,
	  eNo,
	  eUnit };

chan UM = [K] of { mtype };
chan OSRD = [K] of { mtype };
chan SM = [K] of { mtype };
chan LED = [K] of { mtype };

proctype SwitchMachine() {

ChangeSwitchStatus:
  OSRD!eSwitchStatusChange;
  goto ChangeSwitchStatus
}

proctype LEDMachine() {

LED_Init:
  if
    :: LED?eUpdateBarGraphStateUsingControlTransfer ->
       goto ProcessUpdateLED
    :: LED?eSetLedStateToUnstableUsingControlTransfer ->
       goto UnstableLED
    :: LED?eSetLedStateToStableUsingControlTransfer ->
       goto StableLED
  fi

ProcessUpdateLED:
  if
    :: OSRD!eTransferSuccess
    :: OSRD!eTransferFailure
  fi
  goto LED_Init

UnstableLED:
  OSRD!eTransferSuccess

  if
    :: LED?eSetLedStateToStableUsingControlTransfer ->
       goto LED_Init
    :: LED?eUpdateBarGraphStateUsingControlTransfer ->
       goto ProcessUpdateLED
  fi

StableLED:
  OSRD!eTransferSuccess;
  goto LED_Init
}

proctype OSRDriverMachine() {

sDxDriver: 
  do
    :: OSRD?eD0Exit -> skip
    :: OSRD?eD0Entry -> goto sCompleteD0EntryDriver
  od
  
sCompleteD0EntryDriver:
  /* CompleteDStateTransition(); */
  goto  sWaitingForSwitchStatusChangeDriver;

sWaitingForSwitchStatusChangeDriver:
  do
    :: OSRD?eD0Entry -> skip;
    :: OSRD?eD0Exit -> goto sCompletingD0ExitDriver
    :: OSRD?eSwitchStatusChange -> goto sStoringSwitchAndCheckingIfStateChangedDriver
  od

sCompletingD0ExitDriver:
  /* CompleteDStateTransition(); */
  goto sDxDriver;

sStoringSwitchAndCheckingIfStateChangedDriver:
  /* StoreSwitchAndEnableSwitchStatusChange(); */
  if
    :: goto sUpdatingBarGraphStateDriver
    :: goto sWaitingForTimerDriver
  fi

sUpdatingBarGraphStateDriver:
  LED!eUpdateBarGraphStateUsingControlTransfer;
 
  do
    :: OSRD?eD0Entry -> skip;
    :: OSRD?eTransferSuccess -> goto sUpdatingLedStateToUnstableDriver
    :: OSRD?eTransferFailure -> goto sUpdatingLedStateToUnstableDriver
  od
  
sUpdatingLedStateToUnstableDriver:
  LED!eSetLedStateToStableUsingControlTransfer;
 
  do
    :: OSRD?eD0Entry -> skip
    :: OSRD?eTransferSuccess -> goto sWaitingForTimerDriver
  od

sWaitingForTimerDriver:
  do
    :: OSRD?eD0Entry -> skip
    :: OSRD?eSwitchStatusChange -> goto sStoppingTimerOnStatusChangeDriver
    :: OSRD?eD0Exit -> goto sStoppingTimerOnD0ExitDriver
  od

sUpdatingLedStateToStableDriver:
  LED!eSetLedStateToUnstableUsingControlTransfer;

  do
    :: OSRD?eD0Entry -> skip
    :: OSRD?eTransferSuccess -> goto sWaitingForSwitchStatusChangeDriver
  od

sStoppingTimerOnStatusChangeDriver:
  /* TBD */

sStoppingTimerOnD0ExitDriver:
  /* TBD */

sStoppingTimerDriver:
  /* TBD */

sWaitingForTimerToFlushDriver:
  /* TBD */

sReturningTimerStoppedDriver:
  /* TBD */
}

active proctype UserMachine() {
  run OSRDriverMachine(); run LEDMachine(); run SwitchMachine();
S0:
  OSRD!eD0Entry; 
  goto S1
  
S1:
  OSRD!eD0Exit; 
  goto S0
}