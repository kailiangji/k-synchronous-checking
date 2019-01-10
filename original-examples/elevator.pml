/* Elevator */

mtype = { openDoor, closeDoor, reset, stop, open, close,
	  doorOpened, doorClosed, doorStopped };

chan E = [1] of { mtype }; /* elevator channel */
chan D = [1] of { mtype }; /* door channel */

/* Elevator process */
proctype Elevator()
{
  goto Closed1
  
Closed1:
  D!reset; goto Closed2
  
Closed2:
  if
    :: E?closeDoor ->  goto Closed2
    :: E?openDoor -> goto Opening1
  fi 
    
Opening1:
  D!open; goto Opening2   
  
Opening2:
  E?doorOpened -> goto Opened
  
Opened:
 D!reset; goto Closing1 

Closing1:
  D!close; goto Closing2
  
Closing2:
  if
    :: E?doorClosed ->  goto Closed1
    :: E?openDoor ->  goto Stopping1
  fi 
  
Stopping1:
  D!stop;  goto Stopping2 
  
Stopping2:
  if
    :: E?openDoor -> goto Stopping2
    :: E?doorClosed -> goto Closed1
    :: E?doorStopped -> goto Opening2
  fi 
}

/* Door process */
proctype Door()
{
  goto Start;
  
Start:
  if
    :: D?reset -> goto Start 
    :: D?stop -> goto Start
    :: D?open ->  goto OpenDoor
    :: D?close -> goto Closing
  fi 
  
OpenDoor:
  E!doorOpened; goto ResetDoor
  
ResetDoor:
  if
    :: D?open -> goto ResetDoor
    :: D?close ->  goto ResetDoor
    /* :: D?stop -> goto ResetDoor */
    :: D?reset ->  goto Start
  fi 
  
StopDoor:
  E!doorStopped; goto OpenDoor
  
Closing:
  if
    :: D?stop -> goto StopDoor
    :: E!doorClosed; goto ResetDoor
  fi  
}

/* User process */
active proctype User() {
  run Elevator();
  run Door();
  goto Loop; 
  
Loop:
  if
    :: E!openDoor;
    :: E!closeDoor; 
  fi
  goto Loop
}
