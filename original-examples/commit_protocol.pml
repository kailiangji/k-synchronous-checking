// Commit Protocol

mtype = { update, OK };
chan M = [1] of { mtype };
chan C = [1] of { mtype };
chan N1 = [1] of { mtype };
chan N2 = [1] of { mtype };

/* Manager process */
active proctype Manager() {
  goto Start;
  
Start:
  M?update -> goto Send1 

Send1:
  N1!update;
  goto Send2

Send2:
  N2!update;
  goto Rec1

Rec1:
  M?OK -> goto Rec2 

Rec2:
  M?OK -> goto Rec3

Rec3:
  C!OK;
  goto Start
}

/* The Client process */
active proctype Client() {
  goto Send;

Send:
  M!update;
  goto Ack

Ack:
  C?OK -> goto Send
}

/* Node n1 */
active proctype Node1() {
  goto Send;
  
Send:
  N1?update -> goto Ack
  
Ack:
  M!OK;
  goto Send
}

/* Node n2 */
active proctype Node2() {
  goto Send;
  
Send:
  N2?update -> goto Ack 
  
Ack:
  M!OK;
  goto Send
}