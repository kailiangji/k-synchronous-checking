/* German */

#define N 5
#define K 2

mtype = { req_share, req_excl, need_invalidate, invalidate_ack, grant,
	  ask_share, ask_excl, invalidate, grant_excl, grant_share,
	  normal, wait, invalidate_sharers, sharer_id };

chan H = [K] of { mtype, pid };
chan C1 = [K] of { mtype, pid };
chan C2 = [K] of { mtype, pid };
chan C3 = [K] of { mtype, pid };
//chan CPUCh = [K] of { mtype };
chan sharer_list = [N] of { pid };

active proctype Host() {
  pid curr_client;
  pid clients[3];
//  pid curr_cpu;
  bool is_curr_req_excl;
  bool is_excl_granted;
  byte i, s;
  pid temp;
  clients[0] = run Client1();
  clients[1] = run Client2();
  clients[2] = run Client3();
  curr_client = N;
  //  curr_cpu = run CPU();
  run CPU();
  assert(len(sharer_list) == 0);
  goto ReceiveState;

ReceiveState:
  if
    :: H?req_share,curr_client -> goto ShareRequest
    :: H?req_excl,curr_client -> goto ExclRequest
  fi
  
ShareRequest:
  is_curr_req_excl = false;
  goto ProcessReq;
  
ExclRequest:
  is_curr_req_excl = true;
  goto ProcessReq;
  
ProcessReq:
  if
    :: is_curr_req_excl || is_excl_granted -> goto Inv
    :: else -> goto GrantAccess
  fi
  
Inv:
  i = 0;
  if
    :: empty(sharer_list) ->
       goto GrantAccess
    :: nempty(sharer_list) ->
       s = len(sharer_list);
       do
	 :: i < s ->
	    sharer_list?temp ->
	    if
	      :: temp == clients[0] -> C1!invalidate,_pid
	      :: temp == clients[1] -> C2!invalidate,_pid
	      :: temp == clients[2] -> C3!invalidate,_pid
	    fi
	    i++;
	    sharer_list!temp
	 :: i >= s -> break
       od
  fi

  if
    :: H?invalidate_ack,_ ->
       /* do rec_ack */
       sharer_list?_ ->
       if
	 :: empty(sharer_list) -> goto GrantAccess
	 :: nempty(sharer_list) -> skip
       fi
    :: H?grant,_ -> goto GrantAccess
  fi

GrantAccess:
  if
    :: is_curr_req_excl ->
       is_excl_granted = true;
       if
	 :: curr_client == clients[0] -> C1!grant_excl,_pid
	 :: curr_client == clients[1] -> C2!grant_excl,_pid
	 :: curr_client == clients[2] -> C3!grant_excl,_pid
       fi
    :: !is_curr_req_excl ->
       if
	 :: curr_client == clients[0] -> C1!grant_share,_pid
	 :: curr_client == clients[1] -> C2!grant_share,_pid
	 :: curr_client == clients[2] -> C3!grant_share,_pid
       fi
  fi
  sharer_list!curr_client; goto ReceiveState
}

proctype Client1() {
  bool pending;

Start:
  pending = false;
  goto Invalid;
  
Invalid:
  if
    :: C1?ask_share,_ -> goto Asked_share;
    :: C1?ask_excl,_ -> goto Asked_excl;
    :: C1?invalidate,_ -> goto Invalidating;
    :: C1?grant_excl,_ -> goto Exclusive;
    :: C1?grant_share,_ -> goto Sharing;
  fi

Asked_share:
  H!req_share,_pid;
  pending = true;
  goto Invalid_wait;
  
Asked_excl:
  H!req_excl,_pid;
  pending = true;
  goto Invalid_wait;
  
Invalid_wait:
  if
    :: C1?invalidate,_ -> goto Invalidating
    :: C1?grant_excl,_ -> goto Exclusive
    :: C1?grant_share,_ -> goto Sharing
  fi
  
Asked_ex2:
  H!req_excl,_pid;
  pending = true;
  goto Sharing_wait;
  
Sharing:
  pending = false;
  if
    :: C1?invalidate,_ -> goto Invalidating
    :: C1?grant_share,_ -> goto Sharing
    :: C1?grant_excl,_ -> goto Exclusive
    :: C1?ask_share,_ -> goto Sharing
    :: C1?ask_excl,_ -> goto Asked_ex2
  fi
  
Sharing_wait:
  if
    :: C1?invalidate -> goto Invalidating
    :: C1?grant_share -> goto Sharing_wait
    :: C1?grant_excl -> goto Exclusive
  fi
  
Exclusive:
  pending = false;
  do
    :: C1?ask_share,_ -> skip
    :: C1?ask_excl,_ -> skip
    :: C1?invalidate,_ -> goto Invalidating
    :: C1?grant_share,_ -> goto Sharing_wait
    :: C1?grant_excl,_ -> goto Exclusive
  od
  
Invalidating:
  H!invalidate,_pid;
  if
    :: pending -> goto Invalid_wait
    :: !pending -> goto Invalid
  fi
}

proctype Client2() {
  bool pending;

Start:
  pending = false;
  goto Invalid;
  
Invalid:
  if
    :: C2?ask_share,_ -> goto Asked_share;
    :: C2?ask_excl,_ -> goto Asked_excl;
    :: C2?invalidate,_ -> goto Invalidating;
    :: C2?grant_excl,_ -> goto Exclusive;
    :: C2?grant_share,_ -> goto Sharing;
  fi

Asked_share:
  H!req_share,_pid;
  pending = true;
  goto Invalid_wait;
  
Asked_excl:
  H!req_excl,_pid;
  pending = true;
  goto Invalid_wait;
  
Invalid_wait:
  if
    :: C2?invalidate,_ -> goto Invalidating
    :: C2?grant_excl,_ -> goto Exclusive
    :: C2?grant_share,_ -> goto Sharing
  fi
  
Asked_ex2:
  H!req_excl,_pid;
  pending = true;
  goto Sharing_wait;
  
Sharing:
  pending = false;
  if
    :: C2?invalidate,_ -> goto Invalidating
    :: C2?grant_share,_ -> goto Sharing
    :: C2?grant_excl,_ -> goto Exclusive
    :: C2?ask_share,_ -> goto Sharing
    :: C2?ask_excl,_ -> goto Asked_ex2
  fi
  
Sharing_wait:
  if
    :: C2?invalidate -> goto Invalidating
    :: C2?grant_share ->  goto Sharing_wait
    :: C2?grant_excl ->  goto Exclusive
  fi

Exclusive:
  pending = false;
  do
    :: C2?ask_share,_ -> skip
    :: C2?ask_excl,_ -> skip
    :: C2?invalidate,_ -> goto Invalidating
    :: C2?grant_share,_ -> goto Sharing_wait
    :: C2?grant_excl,_ -> goto Exclusive
  od
  
Invalidating:
  H!invalidate,_pid;
  if
    :: pending -> goto Invalid_wait
    :: !pending -> goto Invalid
  fi
}

proctype Client3() {
  bool pending;
  
Start:
  pending = false;
  goto Invalid;
  
Invalid:
  if
    :: C3?ask_share,_ -> goto Asked_share;
    :: C3?ask_excl,_ -> goto Asked_excl;
    :: C3?invalidate,_ -> goto Invalidating;
    :: C3?grant_excl,_ -> goto Exclusive;
    :: C3?grant_share,_ -> goto Sharing;
  fi

Asked_share:
  H!req_share,_pid;
  pending = true;
  goto Invalid_wait;
  
Asked_excl:
  H!req_excl,_pid;
  pending = true;
  goto Invalid_wait;
  
Invalid_wait:
  if
    :: C3?invalidate,_ -> goto Invalidating
    :: C3?grant_excl,_ -> goto Exclusive
    :: C3?grant_share,_ -> goto Sharing
  fi
  
Asked_ex2:
  H!req_excl,_pid;
  pending = true;
  goto Sharing_wait;
  
Sharing:
  pending = false;
  if
    :: C3?invalidate,_ -> goto Invalidating
    :: C3?grant_share,_ -> goto Sharing
    :: C3?grant_excl,_ -> goto Exclusive
    :: C3?ask_share,_ -> goto Sharing
    :: C3?ask_excl,_ -> goto Asked_ex2
  fi  
  
Sharing_wait:
  if
    :: C3?invalidate -> goto Invalidating
    :: C3?grant_share -> goto Sharing_wait
    :: C3?grant_excl -> goto Exclusive
  fi
  
Exclusive:
  pending = false;
  do
    :: C3?ask_share,_ -> skip
    :: C3?ask_excl,_ -> skip
    :: C3?invalidate,_ -> goto Invalidating
    :: C3?grant_share,_ -> goto Sharing_wait
    :: C3?grant_excl,_ -> goto Exclusive
  od
  
Invalidating:
  H!invalidate,_pid;
  if
    :: pending -> goto Invalid_wait
    :: !pending -> goto Invalid
  fi
}

proctype CPU() {

MakeReq:
  if
    :: C1!ask_share,_pid; goto MakeReq
    :: C1!ask_excl,_pid; goto MakeReq
    :: C2!ask_share,_pid; goto MakeReq
    :: C2!ask_excl,_pid; goto MakeReq
    :: C3!ask_share,_pid; goto MakeReq
    :: C3!ask_excl,_pid; goto MakeReq
  fi
}