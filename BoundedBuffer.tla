--------------------------- MODULE BoundedBuffer ---------------------------
EXTENDS Naturals, Sequences, FiniteSets,
        TLC \* for print 
CONSTANTS Messages

(*
--algorithm BoundedBuffer
  variables buffer = <<>>; \* Buffer is a sequence
            capacity = 3;  \* Counting semaphore initial capacity of buffer
            available = 0; \* Counting semaphore messages in buffer
            data = Messages; \* Data set to send
            recieved = {};   \* recieved data-set

  process writer = "w"
  variable message;
  begin
    sending:  \* label needed for while
    while Cardinality(data)>0 do             \* while there are messages to send
    message := CHOOSE m \in data : TRUE;     \* randomly pick an unsent message
    send: await capacity>0;                  \* entry semaphore - while there is space in the buffer
          capacity := capacity - 1;          \* reduce capacity remaining
          buffer := Append(buffer, message); \* put message into buffer
          available := available + 1;        \* mark message available
    data := data \ {message};                \* remove message from data set
    end while;
  end process

  process reader = "r"
  variable message;
  begin
    listening:
    while Cardinality(recieved)<Cardinality(Messages) do \* while messages are to be recieved
    recv: await available>0;               \* wait for message to be available
          available := available - 1;      \* reduce semaphore
          message := Head(buffer);         \* read message
          buffer := Tail(buffer);          \* remove message from buffer
          capacity := capacity + 1;        \* signal on semaphore
    recieved := recieved \union {message}; \* add message to recieved set
    end while;
    print recieved;
  end process
end algorithm
*)
\* BEGIN TRANSLATION
\* Process variable message of process writer at line 15 col 12 changed to message_
CONSTANT defaultInitValue
VARIABLES buffer, capacity, available, data, recieved, pc, message_, message

vars == << buffer, capacity, available, data, recieved, pc, message_, message
        >>

ProcSet == {"w"} \cup {"r"}

Init == (* Global variables *)
        /\ buffer = <<>>
        /\ capacity = 3
        /\ available = 0
        /\ data = Messages
        /\ recieved = {}
        (* Process writer *)
        /\ message_ = defaultInitValue
        (* Process reader *)
        /\ message = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "w" -> "sending"
                                        [] self = "r" -> "listening"]

sending == /\ pc["w"] = "sending"
           /\ IF Cardinality(data)>0
                 THEN /\ message_' = (CHOOSE m \in data : TRUE)
                      /\ pc' = [pc EXCEPT !["w"] = "send"]
                 ELSE /\ pc' = [pc EXCEPT !["w"] = "Done"]
                      /\ UNCHANGED message_
           /\ UNCHANGED << buffer, capacity, available, data, recieved, 
                           message >>

send == /\ pc["w"] = "send"
        /\ capacity>0
        /\ capacity' = capacity - 1
        /\ buffer' = Append(buffer, message_)
        /\ available' = available + 1
        /\ data' = data \ {message_}
        /\ pc' = [pc EXCEPT !["w"] = "sending"]
        /\ UNCHANGED << recieved, message_, message >>

writer == sending \/ send

listening == /\ pc["r"] = "listening"
             /\ IF Cardinality(recieved)<Cardinality(Messages)
                   THEN /\ pc' = [pc EXCEPT !["r"] = "recv"]
                   ELSE /\ PrintT(recieved)
                        /\ pc' = [pc EXCEPT !["r"] = "Done"]
             /\ UNCHANGED << buffer, capacity, available, data, recieved, 
                             message_, message >>

recv == /\ pc["r"] = "recv"
        /\ available>0
        /\ available' = available - 1
        /\ message' = Head(buffer)
        /\ buffer' = Tail(buffer)
        /\ capacity' = capacity + 1
        /\ recieved' = (recieved \union {message'})
        /\ pc' = [pc EXCEPT !["r"] = "listening"]
        /\ UNCHANGED << data, message_ >>

reader == listening \/ recv

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(* Some invariants to check *)
BufferSize == Len(buffer)\leq 3
SemaphoreSend == capacity  \in 0..3
SemaphoreRecv == available \in 0..3 
DataSet == data \in SUBSET Messages
RecievedSet == recieved \in SUBSET Messages
=============================================================================
\* Modification History
\* Last modified Mon Oct 21 22:38:12 BST 2019 by alun
\* Created Mon Oct 21 21:27:12 BST 2019 by alun
