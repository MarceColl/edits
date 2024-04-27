------------------------------- MODULE edits -------------------------------

EXTENDS Sequences, Naturals

CONSTANT NULL
VARIABLES operations, layer, start_marker, end_marker, patches, id_pool

vars == <<operations, layer, start_marker, end_marker, patches, id_pool>>

Init == /\ operations = 5
        /\ layer = [a |-> [prev |-> NULL, value |-> "START", next |-> "b"], 
                    b |-> [prev |-> "a", value |-> "END", next |-> NULL]]
        /\ start_marker = "a"
        /\ end_marker = "b"
        /\ patches = {}
        /\ id_pool = {"c", "d", "e", "f", "g"}

GeneratePatch == \E target \in (DOMAIN layer \ {end_marker}):
                 \E span_id \in id_pool:
                    /\ operations > 0
                    /\ patches' = patches \union { [ id |-> span_id, targetid |-> target, value |-> "Word" ] }
                    /\ operations' = operations - 1
                    /\ id_pool' = id_pool \ { span_id }
                    /\ UNCHANGED <<layer, start_marker, end_marker>>
                    
ApplyPatch == \E patch \in patches:
                /\ operations > 0
                /\ operations' = operations - 1
                /\ patches' = patches \ { patch }
                \* Typical linked list insertion
                /\ layer' = [layer EXCEPT ![layer[patch.targetid].next].prev = patch.id,
                                          ![patch.targetid].next = patch.id,
                                          ![patch.id] = [prev  |-> patch.targetid, 
                                                         value |-> patch.value, 
                                                         next  |-> layer[patch.targetid].next] ]
                /\ UNCHANGED << start_marker, end_marker, id_pool >>
                 
End == /\ operations = 0
       /\ UNCHANGED vars

Next == \/ GeneratePatch
        \/ ApplyPatch
        \/ End
        
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


=============================================================================
\* Modification History
\* Last modified Sat Apr 27 07:07:38 CEST 2024 by marcecoll
\* Created Fri Apr 05 23:18:28 CEST 2024 by marcecoll
