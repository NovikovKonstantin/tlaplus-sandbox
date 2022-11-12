------------------------------ MODULE scratch ------------------------------

EXTENDS Sequences, Naturals

ValueInteger == 10
ValueString == "Text value"

Or(A,B) == A \/ B
And(A,B) == A /\ B
Not(A) == ~A
Implication1(A,B) == Or(~A,B)
Implication2(A,B) == A => B

(* A or B or (A and (A or B)) or C*)    
Expr1(A,B,C) == \/ A
                \/ B
                \/ /\ A
                   /\ \/ A
                      \/ B
                \/ C

ValueSequence == <<1,2,3>>
ValueSet == {"a", "b", "c", "d"}
IsInValueSet(A) == A \in ValueSet
IsNotInValueSet(A) == A \notin ValueSet

(* Map: {[operation]:[values]} *)
Squares == {x*x: x \in 1..4}

(* Filter: {[values]:[condition]} *)
Even == {x \in 1..4: x%2 = 0}

(* All possible combinations of HH:MM:SS*)
ClockType == (0..23) \X (0..59) \X (0..59)

(* Operator LET can be used to make inline function *)
ThreeMax(a, b, c) ==
   LET
     Max(x, y) == IF x > y THEN x ELSE y
   IN
     Max(Max(a, b), c)
=============================================================================
