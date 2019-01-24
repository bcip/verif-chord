Require Import Coq.omega.Omega.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Node.

(** STATE STRUCTURE AND PARAMETERS *)

Inductive Status : Type :=
  | Stabilizing : Status
  | Rectifying : Status.

Inductive adjacent {A} : A -> A -> list A -> Prop :=
  | adj_hd : forall (j k : A) (l : list A),
               head l = Some j ->
               head (tl l) = Some k ->
               adjacent j k l
  | adj_tl : forall (j k : A) (l : list A),
               head l <> None ->
               adjacent j k (tl l) ->
               adjacent j k l.

(* NetState *)
Record NetState : Type := mkNetState
  {
    members: set Node;
    succlength : nat;
    succ : Node -> list Node;
    prdc : Node -> Node;
    status : Node -> Status
  }.

(* Invariant *)
Definition WellFormedNetState (s : NetState) : Prop :=
  NoDup (members s) /\
  succlength s > 0 /\
  forall (n : Node), set_In n (members s) -> length (succ s n) = succlength s.

Definition LiveSuccCondition (s : NetState) : Prop :=
  forall (n : Node), set_In n (members s) ->
    Exists (fun m => set_In m (members s)) (succ s n).

Definition Principal (s : NetState) (p : Node) : Prop :=
  forall n, set_In n (members s) ->
    forall j k : Node, adjacent j k (n :: (succ s n)) ->
    ~ (between j p k).

Definition SufficientPrincipals (s : NetState) : Prop :=
  exists (principals : set Node),
    length principals >= succlength s + 1 /\
    NoDup principals /\
    (forall (p : Node), set_In p principals ->
      set_In p (members s) /\
      Principal s p).

Definition Invariant (s : NetState) : Prop :=
  WellFormedNetState s /\ LiveSuccCondition s /\ SufficientPrincipals s.



