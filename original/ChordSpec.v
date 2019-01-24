Require Import Coq.omega.Omega.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.

(** Nodes *)

Inductive Node : Type :=
  N : nat -> Node.

Definition LT (n1: Node) (n2 : Node) :=
  match (n1, n2) with
    (N id1, N id2) => id1 < id2
  end.

Definition LTE (n1: Node) (n2 : Node) :=
  n1 = n2 \/ LT n1 n2.

Theorem cmp_dec : forall x y : Node,
  {x = y} + {x <> y}.
Proof.
  intros.
  destruct x as [xn]. destruct y as [yn].
  destruct (xn =? yn) eqn:Eq.
  - left. rewrite Nat.eqb_eq in Eq. auto.
  - right. unfold not. intros.
    inversion H.
    assert (H': xn <> yn). { apply beq_nat_false. auto. }
    auto.
Qed.

(* List operations *)
Fixpoint take' {A} (l taken : list A) (n : nat) : list A :=
  match (l, n) with
  | (nil, _) => taken
  | (_, O) => taken
  | (h :: t, S n') => take' t ( h::taken ) (n')
  end.

Definition take {A} (l : list A) (n : nat) : list A :=
  take' l nil n.

(** THEOREMS ABOUT IDENTIFIER SPACES *)
Inductive between : Node -> Node -> Node -> Prop :=
  | Between :
      forall n1 nb n2,
        LT n1 n2 -> LT n1 nb -> LT nb n2 ->
        between n1 nb n2
  | Between_cycle :
      forall n1 nb n2,
        ~(LT n1 n2) -> (LT n1 nb) \/ (LT nb n2) ->
        between n1 nb n2.

Theorem AnyBetweenAny :
  forall (n1 n2 : Node), n1 <> n2 -> between n1 n2 n1.
Proof.
  intros. destruct n1 as [id1]. destruct n2 as [id2].
  apply Between_cycle.
  - unfold not.
    intros. unfold LT in H0.
    omega.
  - assert (H' : id1 <> id2).
    { unfold not. intros. auto. }
    assert (H'' : id1 < id2 \/ id2 < id1).
    { omega. }
    destruct H''.
    + left. unfold LT. auto.
    + right. unfold LT. auto.
Qed.

Inductive includedIn : Node -> Node -> Node -> Prop :=
  | Included :
      forall n1 nb n2,
        LT n1 n2 -> LTE n1 nb -> LTE nb n2 ->
        includedIn n1 nb n2
  | Included_cycle :
      forall n1 nb n2,
        ~(LT n1 n2) -> LTE n1 nb \/ LTE nb n2 ->
        includedIn n1 nb n2.

Theorem AnyIncludedInAny :
  forall (n1 n2 : Node), includedIn n1 n2 n1.
Proof.
  intros. destruct n1 as [id1]. destruct n2 as [id2].
  apply Included_cycle.
  - unfold not.
    intros. unfold LT in H.
    omega.
  - assert (H'' : id1 <= id2 \/ id2 <= id1).
    { omega. }
    destruct H''.
    + destruct H; left; unfold LTE; unfold LT; auto; right; omega.
    + destruct H; right; unfold LTE; unfold LT; auto; right; omega.
Qed.

Theorem Untitled :
  forall (n1 nb n2 : Node),
    includedIn n1 nb n2 <->
      ( between n1 nb n2 \/
        n1 = nb \/ nb = n2 ).
Proof.
  split; intros.
  - inversion H.
    + (* Included *)
      subst. inversion H1.
      * (* n = n0 *) right. left. auto.
      * (* n < n0 *) inversion H2.
        { (* n0 = n1 *) right. right. auto. }
        { (* n0 < n1 *) left. apply Between; auto. }
    + (* Included_cycle *)
      subst. destruct H1.
      * (* n < n0 *) inversion H1.
        { (* n = n0 *) right. left. auto. }
        { (* n < n0 *) left. apply Between_cycle; auto. }
      * (* n0 < n1 *) inversion H1.
        { (* n0 = n1 *) right. right. auto. }
        { (* n < n0 *) left. apply Between_cycle; auto. }
  - (* Included_cycle *)
    inversion H.
    + (* between n1 nb n2 *)
      inversion H0.
      * (* Between *) subst.
        assert (LTE n1 nb) by (unfold LTE; right; auto).
        assert (LTE nb n2) by (unfold LTE; right; auto).
        apply Included; auto.
      * (* Between_cycle *) subst.
        assert (LTE n1 nb \/ LTE nb n2).
          { unfold LTE; inversion H2.
            - left; right; auto.
            - right; right; auto. }
        apply Included_cycle; auto.
   + inversion H0.
     * (* n1 = nb *)
       rewrite H1 in *.
       destruct nb as [nbn]. destruct n2 as [n2n].
       destruct (nbn <? n2n) eqn:Less.
       { rewrite Nat.ltb_lt in Less.
         apply Included; auto. left; auto. right; auto. }
       { rewrite Nat.ltb_nlt in Less.
         apply Included_cycle; auto; left; auto; left; auto. }
    * (* nb = nb *)
      rewrite H1 in *.
      destruct n1 as [n1n]. destruct n2 as [n2n].
      destruct (n1n <? n2n) eqn:Less.
      { rewrite Nat.ltb_lt in Less.
        apply Included; auto. right; auto. left; auto. }
       { rewrite Nat.ltb_nlt in Less.
         apply Included_cycle; auto. right. left; auto. }
Qed.

Theorem IncludedReversesBetween :
  forall (n1 nb n2 : Node),
    n1 <> n2 ->
    ( ~ (between n1 nb n2) <-> includedIn n2 nb n1).
Admitted.

Theorem ChainedIntervals :
  forall (n1 n2 n3 nb : Node),
    n1 <> n2 -> n2 <> n3 -> n1 <> n3 ->
    includedIn n1 nb n2 /\ includedIn n2 nb n3 -> n2 = n3.
Admitted.

Theorem LocationOfUnskippedNode :
  forall (n1 n2 n3 nb : Node),
    n1 <> n2 -> n2 <> n3 -> n1 <> n3 ->
    ~ between n1 nb n2 /\ ~ between n2 nb n3 ->
    nb = n1 \/ nb = n2 \/ nb = n3 \/ between n3 nb n1.
Admitted.

(** STATE STRUCTURE AND PARAMETERS *)

Inductive Status : Type :=
  | Stabilizing : Status
  | Rectifying : Status.

Inductive SubSetNodeType : set Node -> Type :=
  | ss : forall (nodes nodes' : set Node) (n : Node),
         (set_In n nodes' -> set_In n nodes)
         -> SubSetNodeType nodes.

Definition proj1_sig_opt {T} {P} (x : option { x : T | P (x) }) :=
  match x with
  | None => None
  | Some x' => Some (proj1_sig x')
  end.

Inductive adjacent {A} : A -> A -> list A -> Prop :=
  | adj_hd : forall (j k : A) (l : list A),
               head l = Some j ->
               head (tl l) = Some k ->
               adjacent j k l
  | adj_tl : forall (j k : A) (l : list A),
               head l <> Some j ->
               head l <> None ->
               adjacent j k (tl l) ->
               adjacent j k l.

Definition Time := nat.

Definition next (t : Time) : Time := t + 1.

(* NetState *)
Record NetState : Type := mkNetState
  { time : Time;
    members: set Node;
    succlength : nat;
    succ : Node -> list Node;
    prdc : Node -> Node;
    status : Node -> option Status;
    saved : Node -> option Node;
    bestSucc : Node -> option Node;
    principals : set Node
  }.

(* Range restrictions *)
Definition SuccCondition (s : NetState) : Prop :=
  succlength s > 0 /\ forall (m : Node), set_In m (members s) -> length (succ s m) = succlength s.

Definition BestSuccCondition (s : NetState) : Prop :=
  forall (m n : Node), set_In m (members s) -> (bestSucc s m) = Some n -> set_In n (members s).

Definition PrincipalsCondition (s : NetState) : Prop :=
  forall (m : Node), set_In m (principals s) -> set_In m (members s).

(* Conditions *)
(* a member has a saved node if and only if it has a status *)
Definition SavedNodeStatus (s : NetState) : Prop :=
  forall (m : Node), set_In m (members s) -> (status s m = None <-> saved s m = None).

(* bestSucc is derived from successor lists; a member's bestSucc is its
   first live successor, if any.*)
Definition NoBestSucc (s : NetState) : Prop :=
  forall (m : Node),
    set_In m (members s) ->
    (set_inter cmp_dec (succ s m) (members s) = empty_set Node ->
    bestSucc s m = None).

Definition BestSuccFirst (s : NetState) : Prop :=
  forall (m : Node),
    set_In m (members s) ->
      (set_inter cmp_dec (succ s m) (members s) <> empty_set Node ->
      bestSucc s m = head (filter (fun x => set_mem cmp_dec x (members s)) (succ s m))).

(* A member is a principal member iff, for all other members,
   it is not skipped by any adjacent pair in that other member's extended
   successor list. *)
Definition Principals (s : NetState) : Prop :=
  forall (p : Node),
   (forall m, set_In m (members s) ->
     (forall j k : Node, adjacent j k (m :: (succ s m)) ->
      ~ (between j p k))) <->
    set_In p (principals s).

Definition DefaultStatus (s : NetState) : Prop :=
  forall (n : Node), ~ set_In n (members s) -> status s n = None.

Definition DefaultSaved (s : NetState) : Prop :=
  forall (n : Node), ~ set_In n (members s) -> saved s n = None.

Definition NetStateVariant (s : NetState) : Prop :=
  forall (s' : NetState), s' <> s -> time s' <> time s.

Definition WellFormedNetState (s : NetState) : Prop :=
  SuccCondition s /\ BestSuccCondition s /\ PrincipalsCondition s /\
  SavedNodeStatus s /\ NoBestSucc s /\ BestSuccFirst s /\ Principals s /\
  NoDup (members s) /\ NoDup (principals s) /\ DefaultStatus s /\ DefaultSaved s /\
  NetStateVariant s.

(** PROPERTIES OF NETWORK STATES *)

Definition Invariant (s : NetState) : Prop :=
  WellFormedNetState s /\
  (* one live successor *)
  (forall (n : Node), set_In n (members s) -> s.(bestSucc) n <> None) /\
  (* base of principals *)
  (length (principals s) >= succlength s + 1).

Definition OrderedSuccessorLists (s : NetState) : Prop :=
  WellFormedNetState s ->
  forall (m : Node) (j k l : nat),
    set_In m (members s) ->
    (k < succlength s -> j < k ->
      between m
      (nth j (succ s m) m)
      (nth k (succ s m) m)) /\
      (l < succlength s -> j < k -> k < l ->
      between
      (nth j (succ s m) m)
      (nth k (succ s m) m)
      (nth l (succ s m) m)).

Theorem InvariantEnsuresOrderedSuccessorLists :
  forall (s : NetState), Invariant s -> OrderedSuccessorLists s.
Admitted.

Definition NoDuplicates (s : NetState) : Prop :=
  WellFormedNetState s ->
  forall m : Node,
    set_In m (members s) ->
    (~ (set_In m (succ s m)) /\
    NoDup (succ s m)).

Theorem InvariantEnsuresNoDuplicates :
  forall (s : NetState), Invariant s -> NoDuplicates s.
Admitted.

(* A ring member is a network member that can be reached by
  following the chain of best successors beginning at itself. *)
Inductive CanReach : NetState -> Node -> Node -> Prop :=
  | reach_self : forall (s : NetState) (m m' : Node),
                 set_In m (members s) -> set_In m' (members s) ->
                 bestSucc s m = Some m' ->
                 CanReach s m m'
  | reach_other : forall (s : NetState) (m m' m'' : Node),
                  set_In m (members s) -> set_In m' (members s) -> set_In m'' (members s) ->
                  bestSucc s m = Some m' ->
                  CanReach s m' m'' ->
                  CanReach s m m''.

Definition IsRingMember (s : NetState) (m : Node) : Prop :=
  CanReach s m m.

Definition PrincipalsAreRingMembers (s : NetState) : Prop :=
  WellFormedNetState s ->
  forall p : Node,
    set_In p (members s) ->
    set_In p (principals s) ->
    IsRingMember s p.

Theorem InvariantEnsuresPrincipalsInRing :
  forall (s : NetState), Invariant s -> PrincipalsAreRingMembers s.
Admitted.

Definition OneOrderedRing (s : NetState) : Prop :=
  WellFormedNetState s ->
  (* at least one ring *)
  (exists (m : Node), IsRingMember s m) /\
  (* at most one ring *)
  (forall (m m' : Node),
     IsRingMember s m -> IsRingMember s m' ->
     CanReach s m m') /\
  (* ordered ring *)
  (forall (m m1 m2 mb: Node),
     set_In m (members s) ->
     m1 = m ->
     IsRingMember s m1 -> IsRingMember s m2 -> IsRingMember s mb ->
     m1 <> m2 -> m2 <> mb -> m1 <> mb ->
     Some m2 = bestSucc s m -> ~ (between m1 mb m2)).

Theorem InvariantEnsuresOneOrderedRing :
  forall (s : NetState), Invariant s -> OneOrderedRing s.
Admitted.

Definition ConnectedAppendages (s : NetState) : Prop :=
  WellFormedNetState s ->
  forall (m : Node),
    set_In m (members s) ->
    ~ (IsRingMember s m) ->
    exists (m' : Node), IsRingMember s m' /\ CanReach s m m'.

Theorem InvariantEnsuresConnectedAppendages :
  forall (s : NetState), Invariant s -> ConnectedAppendages s.
Admitted.

(* The Ideal definition is based off of the definition in the paper
   rather than the one in the Alloy model *)
Definition Ideal (s : NetState) : Prop :=
  (* Every pointer points to a live node *)
  (forall (m n : Node), set_In m (members s) ->
     In n (succ s m) -> set_In n (members s)) /\
  (* Every successor pointer is its node's first successor in
     identifier order *)
  (forall (m n p: Node), set_In m (members s) ->
      Some n = bestSucc s m -> between m n p) /\
  (* Every predecessor pointer is its node's first predecessor in
     identifier order *)
  (forall (m1 m2 : Node),
     set_In m1 (members s) -> set_In m2 (members s) ->
     head (succ s m1) = Some m2 <-> prdc s m2 = m1) /\
  (* the tail of the successor list of a node is the
     successor\u2019s successor list, with the last entry removed *)
  (forall (m sn: Node),
   set_In m (members s) -> set_In sn (members s) ->
   Some sn = bestSucc s m ->
   tail (succ s m) = take (succ s sn) (succlength s - 1)).

(** STATE TRANSITIONS *)
Definition Fail (s s' : NetState) (f : Node) : Prop :=
  (* PRECONDITIONS *)
  WellFormedNetState s /\
  set_In f (members s) /\
  (* A member cannot fail if it would leave another member with no live
     successor *)
  ((forall (m : Node),
     set_In m (members s) -> m <> f -> (* m : s.members - f *)
     set_In f (succ s m) ->
     exists (m' : Node), set_In m' (members s) /\ m' <> f /\ (* m': s.members - f*)
     set_In m' (succ s m)) /\
  (* A principal member cannot fail if the number of principals is the
     base size or less *)
  (set_In f (principals s) -> length (principals s) > succlength s + 1)) /\
  (* POSTCONDITIONS *)
  WellFormedNetState s' /\
  succlength s' = succlength s /\
  time s' = next (time s) /\
  members s' = set_remove cmp_dec f (members s) /\
  (forall (m : Node), set_In m (members s') -> succ s' m = succ s m) /\
  (forall (m : Node), set_In m (members s') -> prdc s' m = prdc s m) /\
  (forall (m : Node), set_In m (members s') -> status s' m = status s m) /\
  (forall (m : Node), set_In m (members s') -> saved s' m = saved s m).

(* Proving that Fail preserves the Invariant: *)
Lemma set_remove_nothing (A : Type) (Aeq_dec: forall x y:A, {x = y} + {x <> y}) (a : A) (l : set A) :
   ~(In a l) -> (set_remove Aeq_dec a l) = l.
Proof.
  induction l; intros.
  - reflexivity.
  - unfold not in H.
    assert (a <> a0). { unfold not. intros. subst. apply H. constructor. reflexivity. }
    assert (~ In a l). { unfold not. intros. apply H. right. auto. }
    destruct (Aeq_dec a a0) eqn:Eq.
    + subst. unfold not in H0. exfalso. auto.
    + simpl. rewrite Eq. apply IHl in H1. rewrite H1. reflexivity.
Qed.

(* The following two lemmas are actually here: https://coq.inria.fr/library/Coq.Lists.ListSet.html *)
Lemma set_remove_iff (A : Type) (Aeq_dec: forall x y:A, {x = y} + {x <> y}) (a b : A) (l : set A) :
   NoDup l -> (In a (set_remove Aeq_dec b l) <-> In a l /\ a <> b).
Proof.
induction l; intros.
  - simpl. split; intros; auto. destruct H0; auto.
  - split; intros.
    + split.
      * inversion H.
        { destruct (Aeq_dec a a0).
          - subst. left. reflexivity.
          - destruct (Aeq_dec b a0) eqn:Eq.
            + unfold set_remove in H0. rewrite Eq in H0. right. auto.
            + apply IHl in H4.
              * unfold set_remove in H0. rewrite Eq in H0.
                assert (((fix set_remove (a : A) (x : set A) {struct x} : set A :=
                           match x with
                           | nil => empty_set A
                           | a1 :: x1 => if Aeq_dec a a1 then x1 else a1 :: set_remove a x1
                          end) b l) = set_remove Aeq_dec b l) by auto.
                rewrite H5 in *. inversion H0.
                { exfalso. apply n. auto. }
                { right. apply H4. auto. } }
      * inversion H. unfold not. intros. rewrite H5 in *. clear H5. clear H1. clear H2.
        unfold set_remove in H0.
        { destruct (Aeq_dec b a0) eqn:Eq.
          - subst. apply H3. auto.
          - inversion H0.
            + apply n. auto.
            + assert (((fix set_remove (a : A) (x : set A) {struct x} : set A :=
                          match x with
                          | nil => empty_set A
                          | a1 :: x1 => if Aeq_dec a a1 then x1 else a1 :: set_remove a x1
                          end) b l) = set_remove Aeq_dec b l) by auto.
              rewrite H2 in H1. apply IHl in H4; auto. apply H4 in H1. destruct H1. apply H5.
              reflexivity. }
    + inversion H0.
      destruct (Aeq_dec b a0) eqn:Eq.
      * unfold set_remove. rewrite Eq.
        { inversion H.
          - apply IHl in H6.
            inversion H1.
            + subst. exfalso. apply H2. auto.
            + auto. }
      * unfold set_remove. rewrite Eq.
        assert (((fix set_remove (a : A) (x : set A) {struct x} : set A :=
                    match x with
                    | nil => empty_set A
                    | a1 :: x1 => if Aeq_dec a a1 then x1 else a1 :: set_remove a x1
                    end) b l) = set_remove Aeq_dec b l) by auto.
        rewrite H3.
        { destruct (Aeq_dec a a0).
          - left. auto.
          - right. inversion H. apply IHl in H7. apply H7.
            split.
            + inversion H1; subst; auto; exfalso; apply n0; auto.
            + auto. }
Qed.

Lemma set_remove_nodup (A : Type) (Aeq_dec: forall x y:A, {x = y} + {x <> y}) (a : A) (l : set A) :
  NoDup l -> NoDup (set_remove Aeq_dec a l).
Proof.
  induction l.
  - auto.
  - intros. inversion H. unfold set_remove.
    destruct (Aeq_dec a a0); auto.
    assert (((fix set_remove (a1 : A) (x0 : set A) {struct x0} : 
               set A :=
                 match x0 with
                 | nil => empty_set A
                 | a2 :: x1 => if Aeq_dec a1 a2 then x1 else a2 :: set_remove a1 x1
                 end) a l) = set_remove Aeq_dec a l) by auto.
    rewrite H4.
    apply NoDup_cons; auto.
    unfold not. intros.
    apply set_remove_iff with (Aeq_dec:=Aeq_dec) (a:=a0) (b:=a) in H3.
    apply H3 in H5. destruct H5. auto.
Qed.

Lemma in_prop : forall (A : Type) (l : list A) (x : A),
  In x l -> exists (y : A), Some y = head l.
Proof.
  induction l.
  - intros. inversion H.
  - intros. exists a. reflexivity.
Qed.

Lemma set_mem_remove (A : Type) (Aeq_dec: forall x y:A, {x = y} + {x <> y}) (a a': A) (l : set A) :
  a <> a' -> set_mem Aeq_dec a (set_remove Aeq_dec a' l) = set_mem Aeq_dec a l.
Proof.
  induction l; intros.
  - reflexivity.
  - assert (a <> a') by apply H. apply IHl in H.
    destruct (Aeq_dec a' a0) eqn:Eq.
    + subst. simpl. rewrite Eq. Search sumbool.
      destruct (Aeq_dec a a0).
      * exfalso. apply H0. auto.
      * reflexivity.
    + simpl. rewrite Eq. simpl. rewrite H. reflexivity.
Qed.

Lemma set_inter_remove (A : Type) (Aeq_dec: forall x y:A, {x = y} + {x <> y}) (a : A) (l l' : set A) :
  ~ (set_In a l) -> set_inter Aeq_dec l (set_remove Aeq_dec a l') = set_inter Aeq_dec l l'.
Proof.
  induction l; intros.
  - reflexivity.
  - destruct (Aeq_dec a a0).
    + exfalso. apply H. subst. constructor. reflexivity.
    + assert ( ~set_In a l ). { unfold not. intros. apply H. simpl. right. auto. } simpl.
      assert (n' : a0 <> a) by auto.
      apply set_mem_remove with (Aeq_dec:=Aeq_dec) (l := l') in n'.
      rewrite n'.
      apply IHl in H0. rewrite H0. reflexivity.
Qed.

Lemma set_remove_len (A : Type) (Aeq_dec: forall x y:A, {x = y} + {x <> y}) (a : A) (l : set A) :
  length (set_remove Aeq_dec a l) + 1 >= length l.
Proof.
  induction l; intros.
  - simpl. omega.
  - simpl.
    destruct (Aeq_dec a a0).
    + omega.
    + simpl. omega.
Qed.

Lemma in_not_nil (A : Type) (l : list A) :
  l <> nil -> exists x, In x l.
Proof.
  induction l.
  - intros. exfalso. auto.
  - intros. exists a. left. reflexivity.
Qed.


Theorem FailPreservesInvariant :
  forall (s s' : NetState) (f : Node),
    Invariant s /\ Fail s s' f -> Invariant s'.
Proof.
  intros. unfold Invariant. split.
  - (* Failing results in a Well-Formed Net State *)
    destruct H as [_ [_ [_ [_ [H _]]]]]. auto.
  - split.
    + (* Failing preserves in OneLiveSuccessor *)
      intros. destruct H.
      destruct H as [H [BS _]]. unfold WellFormedNetState in H.
      destruct H as [SC [_ [_ [_ [NBS [_ [_ [NDM _]]]]]]]].
      unfold not. intros.
      destruct H1 as [_ [Inf [[Succf _] [[SC' [_ [_ [_ [_ [BSF' _]]]]]] [Succlength [_ [Members [Succ _]]]]]]]].
      destruct n as [nn]. destruct f as [fn].
      destruct (nn =? fn) eqn:Eq.
      * (* The node (N nf) that failed is (N nn) *)
        apply beq_nat_true in Eq. subst.
        rewrite -> Members in H0.
        apply set_remove_iff with (Aeq_dec:=cmp_dec) (a:=N fn) (b:=N fn) in NDM.
        apply NDM in H0. destruct H0. auto.
      * (* The node (N nf) that failed is not (N nn) *)
        apply beq_nat_false in Eq.
        assert (Ins' : set_In (N nn) (members s')) by (apply H0).
        assert (Ins'' : set_In (N nn) (members s')) by (apply H0).
        rewrite -> Members in H0.
        assert (NDM' : NoDup (members s)) by (apply NDM).
        apply set_remove_iff with (Aeq_dec:=cmp_dec) (a:=N nn) (b:=N fn) in NDM.
        apply NDM in H0. destruct H0.
        apply BSF' in Ins'.
        assert (set_inter cmp_dec (succ s' (N nn)) (members s') <> empty_set Node).
        { assert (Inf' : set_In (N fn) (succ s (N nn)) -> exists m' : Node,
            set_In m' (members s) /\ m' <> N fn /\ set_In m' (succ s (N nn))) by auto.
          assert (InSuccf : {In (N fn) (succ s (N nn))} + {~ In (N fn) (succ s (N nn))}) by (apply in_dec; apply cmp_dec).
          destruct InSuccf.
          - (* (N fn) is in (succ n (N nn)) *)
            apply Inf' in i. destruct i.
            (* x is in (set_inter cmp_dec (succ s' (N nn)) (members s')), so the intersection cannot be empty*)
            apply set_remove_iff with (Aeq_dec := cmp_dec) (a:=x) (b:=N fn) in NDM'.
            rewrite <- Members in *. clear Members.
            assert (InxSucc' : set_In x (succ s' (N nn))).
              { apply (Succ (N nn)) in Ins''. rewrite Ins'' in *. repeat (destruct H2 as [_ H2]). auto. }
            assert (InxMem' : set_In x (members s')).
              { apply NDM'. split; destruct H2; auto; destruct H3; auto. }
            apply set_inter_intro with (Aeq_dec:=cmp_dec) (x:=succ s' (N nn)) in InxMem'; auto.
            unfold not. intros. rewrite H3 in InxMem'. inversion InxMem'.
          - (* (N fn) is not in (succ s (N nn)) *)
            apply (Succ (N nn)) in Ins''. rewrite Ins'' in *.
            (* the intersection of (succ s (N nn)) and (members s) is the same as the intersection of
               (succ s (N nn)) and (set_remove cmp_dec (N fn) members) *)
            assert (set_inter cmp_dec (succ s (N nn)) (members s') = set_inter cmp_dec (succ s (N nn)) (members s)).
              { rewrite Members. apply set_inter_remove. auto. }
            (* use the well-formedness of the NetState s to show that
               (set_inter cmp_dec (succ s (N nn)) (members s) <> None) *)
            rewrite H2. unfold not. intros.
            assert (bestSucc s (N nn) <> None) by (apply BS in H0; auto).
            apply H4. apply NBS in H0. auto.
       }
        assert (exists x, In x (filter (fun x : Node => set_mem cmp_dec x (members s')) (succ s' (N nn)))).
        { apply in_not_nil in H2. destruct H2.
          exists x. apply filter_In. split.
          - apply set_inter_elim1 in H2. auto.
          - apply set_inter_elim2 in H2. apply set_mem_correct2. auto. }
        apply BSF' in H2; auto.
        destruct H3.
        apply in_prop in H3.
        destruct H3.
        rewrite <- H3 in *.
        rewrite H in H2.
        inversion H2.
     + (* Failing preserves SufficientPrincipals *)
       destruct H.
       destruct H0 as [_ [_ [[_ PrincipPrecond'] [[_ [_ [PC' [_ [_ [_ [P' [NDM' [NDP' _]]]]]]]]]
                      [Succlength [_ [Members [Succ _]]]]]]]].
       destruct H as [[_ [_ [PC [_ [_ [_ [P [NDM [NDP _]]]]]]]]] [_ PrincipCond]].
       unfold PrincipalsCondition in *.
       unfold Principals in *.
       assert (MS' : forall a, In a (set_remove cmp_dec f (members s)) <-> In a (members s) /\ a <> f).
       { intros. apply set_remove_iff. auto. }
       assert (forall m, set_In m (principals s) -> m <> f -> set_In m (principals s')).
       { intros.
         assert (set_In m (members s)). { apply PC in H. auto. }
         specialize (P m).
         rewrite <- P in H.
         apply P'.
         rewrite <- Members in *.
         intros.
         assert (set_In m0 (members s')) by (apply H2).
         specialize (H m0). rewrite MS' in H2. destruct H2.
         apply H; auto.
         apply Succ in H4. rewrite <- H4. auto. }
       (* have that set_remove cmp_dec f (members s) (principals s) is a subset of (principals s')*)
       assert (Incl: incl (set_remove cmp_dec f (principals s)) (principals s')).
         { unfold incl. intros. rewrite set_remove_iff in H0; auto. destruct H0. apply H; auto. }
       assert (Len : length (set_remove cmp_dec f (principals s)) + 1 >= length (principals s)).
         { apply set_remove_len. }
       assert (NDPf : NoDup (set_remove cmp_dec f (principals s))).
         { apply set_remove_nodup. auto. }
       apply NoDup_incl_length with (l' := principals s') in NDPf; auto.
       assert ({In f (principals s)} + {~ In f (principals s)}) by (apply in_dec; apply cmp_dec).
       destruct H0.
       * apply PrincipPrecond' in i. omega.
       * apply set_remove_nothing with (Aeq_dec:=cmp_dec) (a:=f) in n. rewrite n in *.
         omega.
Qed.

Definition Join (s s' : NetState) (j : Node) : Prop :=
  (* PRECONDITIONS *)
  WellFormedNetState s /\
  ~ (set_In j (members s)) /\
  (* j queries m to get its successor list *)
  (exists (m : Node), forall (m' : Node),
     set_In m (members s) /\
     Some m' = head (succ s m) -> between m j m' /\
  (* POSTCONDITIONS *)
  WellFormedNetState s' /\
  succlength s' = succlength s /\
  time s' = next (time s) /\
  members s' = set_add cmp_dec j (members s) /\
  (forall (m : Node), set_In m (members s) -> succ s' m = succ s m) /\
  succ s' j = succ s m /\
  (forall (m : Node), set_In m (members s) -> prdc s' m = prdc s m) /\
  prdc s' j = m /\
  status s' = status s /\
  saved s' = saved s).

Theorem JoinPreservesInvariant :
  forall (s s' : NetState) (j : Node),
    Invariant s /\ Join s s' j -> Invariant s'.
Admitted.

Definition nextInRing (s : NetState) (n n' : Node) : Prop :=
  IsRingMember s n' /\
  (forall (n'' : Node), IsRingMember s n'' -> between n n' n'').

Definition StabilizeFromSuccessor (s s' : NetState) (t : Node) : Prop :=
  (* PRECONDITIONS *)
  WellFormedNetState s /\
  set_In t (members s) /\
  (status s t) = None /\
  (* POSTCONDITIONS *)
  WellFormedNetState s' /\
  succlength s' = succlength s /\
  time s' = next (time s) /\
  members s' = members s /\
  prdc s' = prdc s /\
  forall (succ1 : Node),
    Some succ1 = head (succ s t) ->
     (* successor is dead *)
     (~ set_In succ1 (members s) ->
       (* t' is the next node in the ring after the last entry in t's successor list *)
       forall (t' : Node),
         nextInRing s (last (succ s t) t) t' ->
           (* there is a list u that consists of the tail of t's successor list appended
              to the singleton list consisting of t' *)
           forall (u : list Node),
             u = tl (succ s t) ++ (t'::nil) ->
             (length u = succlength s /\
             (* all successor lists other than t's are unchanged *)
             (forall (m : Node), m <> t -> succ s' m = succ s m) /\
             (* t's successor list is u *)
             succ s' t = u)) /\
     (* successor is live *)
     (set_In succ1 (members s) ->
     (* t incorporates its successor's successor list *)
     succ s' t = succ1 :: (take (succ s succ1) (succlength s - 1)) /\
     (* successor's predecessor is better successor *)
     (between t (prdc s succ1) succ1 ->
        (forall (m : Node), set_In m (members s) ->
         (m <> t -> (status s' m = status s m /\ saved s' m = saved s m)) /\
         status s' t = Some Stabilizing /\ saved s' t = Some (prdc s succ1))) /\
     (* successor's predecessor is no improvement, op is done *)
     (~ between t (prdc s succ1) succ1 ->
       (forall (ts : Node), Some ts = head (succ s' t) ->
          (forall (m : Node), set_In m (members s) ->
          (m <> ts -> (status s' m = status s m /\ saved s' m = saved s m)) /\
          status s' ts = Some Rectifying /\ saved s' ts = Some t)))).

Definition StabilizeDead (s s' : NetState) (t : Node) :=
  WellFormedNetState s -> WellFormedNetState s' ->
  StabilizeFromSuccessor s s' t /\
  forall (ts : Node), Some ts = head (succ s t) -> ~ set_In ts (members s).

Definition StabilizeToNextStep (s s' : NetState) (t : Node) :=
  WellFormedNetState s -> WellFormedNetState s' ->
  forall (succ1 : Node),
    Some succ1 = head (succ s t) ->
    (StabilizeFromSuccessor s s' t /\ set_In succ1 (members s) /\
    between t (prdc s succ1) succ1).

Definition StabilizeWithListChange (s s' : NetState) (t : Node) :=
  WellFormedNetState s -> WellFormedNetState s' ->
  forall (succ1 : Node),
    Some succ1 = head (succ s t) ->
    (StabilizeFromSuccessor s s' t /\ set_In succ1 (members s) /\
     ~ between t (prdc s succ1) succ1 /\ succ s t <> succ s' t).

Theorem StabilizeFromSuccessorPreservesInvariant :
  forall (s s' : NetState) (t : Node),
    Invariant s /\ StabilizeFromSuccessor s s' t -> Invariant s'.
Admitted.

Definition StabilizeFromPredecessor (s s' : NetState) (t : Node) : Prop :=
  (* PRECONDITIONS *)
  WellFormedNetState s /\
  set_In t (members s) /\
  status s t = Some Stabilizing /\
  (* to ensure the following precondition, t must not change its successor
     between the StabilizeFromSuccessor state transition that created the
     Stabilizing status and now *)
  (* t queries its saved successor's predecessor to get its successor list,
     if possible *)
  (exists (sa : Node), Some sa = saved s t) /\
  (forall (sa ts : Node), Some sa = saved s t -> Some ts = head (succ s t) ->
     between t sa ts) /\
  (* POSTCONDITIONS *)
  WellFormedNetState s' /\
  succlength s' = succlength s /\
  time s' = next (time s) /\
  members s' = members s /\
  prdc s' = prdc s /\
  forall (newSucc : Node), Some newSucc = saved s t ->
    (* predecessor is dead *)
    (~ set_In newSucc (members s) ->
       succ s' = succ s /\
       (forall (m : Node), m <> t ->
        status s' m = status s m /\ saved s' m = saved s m) /\
       status s' t = None /\ saved s' t = None) /\
    (* predecessor is alive *)
    (set_In newSucc (members s) ->
    (* t incorporates the predecessor's successor  *)
       succ s' t = newSucc :: (take (succ s newSucc) (succlength s - 1))) /\
       (forall (m : Node), m <> t -> succ s' m = succ s m) /\
       (forall (m : Node), m <> t -> status s m = status s' m) /\
       status s' t = None /\
       status s' newSucc = Some Rectifying /\
       (forall (m : Node), m <> t -> m <> newSucc -> saved s m = saved s' m) /\
       saved s' t = None /\
       saved s' newSucc = Some t.

Definition StabilizeFromDeadPredecessor (s s' : NetState) (t : Node): Prop :=
  WellFormedNetState s -> WellFormedNetState s' ->
  StabilizeFromPredecessor s s' t /\
  forall (sa : Node), Some sa = saved s t -> ~ set_In sa (members s).

Definition ActiveStabilizeFromPredecessor (s s' : NetState) (t : Node): Prop :=
  WellFormedNetState s -> WellFormedNetState s' ->
  StabilizeFromPredecessor s s' t /\
  forall (sa : Node), Some sa = saved s t -> set_In sa (members s).

Theorem StabilizeFromPredecessorPreservesInvariant :
  forall (s s' : NetState) (t : Node),
    Invariant s /\ StabilizeFromPredecessor s s' t -> Invariant s'.
Admitted.

Definition Rectify (s s' : NetState) (r : Node) : Prop :=
  (* PRECONDITIONS *)
  WellFormedNetState s /\
  set_In r (members s) /\
  status s r = Some Rectifying /\
  (exists (sa : Node), Some sa = saved s r) /\
  (* if necessary, r queries its current predecessor to see if it is alive *)
  (* POSTCONDITIONS *)
  WellFormedNetState s' /\
  succlength s' = succlength s /\
  time s' = next (time s) /\
  members s' = members s /\
  succ s' = succ s /\
  (forall (m : Node), m <> r -> status s' m = status s m) /\
  status s' r = None /\
  (forall (m : Node), m <> r -> saved s' m = saved s m) /\
  saved s' r = None /\
  (forall (newPrdc : Node),
     Some newPrdc = saved s r ->
       ( (*adopt new predecessor without checking old*)
         (between (prdc s r) newPrdc r ->
           (forall (m : Node), m <> r -> prdc s' m = prdc s m) /\
           prdc s r = newPrdc) /\
         (* check old predecessor *)
         (~ between (prdc s r) newPrdc r ->
            (* no change *)
            (set_In (prdc s r) (members s) -> prdc s' = prdc s) /\
            (* old predecessor dead, adopt new one *)
            (~ set_In (prdc s r) (members s) ->
               (forall (m : Node), m <> r -> prdc s' m = prdc s m) /\
               prdc s r = newPrdc)))).

Definition ActiveRectify (s s' : NetState) (r : Node) : Prop :=
  WellFormedNetState s -> WellFormedNetState s' ->
  Rectify s s' r /\ prdc s' <> prdc s.

Theorem RectifyPreservesInvariant :
  forall (s s' : NetState) (t : Node),
    Invariant s /\ Rectify s s' t -> Invariant s'.
Admitted.

(** TRACE STRUCTURE *)
Definition Stutter (s s' : NetState) : Prop :=
  WellFormedNetState s /\ WellFormedNetState s' /\
  time s' = next (time s) /\ succlength s' = succlength s /\
  members s' = members s /\ succ s' = succ s /\
  prdc s' = prdc s /\ status s = status s' /\ saved s' = saved s'.

Inductive NextNetState : NetState -> NetState -> Prop :=
  | stutter : forall (s s' : NetState), Stutter s s' -> NextNetState s s'
  | fail : forall (s s' : NetState) (n : Node),
      Fail s s' n -> NextNetState s s'
  | join : forall (s s' : NetState) (n : Node),
      Join s s' n -> NextNetState s s'
  | stabilize_succ : forall (s s' : NetState) (n : Node),
      StabilizeFromSuccessor s s' n -> NextNetState s s'
  | stabilize_pred : forall (s s' : NetState) (n : Node),
      StabilizeFromPredecessor s s' n -> NextNetState s s'
  | rectify : forall (s s' : NetState) (n : Node),
      Rectify s s' n -> NextNetState s s'.

(** EFFECT ON THE BASE OF PRINCIPALS *)
Theorem LossOfPrincipal :
  forall (s s' : NetState),
    WellFormedNetState s -> WellFormedNetState s' ->
    NextNetState s s' /\ length (principals s') < length (principals s) ->
    exists (f : Node),
      Fail s s' f /\ principals s' = remove cmp_dec f (principals s).
Admitted.

(** PROGRESS PROPERTIES *)
Definition EffectiveStabilizeFromSuccessorIsEnabled
  (s : NetState) (m : Node) : Prop :=
  set_In m (members s) /\
  status s m = None /\
  forall (succ1 : Node), Some succ1 = head (succ s m) ->
    ~ (set_In succ1 (members s)) \/
    set_In succ1 (members s) /\ (succ s m) <> succ1 :: (tl (succ s succ1)).

Definition EffectiveStabilizeFromPredecessorIsEnabled
  (s : NetState) (m : Node) : Prop :=
  set_In m (members s) /\
  status s m = None /\
  forall (succ1 : Node), Some succ1 = head (succ s m) ->
    set_In succ1 (members s) /\
    between m (prdc s succ1) succ1 /\
    set_In (prdc s succ1) (members s).

Definition EffectiveRectifyFromSuccIsEnabled
  (s : NetState) (m : Node) : Prop :=
  set_In m (members s) /\
  status s m = None /\
  forall (succ1 : Node), Some succ1 = head (succ s m) ->
    set_In succ1 (members s) /\
    ~ between m (prdc s succ1) succ1 /\
    (between (prdc s succ1) m succ1 \/
     ~ set_In (prdc s succ1) (members s)).

Definition EffectiveRectifyFromPrdcIsEnabled
  (s : NetState) (m : Node) : Prop :=
  set_In m (members s) /\
  status s m = None /\
  forall (succ1 : Node), Some succ1 = head (succ s m) ->
    set_In succ1 (members s) /\
    between m (prdc s succ1) succ1 /\
    ( ((* (prdc s succ1) will be notified *)
       set_In (prdc s succ1) (members s) /\
       between (prdc s (prdc s succ1)) m (prdc s succ1) ) \/
      ((* (prdc s succ1) will be notified *)
       set_In (prdc s succ1) (members s) /\
       ~ set_In (prdc s (prdc s succ1)) (members s)) \/
      ((* succ1 will be notified *)
       ~ In (prdc s succ1) (members s)) ).

Theorem EffectiveStabilizeFromSuccChangesState :
  forall (s s' : NetState) (m : Node),
    WellFormedNetState s -> WellFormedNetState s' ->
    EffectiveStabilizeFromSuccessorIsEnabled s m /\
    StabilizeFromSuccessor s s' m -> succ s m <> succ s' m.
Admitted.

Theorem EffectiveStabilizeFromPrdcChangesState :
  forall (s s' s'' : NetState) (m : Node),
    WellFormedNetState s -> WellFormedNetState s' -> WellFormedNetState s'' ->
    EffectiveStabilizeFromPredecessorIsEnabled s m /\
    StabilizeFromSuccessor s s' m /\
    StabilizeFromPredecessor s' s'' m -> succ s m <> succ s'' m.
Admitted.

Theorem EffectiveRectifyFromSuccChangesState :
  forall (s s' s'' : NetState) (m : Node),
    WellFormedNetState s -> WellFormedNetState s' -> WellFormedNetState s'' ->
    forall (succ1 : Node), Some succ1 = head (succ s m) ->
      EffectiveRectifyFromSuccIsEnabled s m /\
      StabilizeFromSuccessor s s' m /\
      Rectify s' s'' succ1 -> prdc s succ1 <> prdc s'' succ1.
Admitted.

Theorem EffectiveRectifyFromPrdcChangesState :
  forall (s s' s'' s''' : NetState) (m r : Node),
    WellFormedNetState s -> WellFormedNetState s' ->
    WellFormedNetState s'' -> WellFormedNetState s''' ->
    EffectiveRectifyFromPrdcIsEnabled s m /\
    StabilizeFromSuccessor s s' m /\
    StabilizeFromPredecessor s' s'' m /\
    Rectify s'' s''' r -> prdc s r <> prdc s''' r.
Admitted.

Theorem NonIdealImpliesChangeEnabled :
  forall (s : NetState),
    Invariant s /\ ~ Ideal s /\
    (forall (n : Node), set_In n (members s) -> status s n = None) ->
    exists (m : Node),
      EffectiveStabilizeFromSuccessorIsEnabled s m \/
      EffectiveStabilizeFromPredecessorIsEnabled s m \/
      EffectiveRectifyFromSuccIsEnabled s m \/
      EffectiveRectifyFromPrdcIsEnabled s m.
Admitted.

Theorem IdealImpliesNoChangeEnabled :
  forall (s : NetState),
    Invariant s /\ Ideal s /\
    (forall (n : Node), set_In n (members s) -> status s n = None) ->
    ~ (exists (m : Node),
      EffectiveStabilizeFromSuccessorIsEnabled s m \/
      EffectiveStabilizeFromPredecessorIsEnabled s m \/
      EffectiveRectifyFromSuccIsEnabled s m \/
      EffectiveRectifyFromPrdcIsEnabled s m).
Admitted.

(** Extra: There is a sequence of enabled operations that will attain Ideal *)
(* Make progress via enabled operations *)
Inductive NextNetStateProgress : NetState -> NetState -> Node -> Prop :=
  | stabilize_succ_enabled :
      forall (s s' : NetState) (m : Node),
        EffectiveStabilizeFromSuccessorIsEnabled s m ->
        StabilizeFromSuccessor s s' m ->
        NextNetStateProgress s s' m
  | stabilize_pred_enabled :
      forall (s s' s'' : NetState) (m : Node),
        EffectiveStabilizeFromPredecessorIsEnabled s m ->
        StabilizeFromSuccessor s s' m ->
        StabilizeFromPredecessor s' s'' m ->
        NextNetStateProgress s s'' m
  | rectify_succ_enabled :
      forall (s s' s'' : NetState) (m succ1 : Node),
        Some succ1 = head (succ s m) ->
        EffectiveRectifyFromSuccIsEnabled s m ->
        StabilizeFromSuccessor s s' m ->
        Rectify s' s'' succ1 ->
        NextNetStateProgress s s'' m
  | rectify_pred_enabled :
      forall (s s' s'' s''' : NetState) (m r : Node),
        EffectiveRectifyFromPrdcIsEnabled s m ->
        StabilizeFromSuccessor s s' m ->
        StabilizeFromPredecessor s' s'' m ->
        Rectify s'' s''' r ->
        NextNetStateProgress s s''' m.

Inductive Progress : NetState -> NetState -> Prop :=
  | step : forall (s s' : NetState) (m : Node),
      NextNetStateProgress s s' m -> Progress s s'
  | steps : forall (s s' s'': NetState) (m : Node),
      NextNetStateProgress s s' m -> Progress s' s'' -> Progress s s''.

Theorem AchieveIdeal : forall (s : NetState),
  Invariant s -> exists s', Progress s s' /\ Ideal s'.
Admitted.