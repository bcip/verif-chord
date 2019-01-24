Require Import Coq.omega.Omega.
Require Import Node.
Require Import NetState.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Definition NoDuplicates (s : NetState) : Prop :=
  forall n : Node,
    set_In n (members s) ->
    NoDup (n :: succ s n).

Lemma AdjacentIndexAdjacent :
  forall (A : Type) (l : list A) (d : A) (i j : nat),
    0 <= i < j /\ j < length l ->
    i+1 = j ->
    adjacent (nth i l d) (nth j l d) l.
Proof.
  intros A l d i.
  revert l.
  induction i; intros.
  - (* i = 0 *)
    subst j.
    destruct l as [ | x [ | y l]]; simpl in *; try omega.
    constructor 1; auto.
  - (* i > 0 *)
    destruct l as [ | hd l].
    + simpl in *. omega. (* length l <> 0 *)
    + destruct j; try omega. (* j > 0 *)
      simpl.
      constructor 2.
      * simpl. congruence.
      * apply IHi; simpl in *; omega.
Qed.

Lemma RangeContainsPrincipal :
  forall (s : NetState) (p : Node),
  Principal s p ->
  forall (n : Node) (i j : nat),
  set_In n (members s) ->
  0 <= i < j /\ j <= succlength s ->
  succlength s = length (succ s n) ->
  let esl := n :: (succ s n) in
    between
    (nth i esl n)
    p
    (nth j esl n) ->
  exists (k : nat),
  i < k < j /\
  nth k esl n = p.
Proof.
  intros.
  specialize (H n H0).
  set (gap1 := j-i-1).
  assert (gap1 = j-i-1) by auto.
  clearbody gap1.
  fold esl in H.
  generalize dependent j. generalize dependent i.
  induction gap1; intros.
  - (* gap = j-i = 1 *)
    assert (j = i+1) by omega.
    assert (adjacent (nth i esl n) (nth j esl n) esl) by (apply AdjacentIndexAdjacent; simpl; omega).
    exfalso. unfold not in H. eauto.
  - (* gap = j-i > 1 *)
    destruct (eq_dec p (nth (i+1) esl n)).
    + (* p = i+1 th *)
      exists (i+1). omega.
    + (* p <> i+1 th *)
      pose (BetweenDivision _ _ _ _ H3 n0) as Hbetween.
      destruct Hbetween.
      * (* p between i th and i+1 th *)
        assert (adjacent (nth i esl n) (nth (i+1) esl n) esl) by (apply AdjacentIndexAdjacent; simpl; omega).
        exfalso. unfold not in H. eauto.
      * (* p between i+1 th and j th *)
        enough (exists k : nat, (i+1) < k < j /\ nth k esl n = p).
        -- destruct H6 as [k H6]. exists k. omega.
        -- apply IHgap1; auto; omega.
Qed.

Lemma Dup_NotNoDup :
  forall (A : Type) (l : list A) (d : A) (i j : nat),
  0 <= i < j /\ j < length l ->
  nth i l d = nth j l d ->
  ~ (NoDup l).
Proof.
  intros. intro HNoDup.
  generalize dependent j. generalize dependent i.
  induction HNoDup; intros.
  - simpl in H. omega.
  - destruct i; destruct j; try omega; simpl in *.
    + apply H. rewrite H1. apply nth_In. omega.
    + eapply IHHNoDup. 2 : apply H1. omega.
Qed.

Lemma NotDup_NoDup :
  forall (A : Type) (l : list A) (d : A),
  ~ (exists (i j : nat),
    0 <= i < j /\ j < length l /\
    nth i l d = nth j l d) ->
  NoDup l.
Proof.
  intros. induction l.
  - constructor.
  - constructor.
    + intro. apply H.
      pose (In_nth _ _ d H0) as Hnth. destruct Hnth as [j Hnth].
      exists 0, (1+j). simpl. intuition.
    + apply IHl. intro Hnth. destruct Hnth as [i [j Hnth]].
      apply H. exists (1+i), (1+j). simpl. intuition.
Qed.

Definition sublist {A : Type} (i j : nat) (l : list A) : list A :=
    skipn i (firstn j l).

(* Basic lemmas about sublist is not insterestig for this proof *)
Axiom skipn_skipn : forall (A : Type) (i j : nat) (l : list A),
  skipn i (skipn j l) = skipn (i+j) l.

Axiom firstn_skipn : forall (A : Type) (i j : nat) (l : list A),
  firstn i (skipn j l) = skipn j (firstn (i+j) l).

Axiom sublist_cons : forall (A : Type) (i j : nat) (l : list A) (x : A),
  sublist (S i) (S j) (x :: l) = sublist i j l.

Axiom sublist_cons_0 : forall (A : Type) (j : nat) (l : list A) (x : A),
  sublist 0 (S j) (x :: l) = x :: (sublist 0 j l).

Lemma InSublist :
  forall (A : Type) (l : list A) (x d : A) (i j k : nat),
  0 <= i <= k /\ k < j <= length l ->
  nth k l d = x ->
  In x (sublist i j l).
Proof.
  intros A l x d. induction l; intros.
  - simpl in *. omega.
  - destruct k.
    + assert (i = 0) by omega; subst.
      destruct j; try omega. (* j > 0 *)
      simpl. auto.
    + destruct j; try omega. (* j > 0 *)
      assert (In x (sublist (pred i) j l)).
      {
        eapply IHl.
        2 : apply H0.
        simpl in *. omega.
      }
      destruct i.
      * rewrite sublist_cons_0. constructor 2. apply H1.
      * rewrite sublist_cons. apply H1.
Qed.

Lemma InListRemove :
  forall (A : Type) (l : list A) (x : A),
    In x l ->
    exists l',
      1 + length l' = length l /\
      forall (y : A),
        In y l -> x = y \/ In y l'.
Proof.
  intros. induction l.
  - inversion H.
  - inversion H.
    + exists l. split; auto.
      intros. inversion H1.
      * subst. auto.
      * auto.
    + specialize (IHl H0). destruct IHl as [l' IHl].
      exists (a :: l'). split.
      * simpl in *. omega.
      * intros. inversion H1.
        -- right. constructor. auto.
        -- destruct IHl.
           specialize (H4 y H2).
           destruct H4.
           ++ left; auto.
           ++ right. constructor 2. apply H4.
Qed.

Lemma ListNotContainsMoreElements :
  forall (A : Type) (l s : list A),
  length s > length l ->
  NoDup s ->
  ~ (forall x, In x s -> In x l).
Proof.
  intros. generalize dependent l. induction s; intros.
  - (* s = nil *)
    inversion H.
  - (* s <> nil *)
    inversion_clear H0.
    specialize (IHs H2).
    intro Hcontain.
    pose (Hcontain a) as Ha.
    pose (InListRemove _ l a) as Hl'.
    assert (In a l) by (apply Ha; constructor; auto).
    specialize (Hl' H0). destruct Hl' as [l' Hl'].
    assert (length s > length l') by (simpl in *; omega).
    specialize (IHs l' H3).
    apply IHs. intros.
    assert (a <> x). {
      intro. subst. auto.
    }
    destruct Hl'. specialize (H7 x).
    assert (In x l) by intuition.
    intuition.
Qed.

(* Basic lemmas about sublist is not insterestig for this proof *)
Axiom sublist_length :
  forall (A : Type) (l : list A) (i j : nat),
    0 <= i <= j /\ j <= length l ->
    length (sublist i j l) = j-i.

Theorem InvariantEnsuresNoDuplicates :
  forall (s : NetState), Invariant s -> NoDuplicates s.
Proof.
  unfold Invariant, SufficientPrincipals. intros.
  destruct H as [HWellFormedNetState [HLiveSuccCondition [principals HSufficientPrincipals]]].
  intros n HnIn. apply NotDup_NoDup with n. intros [i [j HDup]].
  assert (length (succ s n) = succlength s) as Hlength by (unfold WellFormedNetState in *; intuition).
  eapply ListNotContainsMoreElements with (l := sublist i j (n :: succ s n)) (s := principals).
  - rewrite sublist_length by omega. simpl in *. omega.
  - tauto.
  - intros p HpIn. unfold set_In in HSufficientPrincipals.
    assert (Principal s p) as HPrincipal. {
      intuition.
      specialize (H4 p). tauto.
    }
    destruct (eq_dec p (nth i (n :: succ s n) n)) as [Heq | Hneq].
    + apply InSublist with (k := i) (d := n); omega.
    + pose (RangeContainsPrincipal s p ltac:(auto) n i j ltac:(auto)) as HInRange.
      destruct HInRange as [k HInRange]; try (simpl in *; omega). { 
        replace ((nth j (n :: succ s n) n)) with ((nth i (n :: succ s n) n)) by tauto.
        apply AnyBetweenAny. auto.
      }
      apply InSublist with (k := k) (d := n); omega.
Qed.

Definition bestSucc (s : NetState) (n : Node) : option Node :=
  if set_In_dec eq_dec n (members s)
  then find (fun m => if set_In_dec eq_dec m (members s) then true else false) (succ s n)
  else None.

(* A ring member is a network member that can be reached by
  following the chain of best successors beginning at itself. *)
Inductive CanReach : NetState -> Node -> Node -> Prop :=
  | reach_direct   : forall (s : NetState) (n n' : Node),
                  bestSucc s n = Some n' ->
                  CanReach s n n'
  | reach_indirect : forall (s : NetState) (n n' n'' : Node),
                  bestSucc s n = Some n' ->
                  CanReach s n' n'' ->
                  CanReach s n n''.

Definition IsRingMember (s : NetState) (n : Node) : Prop :=
  CanReach s n n.

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
Proof.
  unfold Invariant, OrderedSuccessorLists, SufficientPrincipals. intros.
  destruct H as [HWellFormedNetState [HLiveSuccCondition [principals HSufficientPrincipals]]].
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