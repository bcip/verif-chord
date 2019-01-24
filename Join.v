Require Import Coq.omega.Omega.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Node.
Require Import NetState.

Definition Join (s s' : NetState) (j : Node) : Prop :=
  (* unchanged properties *)
  succlength s' = succlength s /\
  (forall (n : Node), set_In n (members s) -> succ s' n = succ s n) /\
  (forall (n : Node), set_In n (members s) -> prdc s' n = prdc s n) /\
  ~ (set_In j (members s)) /\
  members s' = j :: members s /\
  (* j queries m to get its successor list *)
  (exists (n : Node),
    set_In n (members s) /\
      (forall (m : Node),
        Some m = head (succ s n) -> between n j m) /\
    succ s' j = succ s n /\
    prdc s' j = n).

Lemma Exists_imp :
  forall (A : Type) (l : list A) (P Q : A -> Prop),
    (forall (x : A), P x -> Q x) ->
    Exists P l ->
    Exists Q l.
Proof.
  intros. rewrite Exists_exists in *.
  destruct H0.
  exists x. intuition.
Qed.

Lemma JoinPreservesPrincipal :
  forall (s s' : NetState) (j p : Node),
    Join s s' j -> Principal s p -> Principal s' p.
Proof.
  unfold Principal. intros.
  replace (members s') with (j :: members s) in *.
    2 : {unfold Join in *. intuition. }
  inversion H1.
  - (* n = j *)
    subst n.
    assert (exists (m : Node), set_In m (members s) /\ (forall m0 : Node, Some m0 = hd_error (succ s m) -> between m j m0) /\ succ s' j = succ s m). {
      unfold Join in *. intuition. destruct H8. exists x. tauto.
    }
    destruct H3 as [m [? []]].
    rewrite H5 in *.
    inversion H2; subst.
    + simpl in H6, H7.
      inversion H6; subst j0.
      specialize (H4 k ltac:(auto)).
      assert (~ between m p k). {
        apply H0 with m; auto.
        constructor 1; auto.
      }
      intro. apply H8.
      inversion H4; inversion H9;
      constructor 1 + constructor 2;
      intuition; omega.
    + simpl in H7.
      apply H0 with m; auto.
        constructor 2; auto.
        simpl. discriminate.
  - (* n <> j *)
    apply H0 with n; auto.
    assert (succ s' n = succ s n). {
      unfold Join in *. intuition.
    }
    congruence.
Qed.

Theorem JoinPreservesInvariant :
  forall (s s' : NetState) (j : Node),
    Invariant s /\ Join s s' j -> Invariant s'.
Proof.
  unfold Invariant, OrderedSuccessorLists, Join. intros.
  destruct H as [[HWellFormedNetState [HLiveSuccCondition [principals HSufficientPrincipals]]] HJoin].
  split; [ | split].
  - (* WellFormedNetState *)
    unfold WellFormedNetState in *.
    replace (members s') with (j :: members s) by intuition.
    repeat split.
    + constructor 2; intuition.
    + omega.
    + intros m H. inversion H.
      * subst m. intuition. destruct H12 as [n H12].
        replace (succ s' j) with (succ s n) by intuition.
        specialize (H7 n ltac:(tauto)). omega.
      * intuition.
        specialize (H4 m ltac:(tauto)).
        specialize (H8 m ltac:(tauto)).
        replace (succ s' m) with (succ s m) by intuition.
        omega.
  - (* LiveSuccCondition *)
    unfold LiveSuccCondition in *.
    replace (members s') with (j :: members s) by intuition.
    intros n H.
    assert (forall m : Node, set_In m (members s) -> set_In m (j :: members s)) by (constructor 2; auto).
    apply (Exists_imp _ _ _ _ H0).
    inversion H.
    + subst n. intuition. destruct H10 as [n ?].
      replace (succ s' j) with (succ s n) by intuition. apply HLiveSuccCondition. tauto.
    + replace (succ s' n) with (succ s n) by firstorder. apply HLiveSuccCondition. tauto.
  - (* SufficientPrincipals *)
    unfold SufficientPrincipals in *.
    exists principals.
    repeat split; try solve [tauto | intuition].
    + replace (members s') with (j :: members s) by intuition. constructor 2. firstorder.
    + apply JoinPreservesPrincipal with s j. apply HJoin. intuition. eapply proj2. eauto.
Qed.