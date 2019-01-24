Require Import Coq.omega.Omega.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.

(** Nodes *)

Definition Node : Type := nat.


Definition eq_dec : forall x y : Node, {x = y} + {x <> y}
  := Nat.eq_dec.

Theorem cmp_dec : forall x y : Node,
  {x = y} + {x <> y}.
Proof.
  exact Nat.eq_dec.
Qed.

(** THEOREMS ABOUT IDENTIFIER SPACES *)
Inductive between : Node -> Node -> Node -> Prop :=
  | Between :
      forall n1 nb n2,
        lt n1 n2 -> lt n1 nb -> lt nb n2 ->
        between n1 nb n2
  | Between_cycle :
      forall n1 nb n2,
        ~(lt n1 n2) -> (lt n1 nb) \/ (lt nb n2) ->
        between n1 nb n2.

Theorem AnyBetweenAny :
  forall (n1 n2 : Node), n1 <> n2 -> between n1 n2 n1.
Proof.
  intros.
  apply Between_cycle.
  - unfold not.
    intros. unfold lt in H0.
    omega.
  - unfold Node in *. omega.
Qed.

Inductive includedIn : Node -> Node -> Node -> Prop :=
  | Included :
      forall n1 nb n2,
        lt n1 n2 -> le n1 nb -> le nb n2 ->
        includedIn n1 nb n2
  | Included_cycle :
      forall n1 nb n2,
        ~(lt n1 n2) -> le n1 nb \/ le nb n2 ->
        includedIn n1 nb n2.

Theorem AnyIncludedInAny :
  forall (n1 n2 : Node), includedIn n1 n2 n1.
Proof.
  intros.
  apply Included_cycle.
  - unfold not.
    intros. unfold lt in H.
    omega.
  - assert (H'' : n1 <= n2 \/ n2 <= n1).
    { omega. }
    destruct H''.
    + destruct H; left; auto; right; omega.
    + destruct H; right; auto; right; omega.
Qed.

Theorem BetweenDivision :
  forall (n1 n2 nb nm: Node),
  between n1 nb n2 ->
  nb <> nm ->
  between n1 nb nm \/ between nm nb n2.
Proof.
  intros.
  inversion H; subst; intuition;
  fold not;
  destruct (lt_dec nb nm);
  try solve [(left + right);
  (constructor 1 + constructor 2);
  omega];
  destruct (lt_dec n1 nm);
  destruct (lt_dec nm n2);
  try solve [(left + right);
  (constructor 1 + constructor 2);
  omega].
Qed.

(* Theorem Untitled :
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
        assert (le n1 nb) by (omega).
        assert (le nb n2) by (omega).
        apply Included; auto.
      * (* Between_cycle *) subst.
        assert (le n1 nb \/ le nb n2).
          { inversion H2.
            - left; omega.
            - omega. }
        apply Included_cycle; auto.
   + inversion H0.
     * (* n1 = nb *)
       rewrite H1 in *.
       destruct (nb <? n2) eqn:Less.
       { rewrite Nat.ltb_lt in Less.
         apply Included; auto. omega. }
       { rewrite Nat.ltb_nlt in Less.
         apply Included_cycle; auto; omega. }
    * (* nb = nb *)
      rewrite H1 in *.
      destruct (n1 <? n2) eqn:Less.
      { rewrite Nat.ltb_lt in Less.
        apply Included; auto. omega. }
       { rewrite Nat.ltb_nlt in Less.
         apply Included_cycle; omega. }
Qed. *)

(* Theorem IncludedReversesBetween :
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
Admitted. *)
