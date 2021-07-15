Require Import ssreflect ssrfun.
Require Import HB.structures.
Require Import Arith.

Set Implicit Arguments.

HB.mixin Record IsMonoid M := {
  zero : M;
  add : M -> M -> M;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { M of IsMonoid M }.

HB.mixin Record IsRing R of Monoid R := {
  one : R; opp : R -> R; mul : R -> R -> R;
  addrC : @commutative R R add;
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.structure Definition Ring := { R of IsRing R & IsMonoid R }.

HB.mixin Record IsComRing R of Ring R := {
  mulrC : @commutative R R mul;
}.
HB.structure Definition ComRing := { R of IsComRing R & IsRing R & IsMonoid R }.


Section rings.
  Declare Scope ring_scope.

  Notation "0" := (@zero _) : ring_scope.
  Notation "1" := (@one _) : ring_scope.
  Notation "-%R" := (@opp _) : ring_scope.
  Notation "- x" := (opp x) : ring_scope.
  Notation "+%R" := (@add _) : fun_scope.
  Local Notation "*%R" := (@mul _) : fun_scope.
  Local Notation "x * y" := (mul x y) : ring_scope.
  Notation "x + y" := (add x y) : ring_scope.
  Notation "x - y" := (x + (@opp y)) : ring_scope.
  Open Scope ring_scope.

  Variable (R : Ring.type).
  Implicit Types a x y : R.
  Hint Rewrite (@addNr R) (@addrN R) (@addNr R) (@add0r R) (@addr0 R) : ring_scope.
  Hint Rewrite (@mul1r R) (@mulr1 R) : ring_scope.

  (* thm_1_1_1_1 *)
  Lemma mul0r a : 0 * a = 0.
  Proof.
    have H x: x + x = x -> x = 0
      by move=> xAddx; rewrite -xAddx -(addrN x) -{3}xAddx -addrA (addrN x) addr0.
    by apply: H; rewrite -mulrDl addr0.
  Qed.

  Hint Rewrite mul0r : ring_scope.

  (* thm_1_1_1_2 *)
  Lemma mulr0 a : a * 0 = 0.
    have H x: x + x = x -> x = 0
      by move=> xAddx; rewrite -xAddx -(addrN x) -{3}xAddx -addrA (addrN x) addr0.
    by apply: H; rewrite -mulrDr addr0.
  Qed.

  Hint Rewrite mulr0 : ring_scope.

  (* thm_1_1_2_1 *)
  Lemma opprK a : opp (opp a) = a.
  Proof.
    have H x y : x + y = 0 -> y = opp x
      by move=> H; rewrite -(add0r (opp x)) -H (addrC x y) -addrA addrN addr0.
    by symmetry; apply: H; rewrite addNr.
  Qed.

  Hint Rewrite opprK : ring_scope.

  Lemma thm_1_1_2_2_1 a b : a * (opp b) = opp (a * b).
  Proof.
    have H x y : x + y = 0 -> y = opp x
      by move=> H; rewrite -(add0r (opp x)) -H (addrC x y) -addrA addrN addr0.
    apply H.
    rewrite -mulrDr.
    by autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_2_2_1 : ring_scope.

  Lemma thm_1_1_2_2_2 a b : opp a * b = opp (a * b).
  Proof.
    have H x y : x + y = 0 -> y = opp x
      by move=> H; rewrite -(add0r (opp x)) -H (addrC x y) -addrA addrN addr0.
    by apply: H; rewrite -mulrDl addrN mul0r.
  Qed.

  Hint Rewrite thm_1_1_2_2_2 : ring_scope.

  Lemma thm_1_1_2_3 a b : opp a * opp b = a * b.
  Proof.
    by autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_2_3 : ring_scope.

  Fixpoint expt (a : R) (n : nat) : R :=
    match n with
    | 0 => 1
    | S n' => a * expt a n'
    end.

  Notation "x <^> y" := (expt x y) (at level 25, left associativity).

  Lemma thm_1_1_3_1 a n m : expt a n * expt a m = expt a (n + m).
  Proof.
    elim: n m => [| n IHn] /= m.
    - by autorewrite with ring_scope.
    - by rewrite -mulrA IHn.
  Qed.

  Hint Rewrite thm_1_1_3_1 : ring_scope.

  Lemma expt_I n : expt 1 n = 1.
  Proof.
    by elim n => [|?] /=; autorewrite with ring_scope.
  Qed.

  Hint Rewrite expt_I : ring_scope.

  Lemma thm_1_1_3_2 a n : forall m, a <^> n <^> m = a <^> (n * m).
  Proof.
    elim=> [| m IHm] /=.
    - by rewrite -mult_n_O.
    - rewrite IHm. autorewrite with ring_scope.
      by rewrite -mult_n_Sm Nat.add_comm.
  Qed.

  Hint Rewrite thm_1_1_3_2 : ring_scope.

  Lemma expt_reorder a : forall (n m o : nat),
      n = plus m o -> a <^> n = a <^> m * a <^> o.
  Proof. by move=>>; autorewrite with ring_scope; move <-. Qed.

  Lemma thm_1_1_4 : forall (a b : R) n,
      a * b = b * a
      -> (a * b) <^> n = a <^> n * b <^> n.
  Proof.
    intros a b n abComm.
    induction n.
    - by autorewrite with ring_scope.
    - simpl.
      rewrite -(mulrA a (a <^> n)).
      rewrite (mulrA (a <^> n)).
      assert (H: forall n, a <^> n * b = b * a <^> n).
      {
        intros m.
        induction m.
        - by autorewrite with ring_scope.
        - rewrite (expt_reorder a m 1).
          by rewrite Nat.add_1_r.
          simpl (a <^> 1).
          autorewrite with ring_scope.
          rewrite (mulrA b _ a).
          rewrite -IHm.
          rewrite -(mulrA _ b a).
          rewrite -abComm.
          by rewrite mulrA.
      }
      rewrite H.
      rewrite -(mulrA b _ _).
      rewrite (mulrA a b _).
      by rewrite IHn.
  Qed.


  Definition is_nonzero (a : R) := a <> 0.
  Definition is_ring_unit (a : R) := exists b, a * b = 1 /\ b * a = 1.
  Definition divRing := forall (a : R), is_nonzero a -> is_ring_unit a.

  Definition comRing := commutative (@mul R).

  Axiom thm_1_4_c : divRing -> forall (a b : R), a * b = 0 -> a = 0 \/ b = 0.

  (* C' and C'' and C''' are logically equivalent to C *)

  (* Every division ring satisfies C' *)
  Lemma thm_1_4_c' : forall (a b : R),
      divRing -> a <> 0 /\ b <> 0 -> a * b <> 0.
  Proof.
    intros a b divRingR abNK.
    destruct abNK.
    unfold not.
    intros.
    pose proof (thm_1_4_c divRingR a b H1).
    destruct H2; tauto.
  Qed.

  (* Every division ring satisfies C'' *)
  Lemma thm_1_4_c'' : forall (a b : R),
      divRing -> a * b = 0 -> a <> 0 -> b = 0.
  Proof.
    intros a b divRingR abCancel aNz.
    unfold divRing in divRingR.
    destruct (divRingR a aNz) as [x [axI xaI]].
    rewrite -(mul1r b).
    rewrite -xaI.
    rewrite -mulrA.
    rewrite abCancel.
    by autorewrite with ring_scope.
  Qed.

  (* Every division ring satisfies C''' *)
  Lemma thm_1_4_c''' : forall (a b : R),
      divRing -> a * b = 0 -> a <> 0 -> b = 0.
  Proof.
    intros a b divRingR abCancel aNz.
    unfold divRing in divRingR.
    destruct (divRingR a aNz) as [x [axI xaI]].
    rewrite -(mul1r b).
    rewrite -xaI.
    rewrite -mulrA.
    rewrite abCancel.
    by autorewrite with ring_scope.
  Qed.

  Lemma coll_1_3_1 : forall (a b : R),
      divRing -> is_nonzero a -> a * b = 0 -> b = 0.
  Proof.
    intros a b divRingR unitA abZ.
    unfold divRing in divRingR.
    destruct (divRingR a unitA) as [aInv [abI baI]].
    by apply thm_1_4_c'' with (a := a).
  Qed.

  Lemma coll_1_3 : forall (a b c : R),
      divRing -> is_nonzero a -> a * b = a * c -> b = c.
  Proof.
    intros a b c divRingR unitA abEqac.
    unfold divRing in divRingR.
    destruct (divRingR a unitA) as [aInv [abI baI]].
    rewrite -(mul1r b).
    rewrite -(mul1r c).
    rewrite -baI.
    rewrite -!mulrA.
    congruence.
  Qed.

  Definition C := forall (a b : R), a * b = 0 -> a = 0 \/ b = 0.

  Definition domain := comRing /\ C.

  Definition field := comRing /\ (forall (a : R), is_nonzero a -> is_ring_unit a).

  Theorem ring_K : C -> forall (a b c : R), a <> 0 -> a * b = a * c -> b = c.
  Proof.
    intros.
    unfold C in H.
    apply (f_equal (fun x => x + opp (a * c))) in H1.
    autorewrite with ring_scope in H1.
    rewrite -(thm_1_1_2_2_1 a c) in H1.
    rewrite -mulrDr in H1.
    pose proof (H a _ H1).
    destruct H2.
    - tauto.
    - apply (f_equal (fun x => x + c)) in H2.
      rewrite -addrA in H2.
      by autorewrite with ring_scope in H2.
  Qed.

  (* Exercise from homework *)
  Theorem hw5_P2 a : domain -> a * a = 1 -> a = 1 \/ a = opp 1.
  Proof.
    intros domR a2I.
    destruct domR.
    assert ((a + 1) * (a + opp 1) = 0).
    {
      rewrite !mulrDr.
      rewrite !mulrDl.
      autorewrite with ring_scope.
      rewrite -(addrA (a * a) a _).
      rewrite (addrA a (opp a) _).
      autorewrite with ring_scope.
      rewrite a2I.
      by autorewrite with ring_scope.
    }
    pose proof (H0 (a + 1) (a + opp 1) H1).
    destruct H2.
    - right. rewrite -(addrN a) in H2.
      apply (f_equal (fun x => opp a + x)) in H2.
      rewrite !addrA in H2.
      autorewrite with ring_scope in H2.
      rewrite H2.
      by autorewrite with ring_scope.
    - left. rewrite -(addrN a) in H2.
      apply (f_equal (fun x => opp a + x)) in H2.
      rewrite !addrA in H2.
      autorewrite with ring_scope in H2.
      apply (f_equal opp) in H2.
      autorewrite with ring_scope in H2.
      by symmetry.
  Qed.

  Definition divides {R : Ring.type} (a : R) (b : R) := exists c, a * c = b.

  Theorem hw6_2a (Rc : ComRing.type) (a b c : Rc) :
    divides a b -> divides b c -> divides a c.
  Proof.
    by move=> [d adb] [e be]; exists (d * e); rewrite mulrA adb.
  Qed.

  Theorem hw6_2b (a b c : R) :
    comRing -> divides a b -> is_ring_unit c -> divides (a * c) b.
  Proof.
    intros.
    unfold divides in *.
    unfold is_ring_unit in H1.
    destruct H0, H1.
    destruct H1.
    exists (x0 * x).
    subst.
    rewrite -(mulrA a c _).
    rewrite (mulrA c x0 _).
    rewrite H1.
    by autorewrite with ring_scope.
  Qed.

  (* if a|b and b|a for non-zero a, and R is a domain, then there
  exist units u and v in R, such that a = ub and b = va; *)

  Theorem hw6_2c (a b : R) :
    domain -> is_nonzero a -> divides a b -> divides b a
    ->  exists u v, a = u * b /\ b = v * a /\ is_ring_unit u /\ is_ring_unit v.
  Proof.
    intros.
    unfold divides in *.
    destruct H1, H2.
    subst.
    exists x0,  x.
    split.
    - destruct H.
      rewrite -H.
      by symmetry.
    - split.
      + apply (proj1 H).
      + unfold domain in H.
        rewrite -{2}(mulr1 a) in H2.
        rewrite -mulrA in H2.
        destruct H.
        eapply ring_K in H2; try auto.
        unfold is_ring_unit.
        pose proof H2.
        rewrite H in H3.
        split; try ((by exists x) || (by exists x0)).
  Qed.

  Theorem hw6_2d (Rc : ComRing.type) (a b c : Rc) :
    divides a b -> divides (a * c) (b * c).
  Proof.
    by move=> [x axb]; exists x; rewrite /divides -mulrA -(mulrC x c) mulrA axb.
  Qed.

  (* e) if ac|bc , R is a domain, and c ̸= 0, then a|b. *)
  Theorem hw6_2e (a b c : R) :
    divides (a * c) (b * c) -> domain -> is_nonzero c -> divides a b.
  Proof.
    intros divACBC domR nonZC.
    destruct divACBC.
    destruct domR.
    rewrite (H0 a c) in H.
    rewrite (H0 b c) in H.
    rewrite -mulrA in H.
    apply ring_K in H; try auto.
    by exists x.
  Qed.
End rings.
