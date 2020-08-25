Require Import Nat.
Require Import PeanoNat.

Open Scope nat.

Set Implicit Arguments.

Section ring_definitions.
  Definition is_assoc (A: Set) (f: A -> A -> A) := forall a b c,
    f (f a b) c = f a (f b c).

  Definition is_commutative (A: Set) (f: A -> A -> A) := forall a b, f a b = f b a.

  Definition is_inverse (A: Set) (f: A -> A -> A) (inv: A -> A) (z: A) :=
    forall a,  f a (inv a) = z /\ f (inv a) a = z.

  Definition is_unit (A: Set) (f: A -> A -> A) (z: A) := forall a, f a z = a /\ f z a = a.

  Definition add_monoid (A: Set) (add: A -> A -> A) (add_unit: A) :=
    (is_assoc add) /\ (is_unit add add_unit).

  Definition mul_monoid (A: Set) (mul: A -> A -> A) (mul_unit: A) :=
    (is_assoc mul) /\ (is_unit mul mul_unit).

  Definition is_ldistr (A : Set) (mul: A -> A -> A) (add: A -> A -> A) :=
    forall a b c, mul a (add b c) = add (mul a b) (mul a c).

  Definition is_rdistr (A : Set) (mul: A -> A -> A) (add: A -> A -> A) :=
    forall a b c, mul (add a b) c = add (mul a c) (mul b c).

  Definition is_ring (A: Set) (add: A -> A -> A) (mul: A -> A -> A)
             (inv: A -> A) (add_unit: A) (mul_unit : A) :=
      add_monoid add add_unit
    /\ mul_monoid mul mul_unit
    /\ is_inverse add inv add_unit
    /\ is_commutative add
    /\ is_rdistr mul add
    /\ is_ldistr mul add.
    
End ring_definitions.

Section rings.
  Structure Ring : Type := makeRing
    {
      A :> Set;

      add : A -> A -> A ;
      mul : A -> A -> A ;
      inv : A -> A ;
      z : A;
      I : A;

      add_assoc : forall a b c, add a (add b c) = add (add a b) c;
      add_unit_l : forall a, add z a = a;
      add_unit_r : forall a, add a z = a;
      add_inverse_l : forall a, add (inv a) a = z;
      add_inverse_r : forall a, add a (inv a) = z;
      add_comm : forall a b, add a b = add b a;
      
      mul_assoc : forall a b c, mul a (mul b c) = mul (mul a b) c;
      mul_unit_l : forall a, mul I a = a;
      mul_unit_r : forall a, mul a I = a;
      mul_ldistr : forall a b c, mul a (add b c) = add (mul a b) (mul a c);
      mul_rdistr : forall a b c, mul (add a b) c = add (mul a c) (mul b c);
    }.

  Arguments z {r}.
  Arguments I {r}.
  Arguments add {r} _ _.
  Arguments mul {r} _ _.
  Arguments inv {r} _.

  Notation "x <+> y" := (add x y) (at level 50, left associativity).
  Notation "x <*> y" := (mul x y) (at level 40, left associativity).
  Variable (R : Ring).

  Hint Rewrite add_inverse_l add_inverse_r add_unit_l add_unit_r : ring_scope.
  Hint Rewrite mul_unit_l mul_unit_r : ring_scope.

  Lemma thm_1_1_1_1 : forall (a : R), z <*> a = z.
  Proof.
    intros.
    assert (forall (x : R), x <+> x = x -> x = z).
    {
      intros.
      rewrite <- H.
      rewrite <- (add_inverse_r _ x).
      rewrite <- H at 3.
      rewrite <- add_assoc.
      rewrite (add_inverse_r R x).
      now autorewrite with ring_scope.
    }
    apply H.
    rewrite <- mul_rdistr.
    now autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_1_1 : ring_scope.

  Lemma thm_1_1_1_2 : forall (a : R), a <*> z = z.
    intros.
    assert (forall (x : R), x <+> x = x -> x = z).
    {
      intros.
      rewrite <- H.
      rewrite <- (add_inverse_r _ x).
      rewrite <- H at 3.
      rewrite <- add_assoc.
      rewrite (add_inverse_r R x).
      now autorewrite with ring_scope.
    }
    apply H.
    rewrite <- mul_ldistr.
    now autorewrite with ring_scope.
  Qed.
  
  Hint Rewrite thm_1_1_1_2 : ring_scope.

  Lemma thm_1_1_2_1 : forall (a : R), inv (inv a) = a.
  Proof.
    intros.
    assert (forall (x y : R), x <+> y = z -> y = inv x).
    {
      intros.
      rewrite <- (add_unit_l _ (inv x)).
      rewrite <- H.
      rewrite (add_comm _ x y).
      rewrite <- add_assoc.
      now autorewrite with ring_scope.
    }
    symmetry.
    apply H.
    now autorewrite with ring_scope.
  Qed.
  
  Hint Rewrite thm_1_1_2_1 : ring_scope.

  Lemma thm_1_1_2_2_1 : forall (a b : R), a <*> (inv b) = inv (a <*> b).
  Proof.
    intros.
    assert (forall (x y : R), x <+> y = z -> y = inv x).
    {
      intros.
      rewrite <- (add_unit_r _ (inv x)).
      rewrite <- H.
      rewrite add_assoc.
      now autorewrite with ring_scope.
    }
    apply H.
    rewrite <- (mul_ldistr).
    now autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_2_2_1 : ring_scope.

  Lemma thm_1_1_2_2_2 : forall (a b : R), inv a <*> b = inv (a <*> b).
  Proof.
    intros.
    assert (forall (x y : R), x <+> y = z -> y = inv x).
    {
      intros.
      rewrite <- (add_unit_r _ (inv x)).
      rewrite <- H.
      rewrite add_assoc.
      now autorewrite with ring_scope.
    }
    apply H.
    rewrite <- mul_rdistr.
    now autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_2_2_2 : ring_scope.

  Lemma thm_1_1_2_3 : forall (a b : R), inv a <*> inv b = a <*> b.
  Proof.
    intros.
    now autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_2_3 : ring_scope.

  Fixpoint expt (a : R) (n : nat) :=
    match n with
    | 0 => I
    | S n' => a <*> expt a n'
    end.

  Lemma thm_1_1_3_1 : forall (a : R) n m, expt a n <*> expt a m = expt a (n + m).
  Proof.
    intros a n.
    induction n; intros; simpl.
    - now autorewrite with ring_scope.
    - rewrite <- mul_assoc. now rewrite IHn.
  Qed.

  Hint Rewrite thm_1_1_3_1 : ring_scope.

  Lemma expt_I : forall n, expt I n = I.
  Proof.
    induction n.
    - easy.
    - simpl. now autorewrite with ring_scope.
  Qed.

  Hint Rewrite expt_I : ring_scope.

  Lemma thm_1_1_3_2 : forall (a : R) n m, expt (expt a n) m = expt a (n * m).
  Proof.
    intros a n m.
    induction m; simpl.
    - now rewrite <- mult_n_O.
    - rewrite IHm. autorewrite with ring_scope.
      rewrite <- mult_n_Sm.
      now rewrite Nat.add_comm.
  Qed.

  Hint Rewrite thm_1_1_3_2 : ring_scope.

End rings.
