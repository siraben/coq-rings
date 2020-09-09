Require Import Coq.Bool.Bool.
Require Import Nat.
Require Import PeanoNat.

Open Scope nat.

Set Implicit Arguments.

Section ring_definitions.
  Variable (A : Set).
  Definition is_assoc (f: A -> A -> A) := forall a b c,
    f (f a b) c = f a (f b c).

  Definition is_commutative (f: A -> A -> A) := forall a b, f a b = f b a.

  Definition is_inverse (f: A -> A -> A) (inv: A -> A) (z: A) :=
    forall a,  f a (inv a) = z /\ f (inv a) a = z.

  Definition is_unit (f: A -> A -> A) (z: A) := forall a, f a z = a /\ f z a = a.

  Definition add_monoid (add: A -> A -> A) (add_unit: A) :=
    (is_assoc add) /\ (is_unit add add_unit).

  Definition mul_monoid (mul: A -> A -> A) (mul_unit: A) :=
    (is_assoc mul) /\ (is_unit mul mul_unit).

  Definition is_ldistr (mul: A -> A -> A) (add: A -> A -> A) :=
    forall a b c, mul a (add b c) = add (mul a b) (mul a c).

  Definition is_rdistr  (mul: A -> A -> A) (add: A -> A -> A) :=
    forall a b c, mul (add a b) c = add (mul a c) (mul b c).

  Definition is_ring (add: A -> A -> A) (mul: A -> A -> A)
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
    intros a.
    assert (H: forall (x : R), x <+> x = x -> x = z).
    {
      intros x xAddx.
      rewrite <- xAddx.
      rewrite <- (add_inverse_r _ x).
      rewrite <- xAddx at 3.
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
    intros a.
    assert (H: forall (x : R), x <+> x = x -> x = z).
    {
      intros x xAddx.
      rewrite <- xAddx.
      rewrite <- (add_inverse_r _ x).
      rewrite <- xAddx at 3.
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
    intros a.
    assert (H: forall (x y : R), x <+> y = z -> y = inv x).
    {
      intros x y xyCancel.
      rewrite <- (add_unit_l _ (inv x)).
      rewrite <- xyCancel.
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
    intros a b.
    assert (H: forall (x y : R), x <+> y = z -> y = inv x).
    {
      intros x y xyCancel.
      rewrite <- (add_unit_r _ (inv x)).
      rewrite <- xyCancel.
      rewrite add_assoc.
      now autorewrite with ring_scope.
    }
    apply H.
    rewrite <- mul_ldistr.
    now autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_2_2_1 : ring_scope.

  Lemma thm_1_1_2_2_2 : forall (a b : R), inv a <*> b = inv (a <*> b).
  Proof.
    intros a b.
    assert (H: forall (x y : R), x <+> y = z -> y = inv x).
    {
      intros x y xyCancel.
      rewrite <- (add_unit_r _ (inv x)).
      rewrite <- xyCancel.
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
    intros a b; now autorewrite with ring_scope.
  Qed.

  Hint Rewrite thm_1_1_2_3 : ring_scope.

  Fixpoint expt (a : R) (n : nat) :=
    match n with
    | 0 => I
    | S n' => a <*> expt a n'
    end.

  Notation "x <^> y" := (expt x y) (at level 25, left associativity).

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
    induction n; simpl; now autorewrite with ring_scope.
  Qed.

  Hint Rewrite expt_I : ring_scope.

  Lemma thm_1_1_3_2 : forall (a : R) n m, a <^> n <^> m = a <^> (n * m).
  Proof.
    intros a n m.
    induction m; simpl.
    - now rewrite <- mult_n_O.
    - rewrite IHm. autorewrite with ring_scope.
      rewrite <- mult_n_Sm.
      now rewrite Nat.add_comm.
  Qed.

  Hint Rewrite thm_1_1_3_2 : ring_scope.

  Lemma expt_reorder : forall (a : R) n m o,
      n = m + o -> a <^> n = a <^> m <*> a <^> o.
  Proof.
    intros a n m o H.
    autorewrite with ring_scope. now rewrite <- H.
  Qed.
  
  Lemma thm_1_1_4 : forall (a b : R) n,
      a <*> b = b <*> a
      -> (a <*> b) <^> n = a <^> n <*> b <^> n.
  Proof.
    intros a b n abComm.
    induction n.
    - now autorewrite with ring_scope.
    - simpl.
      rewrite <- (mul_assoc _ a (a <^> n) _).
      rewrite (mul_assoc _ (a <^> n) _ _).
      assert (H: forall n, a <^> n <*> b = b <*> a <^> n).
      {
        intros m.
        induction m.
        - now autorewrite with ring_scope.
        - rewrite (expt_reorder a m 1).
          simpl (a <^> 1).
          autorewrite with ring_scope.
          rewrite (mul_assoc _ b _ a).
          rewrite <- IHm.
          rewrite <- (mul_assoc _ _ b a).
          rewrite <- abComm.
          now rewrite mul_assoc.
          symmetry.
          apply Nat.add_1_r.
      }
      rewrite H.
      rewrite <- (mul_assoc _ b _ _).
      rewrite (mul_assoc _ a b _).
      now rewrite IHn.
  Qed.


  Definition is_ring_unit {R : Ring} (a : R) := a <> z.
  Definition division_ring (R: Ring) :=
    forall (a : R), is_ring_unit a
               -> exists b, a <*> b = (I (r := R)) /\ b <*> a = (I (r := R)).

  Definition commutative_ring (R: Ring) := is_commutative (mul (r := R)).

  Axiom thm_1_4_c : forall (a b : R),
      division_ring R -> a <*> b = z -> a = z \/ b = z.

  (* Lemma thm_1_4_c' : forall (a b : R), *)
  (*     division_ring R -> a <> z /\ b <> z -> a <*> b <> z. *)
  (* Proof. *)
  (*   intros a b divRingR abNcancel. *)
  (*   destruct abNcancel. *)
  (*   unfold not. *)
  (*   intros. *)

  Lemma thm_1_4_c'' : forall (a b : R),
      division_ring R -> a <*> b = z -> a <> z -> b = z.
  Proof.
    intros a b divRingR abCancel aNz.
    unfold division_ring in divRingR.
    destruct (divRingR a aNz) as [x [axI xaI]].
    rewrite <- (mul_unit_l _ b).
    rewrite <- xaI.
    rewrite <- mul_assoc.
    rewrite abCancel.
    now autorewrite with ring_scope.
  Qed.

  Lemma thm_1_4_c''' : forall (a b : R),
      division_ring R -> a <*> b = z -> a <> z -> b = z.
  Proof.
    intros a b divRingR abCancel aNz.
    unfold division_ring in divRingR.
    destruct (divRingR a aNz) as [x [axI xaI]].
    rewrite <- (mul_unit_l _ b).
    rewrite <- xaI.
    rewrite <- mul_assoc.
    rewrite abCancel.
    now autorewrite with ring_scope.
  Qed.

  Lemma coll_1_3_1 : forall (a b : R),
      division_ring R -> is_ring_unit a -> a <*> b = z -> b = z.
  Proof.
    intros a b divRingR unitA abZ.
    unfold division_ring in divRingR.
    destruct (divRingR a unitA) as [aInv [abI baI]].
    apply thm_1_4_c'' with (a := a); easy.
  Qed.

  Lemma coll_1_3 : forall (a b c : R),
      division_ring R -> is_ring_unit a -> a <*> b = a <*> c -> b = c.
  Proof.
    intros a b c divRingR unitA abEqac.
    unfold division_ring in divRingR.
    destruct (divRingR a unitA) as [aInv [abI baI]].
    rewrite <- (mul_unit_l _ b).
    rewrite <- (mul_unit_l _ c).
    rewrite <- baI.
    rewrite <- !mul_assoc.
    congruence.
  Qed.

  Section subrings.
    Definition set (A : Set) := A -> bool.

    Definition is_mem (A: Set) (H: set A) (a : A) := H a = true.

    Arguments is_mem {A} _ _.

    Theorem is_mem_dec (A : Set) (H : set A) :
      forall a, { is_mem H a } +  { ~(is_mem H a) }.
      unfold is_mem. intros a.
      apply (bool_dec (H a)).
    Qed.

    Theorem is_mem_contradict (A : Set) (H : set A) :
      forall a, is_mem H a -> ~is_mem H a -> False.
      intros a; auto.
    Qed.

    Theorem is_mem_not (A : Set) (H : set A):
      forall a, ~is_mem H a <-> (H a) = false.
      intros a.
      unfold is_mem.
      rewrite <- not_true_iff_false.
      reflexivity.
    Qed.

    Structure subring (R : Ring) : Type := makeSubring
    {
      subring_mem :> set R;
      subring_I : is_mem subring_mem I;
      subring_closed_mul :
        forall a b, is_mem subring_mem a /\ is_mem subring_mem b
               -> is_mem subring_mem (a <*> b);
      subring_closed_add :
        forall a b, is_mem subring_mem a /\ is_mem subring_mem b
               -> is_mem subring_mem (a <+> b);
      subring_inverse :
        forall a, is_mem subring_mem a -> is_mem subring_mem (inv a)
    }.


    Lemma subring_closed1: forall (H: subring R) (a b : R),
        is_mem H a -> is_mem H b -> is_mem H (a <*> b).
    Proof.
      intros; now apply subring_closed_mul.
    Qed.

    Lemma subring_closed2: forall (H : subring R) (a b : R),
        is_mem H a -> is_mem H b -> is_mem H (b <*> a).
    Proof.
      intros; now apply subring_closed_mul.
    Qed.

    Lemma subring_closed3: forall (H: subring R) (a b : R),
        is_mem H a -> is_mem H b -> is_mem H (a <+> b).
    Proof.
      intros; now apply subring_closed_add.
    Qed.

    Lemma subring_closed4: forall (H : subring R) (a b : R),
        is_mem H a -> is_mem H b -> is_mem H (b <+> a).
    Proof.
      intros; now apply subring_closed_add.
    Qed.

  End subrings.

  Definition domain (R: Ring) := commutative_ring R
                              /\ division_ring R.


  (* Exercise from homework *)
  Theorem hw5_P2 : forall (a : R), domain R -> a <*> a = I -> a = I \/ a = inv I.
  Proof.
    intros a domR a2I.
    destruct domR.
    assert ((a <+> I) <*> (a <+> inv I) = z).
    {
      rewrite !mul_ldistr.
      rewrite !mul_rdistr.
      autorewrite with ring_scope.
      rewrite <- (add_assoc _ (a <*> a) a _).
      rewrite (add_assoc _ a (inv a) _).
      autorewrite with ring_scope.
      rewrite a2I.
      now autorewrite with ring_scope.
    }
    pose proof (thm_1_4_c (a <+> I) (a <+> inv I) H0 H1).
    destruct H2.
    - right. rewrite <- (add_inverse_r _ a) in H2.
      apply (f_equal (fun x => inv a <+> x)) in H2.
      rewrite !add_assoc in H2.
      autorewrite with ring_scope in H2.
      rewrite H2.
      now autorewrite with ring_scope.
    - left. rewrite <- (add_inverse_r _ a) in H2.
      apply (f_equal (fun x => inv a <+> x)) in H2.
      rewrite !add_assoc in H2.
      autorewrite with ring_scope in H2.
      apply (f_equal inv) in H2.
      autorewrite with ring_scope in H2.
      now symmetry.
  Qed.
    
End rings.
