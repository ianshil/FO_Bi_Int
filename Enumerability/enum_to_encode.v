Require Import ConstructiveEpsilon.

Definition eq_dec X :=
  forall (x y : X), { x = y } + { x <> y }.

Section Inj.

  Variable X : Type.
  Hypothesis Xeq : eq_dec X.

  Variable f : nat -> X.
  Hypothesis Hf : forall x, exists n, f n = x.

  Definition f_inv :
    X -> nat.
  Proof.
    intros x. specialize (Hf x).
    apply constructive_indefinite_ground_description_nat in Hf as [n H].
    - exact n.
    - intros n. apply Xeq.
  Defined.

  Lemma f_inv_inj x x' :
    f_inv x = f_inv x' -> x = x'.
  Proof.
    unfold f_inv. repeat destruct constructive_indefinite_ground_description_nat. congruence.
  Qed.

End Inj.


