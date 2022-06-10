(* * First-Order Logic *)


Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
Require Import ListAutomation.
Import ListAutomationNotations.

From Coq Require Import Eqdep_dec.
Require Import Coq.Vectors.Vector.
Local Notation vec := t.

Require Export FO_Bi_Int_Syntax.

Set Default Proof Using "Type".

(* ** Discreteness *)

Require Import EqdepFacts.

Lemma inj_pair2_eq_dec' A :
  eq_dec A -> forall (P : A -> Type) (p : A) (x y : P p), existT P p x = existT P p y -> x = y.
Proof.
  apply Eqdep_dec.inj_pair2_eq_dec.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2;
                                                      [subst | try (eauto || now intros; decide equality)]
  end.

Lemma dec_vec_in X n (v : vec X n) :
  (forall x, vec_in x v -> forall y, dec (x = y)) -> forall v', dec (v = v').
Proof with subst; try (now left + (right; intros[=])).
  intros Hv. induction v; intros v'.
  - pattern v'. apply Vector.case0...
  - apply (Vector.caseS' v'). clear v'. intros h0 v'.
    destruct (Hv h (vec_inB h v) h0)... edestruct IHv.
    + intros x H. apply Hv. now right.
    + left. f_equal. apply e.
    + right. intros H. inversion H. resolve_existT. tauto.
Qed.

#[global]
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
  intros v. refine (dec_vec_in _ _ _ _).
Qed.

Section EqDec.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.
  Hypothesis eq_dec_binop : eq_dec binop.
  Hypothesis eq_dec_quantop : eq_dec quantop.

  Global Instance dec_term : eq_dec term.
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence))
    using eq_dec_Funcs.
    intros t. induction t as [ | ]; intros [|? v']...
    - decide (x = n)... 
    - decide (F = f)... destruct (dec_vec_in _ _ _ X v')...
  Qed.

End EqDec.



(* ** Enumerability *)

Section Enumerability.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.

  Variable list_binop : nat -> list binop.
  Hypothesis enum_binop' : list_enumerator__T list_binop binop.

  Variable list_quantop : nat -> list quantop.
  Hypothesis enum_quantop' : list_enumerator__T list_quantop quantop.

  Fixpoint vecs_from X (A : list X) (n : nat) : list (vec X n) :=
    match n with
    | 0 => [Vector.nil X]
    | S n => [ Vector.cons X x _ v | (x,  v) ∈ (A × vecs_from X A n) ]
    end.

  Fixpoint L_term n : list term :=
    match n with
    | 0 => []
    | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from _ (L_term n) (ar_syms F) ] | F ∈ L_T n])
    end.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma list_prod_in X Y (x : X * Y) A B :
    x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
  Proof.
    induction A; cbn.
    - intros [].
    - intros [H | H] % in_app_or. 2: firstorder.
      apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
  Qed.

  Lemma vecs_from_correct X (A : list X) (n : nat) (v : vec X n) :
    (forall x, vec_in x v -> x el A) <-> v el vecs_from X A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. pattern v. now apply Vector.case0.
      + intros [<- | []] x H. inv H.
    - split.
      + intros. revert H. apply (Vector.caseS' v).
        clear v. intros ? t0 H. in_collect (pair h t0); destruct (IHn t0).
        eauto using vec_inB. apply H0. intros x Hx. apply H. now right. 
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        intros x H. inv H; destruct (IHn v'); eauto. apply H2; trivial. now resolve_existT.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) :
    cumulative L -> (forall x, vec_in x v -> exists m, x el L m) -> exists m, v el vecs_from _ (L m) n.
  Proof.
    intros HL Hv. induction v; cbn.
    - exists 0. tauto.
    - destruct IHv as [m H], (Hv h) as [m' H']. 1,3: eauto using vec_inB.
      + intros x Hx. apply Hv. now right.
      + exists (m + m'). in_collect (pair h v). 1: apply (cum_ge' (n:=m')); intuition lia.
      apply vecs_from_correct. rewrite <- vecs_from_correct in H. intros x Hx.
      apply (cum_ge' (n:=m)). all: eauto. lia.
  Qed.

  Lemma enum_term :
    list_enumerator__T L_term term.
  Proof with try (eapply cum_ge'; eauto; lia).
    intros t. induction t using term_rect.
    - exists (S x); cbn; eauto.
    - apply vec_forall_cml in H as [m H]. 2: exact L_term_cml. destruct (el_T F) as [m' H'].
      exists (S (m + m')); cbn. in_app 3. eapply in_concat_iff. eexists. split. 2: in_collect F...
      apply in_map. rewrite <- vecs_from_correct in H |-*. intros x H''. specialize (H x H'')...
  Qed.

  Lemma enumT_term :
    enumerable__T term.
  Proof using enum_Funcs'.
    apply enum_enumT. exists L_term. apply enum_term.
  Qed.

  Fixpoint L_form n : list form :=
    match n with
    | 0 => [⊥;⊤]
    | S n => L_form n
              ++ concat ([ [ atom P v | v ∈ vecs_from _ (L_term n) (ar_preds P) ] | P ∈ L_T n])
              ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ L_T n])
              ++ concat ([ [ quant op phi | phi ∈ L_form n ] | op ∈ L_T n])
    end.

  Lemma L_form_cml :
    cumulative L_form.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma enum_form :
    list_enumerator__T L_form form.
  Proof with (try eapply cum_ge'; eauto; lia).
    intros phi. induction phi.
    - exists 1. cbn; eauto.
    - exists 1. cbn; eauto.
    - rename t into v. destruct (el_T P) as [m Hm], (vec_forall_cml term L_term _ v) as [m' Hm']; eauto using enum_term.
      exists (S (m + m')); cbn. in_app 2. eapply in_concat_iff. eexists. split.
      2: in_collect P... eapply in_map. rewrite <- vecs_from_correct in *. intuition...
    - destruct (el_T b) as [m Hm], IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m + m1 + m2). cbn.
      in_app 3. apply in_concat. eexists. split. apply in_map... in_collect (pair phi1 phi2)...
    - destruct (el_T q) as [m Hm], IHphi as [m' Hm']. exists (1 + m + m'). cbn -[L_T].
      in_app 4. apply in_concat. eexists. split. apply in_map... in_collect phi...
  Qed.

  Lemma enumT_form :
    enumerable__T form.
  Proof using enum_Funcs' enum_Preds' enum_binop' enum_quantop'.
    apply enum_enumT. exists L_form. apply enum_form.
  Defined.

End Enumerability.
