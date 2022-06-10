Require Import List.
Require Import FO_Bi_Int_Syntax.
Require Import Set_FO_Bi_Int_calcs.
Require Import Set_FO_Bi_Int_Kripke_sem.
Require Import Classical.
Require Import Ensembles.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

(* ** Soundness **)

Section KSoundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Lemma Ax_valid : forall A, BIAxioms A -> kvalid A.
Proof.
intros A AX. inversion AX.
- destruct H ; destruct H ; destruct H ; subst. unfold RA1 ; cbn. unfold kvalid. intros. simpl ; intros.
  apply H2 ; auto. apply H0 ; auto. apply (reach_tran H1 H3).
- destruct H ; destruct H ; subst ; simpl. intro. intros. unfold RA2 ; cbn. intros. auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. auto.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. destruct H4.
  apply H0 ; auto. apply (reach_tran H1 H3). apply H2 ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct H0 ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct H0 ; auto.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. split. apply H0 ; auto.
  apply (reach_tran H1 H3). apply H2 ; auto.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. destruct H2.
  pose (H0 _ H1 H2). apply k ; auto. apply reach_refl.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. apply H0.
  apply (reach_tran H1 H3). split ; auto. apply ksat_mon with (u0:=v0) ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply H0 in H4.
  apply (H2 _ H3 H4). apply (reach_tran H1 H3).
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros.
  destruct (classic (rho ⊩( v) x0)) ; auto. right. exists v. repeat split ; auto. apply reach_refl.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct H0. destruct H0.
  destruct H1. exists x1. repeat split ; auto. intros. apply H2. apply H3 ; auto. apply reach_refl.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. destruct H0. destruct H0.
  destruct H1. destruct H0. destruct H0. destruct H3. exists x3. repeat split ; auto. apply (reach_tran H3 H1).
  intro. destruct H5. apply H4 ; auto. apply H2. apply (ksat_mon H3 H5).
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct (classic (rho ⊩( v0) x0)) ; auto.
  exfalso. apply (H0 _ H1). exists v0 ; repeat split ; auto. apply reach_refl.
- destruct H ; subst ; simpl. intro. intros. cbn. intros. apply I.
- destruct H ; subst ; simpl. intro. intros. cbn. intros. inversion H0.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply H0 ; auto.
  apply ksat_comp. auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply ksat_comp.
  unfold funcomp. eapply (ksat_ext v). 2: eapply (H0 (eval rho x0)). intros. unfold scons. destruct x1 ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply ksat_comp in H0.
  eexists (eval rho x0). eapply (ksat_ext v). 2: eapply H0. unfold funcomp. intros. unfold scons. destruct x1 ; auto.
Qed.


(*   Ltac clean_ksoundness :=
    match goal with
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H)
    end. *)

Lemma wSoundness0 : forall s, wFOBIC_rules s -> kvalid_ctx (fst s) (snd s).
Proof.
intros s Hprv. induction Hprv; subst; cbn; intros D M u rho HX.
(* Id *)
- inversion H. subst. apply HX ; auto.
(* Ax *)
- inversion H ; subst. apply Ax_valid ; auto.
(* MP *)
- inversion H1. subst. simpl.
  assert (J1: kvalid_ctx Γ (A --> B)). apply (H0 (Γ, A --> B)). apply in_eq.
  assert (J2: kvalid_ctx Γ A). apply (H0 (Γ, A)). apply in_cons ; apply in_eq.
  simpl in HX. unfold kvalid_ctx in J1,J2. pose (J1 _ _ _ _ HX). pose (J2 _ _ _ _ HX).
  simpl in k. apply k ; auto. apply reach_refl.
(* DNw *)
- inversion H1. subst. simpl. intros. destruct H3. destruct H3. destruct H4.
  assert (J1: kvalid_ctx (Empty_set _) A). apply (H0 (Empty_set _, A)). apply in_eq.
  simpl in HX. unfold kvalid_ctx in J1.
  assert (J2: forall psi : form, In _ (Empty_set _) psi -> rho ⊩( x) psi). intros. inversion H6.
  pose (J1 _ _ x _ J2). apply H5. auto.
(* Gen *)
- inversion H1. subst. simpl in HX. simpl. intros.
  assert (J1: kvalid_ctx (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) A).
  apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A)). apply in_eq.
  unfold kvalid_ctx in J1. apply J1. intros. inversion H2. destruct H3. subst.
  apply HX in H4. apply ksat_comp. simpl. unfold funcomp. simpl. auto.
(* EC *)
- inversion H1. subst. simpl in HX. simpl. intros.
  assert (J1: kvalid_ctx (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) (A --> B[↑])).
  apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑])). apply in_eq.
  unfold kvalid_ctx in J1. destruct H3.
  assert (J2: (forall psi : form, In _ (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) psi -> (x .: rho) ⊩( u) psi)). intros.
  destruct H4. destruct H4. subst. apply HX in H5. apply ksat_comp.
  simpl. unfold funcomp. simpl. auto. pose (J1 _ _ u (x .: rho) J2). simpl in k. apply k in H3 ; auto.
  apply ksat_comp in H3. unfold funcomp in H3. simpl in H3. auto.
Qed.

Lemma wSoundness1 : forall s, wFOBIC_rules s -> loc_conseq (fst s) (fun x => x = (snd s)).
Proof.
intros. apply wSoundness0 in H. destruct s. simpl ; simpl in H. intro. unfold kvalid_ctx in H.
intros. exists f. split ; auto. unfold In. auto.
Qed.

Lemma wSoundnessThm (A : form) : wFOBIC_rules (Empty_set _, A) -> kvalid A.
Proof.
intros. apply wSoundness0 in H. simpl in H. unfold kvalid_ctx in H. unfold kvalid. intros.
apply H. intros. inversion H0.
Qed.

Lemma list_disj_witn : forall D (M : kmodel D) u rho l,
    (ksat u rho (list_disj l)) -> (exists A, (List.In A l) /\ (ksat u rho A)).
Proof.
induction l.
- simpl. intros. inversion H.
- simpl. intros. destruct H.
  * exists a. split. apply in_eq. assumption.
  * apply IHl in H. destruct H. destruct H. exists x. split ; try assumption. apply in_cons ; auto.
Qed.

Theorem wSoundness : forall Γ Δ, wpair_der (Γ, Δ) -> (loc_conseq Γ Δ).
Proof.
intros Γ Δ wpair. destruct wpair. simpl in H. destruct H. destruct H0.
apply wSoundness1 in H1. simpl in H1. intro. intros. unfold loc_conseq in H1.
pose (H1 _ _ _ _ H2). destruct e. destruct H3. inversion H3. subst.
induction x.
- simpl in H0. exfalso. simpl in H4. inversion H4.
- simpl in IHx. simpl in H4. simpl in H3. simpl in H1. destruct H4.
  * exists a. split. apply H0. apply in_eq. auto.
  * apply list_disj_witn in H4. destruct H4. destruct H4. exists x0. split.
    apply H0. apply in_cons ; auto. auto.
Qed.

Theorem sSoundness1 :  forall s, sFOBIC_rules s -> glob_conseq (fst s) (fun x => x = (snd s)).
Proof.
intros s Hprv. induction Hprv; subst; cbn ; intros D M HX u rho.
(* Ids *)
- inversion H. subst ; simpl in HX ; simpl. exists A ; split ; auto. unfold In ; auto.
(* Axs *)
- inversion H ; subst ; simpl. exists A ; split ; auto. unfold In ; auto. apply Ax_valid ; auto.
(* MPs *)
- inversion H1. subst ; simpl in HX ; simpl. exists B ; split ; auto. unfold In ; auto.
  assert (J1: glob_conseq Γ (fun x => x = (A --> B))). apply (H0 (Γ, A --> B)). apply in_eq.
  assert (J2: glob_conseq Γ (fun x => x = A)). apply (H0 (Γ, A)). apply in_cons ; apply in_eq.
  unfold glob_conseq in J1,J2. pose (J1 _ _ HX u rho). pose (J2 _ _ HX u rho).
  destruct e. destruct e0. destruct H2. destruct H3. inversion H2 ; subst.
  inversion H3. subst. apply H4 ; auto. apply reach_refl.
(* DNs *)
- inversion H1. subst ; simpl in HX ; simpl. exists (¬ (∞ A)) ; split ; auto. unfold In ; auto. simpl. intros.
  destruct H3. destruct H3. destruct H4.
  assert (J1: glob_conseq Γ (fun x => x = A)). apply (H0 (Γ, A)). apply in_eq.
  unfold glob_conseq in J1.
  assert (J2: forall A : form, In form Γ A -> forall (u : nodes (domain:=D)) (rho : nat -> D), rho ⊩( u) A). intros.
  auto. pose (J1 _ _ J2 x rho). destruct e. destruct H6. inversion H6 ; subst. auto.
(* Gens *)
- inversion H1. subst; simpl in HX ; simpl. exists (∀ A) ; split ; auto. unfold In ; auto. intro.
  assert (J1: glob_conseq (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) (fun x => x = A)). apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A)). apply in_eq.
  unfold glob_conseq in J1.
  assert (J2: forall A : form,
      In form (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) A -> forall (u : nodes (domain:=D)) (rho : nat -> D), rho ⊩( u) A).
  intros. destruct H2. destruct H2. subst.
  pose (HX _ H3 u0). apply ksat_comp. simpl. unfold funcomp. simpl. auto.
  pose (J1 _ _ J2 u (j .: rho)). destruct e. destruct H2. inversion H2 ; subst ; auto.
(* ECs *)
- inversion H1. subst ; simpl in HX ; simpl. exists ((∃ A) --> B) ; split ; auto. unfold In ; auto. cbn ; intros.
  assert (J1: glob_conseq (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) (fun x => x = (A --> B[↑]))). apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑])). apply in_eq.
  unfold glob_conseq in J1. destruct H3.
  assert (J2: forall A : form, In form (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) A -> forall (u : nodes (domain:=D)) (rho : nat -> D), rho ⊩( u) A). intros.
  destruct H4. destruct H4. subst. pose (HX _ H5 u0). apply ksat_comp.
  simpl. unfold funcomp. simpl. auto. pose (J1 _ _ J2 u (x .: rho)). simpl in e. destruct e. destruct H4. inversion H4. subst.
  simpl in H5. pose (H5 _ H2 H3). apply ksat_comp in k. unfold funcomp in k. simpl in k. auto.
Qed.

Theorem sSoundness : forall Γ Δ, spair_der (Γ, Δ) -> (glob_conseq Γ Δ).
Proof.
intros Γ Δ gpair. destruct gpair. simpl in H. destruct H. destruct H0.
apply sSoundness1 in H1. simpl in H1. intro. intros.
induction x.
- simpl in H1. exfalso. simpl in H0.
  assert (J1: forall A : form, In form Γ A -> forall (u0 : nodes (domain:=D)) (rho0 : nat -> D), rho0 ⊩( u0) A).
  intros. apply H2. auto. pose (H1 _ _ J1 u rho). destruct e. destruct H3.
  inversion H3 ; subst. auto.
- assert (J1: forall A : form, In form Γ A -> forall (u0 : nodes (domain:=D)) (rho0 : nat -> D), rho0 ⊩( u0) A).
  intros. apply H2. auto.
  pose (H1 _ _ J1 u rho). destruct e. destruct H3. inversion H3. subst.
  simpl in H3. simpl in H4. destruct H4.
  * exists a. split. apply H0. apply in_eq. assumption.
  * apply list_disj_witn in H4. destruct H4. destruct H4. exists x0. split ; auto.
    apply H0. apply in_cons. assumption.
Qed.

End KSoundness.
