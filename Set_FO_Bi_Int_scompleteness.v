Require Import Classical.
(* Used only in deciding whether a pair is derivable or not. *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import FO_Bi_Int_Syntax.
Require Import Set_FO_Bi_Int_calcs.
Require Import Set_FO_Bi_Int_logics.
Require Import Set_FO_Bi_Int_extens_interactions.
Require Import Set_FO_wBi_Int_meta_interactions.
Require Import Set_FO_sBi_Int_meta_interactions.
Require Import Set_FO_Bi_Int_Kripke_sem.
Require Import Set_FO_Bi_Int_enum.
Require Import Set_FO_Bi_Int_Lindenbaum_lem.
Require Import ListEnumerabilityFacts.
Require Import FO_strong_induction.
Require Import Set_FO_Bi_Int_wcompleteness.

Section sCompleteness.


  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.

(* Hypothesis encode0_inj : forall A B n, (encode0 A = n) -> (encode0 B = n) -> A = B. *)

Section DN_closure.

  Variable domain : Type.
  Variable M : (kmodel domain).

Fixpoint n_reachable (n: nat) w v: Prop :=
  match n with
  | 0 => w = v
  | S m => exists u, ((reachable u v) \/ (reachable v u)) /\ (n_reachable m w u)
  end.

Lemma n_reachable_refl : forall n w, (n_reachable n w w).
Proof.
induction n ; intros.
- simpl. auto.
- simpl. exists w. split. pose (reach_refl w). auto. auto.
Qed.

Lemma DN_form_DN : forall n A, (DN_form (S n) A) = (DN_form n (¬ (∞ A))).
Proof.
induction n.
- intros. simpl. auto.
- intros. simpl. pose (IHn A). rewrite <- e. simpl. auto.
Qed.

Lemma n_reachable_DN_clos : forall n rho w A,
  (ksat w rho (DN_form n A)) ->
    (forall v, (n_reachable  n w v) -> (ksat v rho A)).
Proof.
induction n.
- intros. simpl in H. inversion H0. subst. auto.
- intros. inversion H0. destruct H1. destruct H1.
  * pose (IHn rho w (¬ (∞ A))). pose (DN_form_DN n A). rewrite e in H.
    pose (k H x H2). simpl in k0. pose (k0 v H1).
    destruct (ksat_dec v rho A) ; auto. exfalso.
    apply f. exists v. split ; auto. split. apply reach_refl. auto.
  * pose (IHn rho w (¬ (∞ A))). pose (DN_form_DN n A). rewrite e in H.
    pose (k H x H2). simpl in k0. pose (k0 x).
    destruct (ksat_dec v rho A) ; auto. exfalso.
    apply f. apply reach_refl. exists v. split ; auto.
Qed.

Lemma DN_clos_DN_form : forall n Γ (A : form), (In _ Γ A) -> (In _ (DN_clos_set Γ) (DN_form n A)).
Proof.
induction n.
- intros. simpl. apply InitClo. auto.
- intros. simpl. apply IndClo. apply IHn. auto.
Qed.


Lemma DN_preserv_closed_form : forall n A, closed A -> closed (DN_form n A).
Proof.
induction n.
- intros. simpl. auto.
- intros. simpl. unfold closed. intros. unfold closed in H. repeat apply uf_bin.
  apply uf_top. apply IHn ; auto. apply uf_bot.
Qed.

Lemma In_DN_clos_set_DN_form : forall A Γ,
  In _ (DN_clos_set Γ) A -> (exists n B, In _ Γ B /\ A = DN_form n B).
Proof.
intros. induction H.
- exists 0. exists A ; split ; auto.
- destruct IHDN_clos_set. destruct H0. destruct H0 ; subst. exists (S x).
  exists x0. split ; auto.
Qed.

Lemma DN_clos_preserv_closed : forall Γ, closed_S Γ  -> closed_S (DN_clos_set Γ).
Proof.
intros. unfold closed_S in H. unfold closed_S. intros.
apply In_DN_clos_set_DN_form in H0. destruct H0. destruct H0. destruct H0. subst.
apply DN_preserv_closed_form. auto.
Qed.

End DN_closure.






Section pruned_model.

    Variable domain : Type.
    Variable M : kmodel domain.

Definition s_is_n_reachable s w : Prop :=
  exists n, @n_reachable domain M n s w.

Definition s_pruned_worlds s : Type :=
  { x | s_is_n_reachable s x}.

Definition s_pruned_relation s (w0 w1 : s_pruned_worlds s) : Prop :=
  reachable (proj1_sig w0) (proj1_sig w1).

Lemma s_R_refl s (u : s_pruned_worlds s) : (s_pruned_relation s) u u.
Proof.
unfold s_pruned_relation. apply reach_refl.
Qed.

Lemma s_R_trans s (u v w : s_pruned_worlds s) :
  ((s_pruned_relation s) u v) -> ((s_pruned_relation s) v w) -> ((s_pruned_relation s) u w).
Proof.
unfold s_pruned_relation. apply reach_tran.
Qed.

Lemma s_mon_P : forall s u v, (s_pruned_relation s) u v ->
  forall P (t : Vector.t domain (ar_preds P)), (fun x => k_P (proj1_sig x)) u P t -> (fun x => k_P (proj1_sig x)) v P t.
Proof.
intros. simpl. destruct v. simpl. destruct u. simpl in H0.
assert (reachable x0 x). auto. apply (mon_P H1). auto.
Qed.

Program Instance s_pruned_model s : kmodel domain :=
      {|
        nodes := (s_pruned_worlds s) ;
        reachable := (s_pruned_relation s) ;
        reach_refl u := s_R_refl s u ;
        reach_tran u v w := s_R_trans s u v w ;
        k_interp := k_interp (domain:=domain) ;
        k_P := fun C P v => k_P (proj1_sig C) v ;
        mon_P := (s_mon_P s)
      |}.

Theorem autosimulation s : forall A (w : s_pruned_worlds s) rho,
                (@ksat _ _ _ (s_pruned_model s) w rho A)   <->   (@ksat _ _ _ M (proj1_sig w) rho A).
Proof.
induction A ; intros. 1-3: split ; intro ; auto.
- destruct b ; split ; intro.
  1-2: simpl ; simpl in H ; destruct H ; split ; [ apply IHA1 ; auto | apply IHA2 ; auto].
  1-2: simpl ; simpl in H ; destruct H ; [ apply IHA1 in H ; auto | apply IHA2 in H ; auto].
  * simpl in H. simpl. intros.
    assert ((fun x => s_is_n_reachable s x) v). unfold s_is_n_reachable.
    destruct w. simpl in H0. destruct s0. exists (S x0). simpl. exists x ; auto.
    pose (@exist (nodes(domain:=domain)) (fun x => s_is_n_reachable s x) v H2).
    pose (IHA2 s0). assert (proj1_sig s0 = v). auto. rewrite H3 in i. apply i.
    apply IHA2. apply IHA2. apply H ; auto. apply IHA1. rewrite H3 ; auto.
  * simpl. simpl in H. intros. apply IHA2. apply H ; auto. apply IHA1 ; auto.
  * simpl. simpl in H. destruct H. destruct H. destruct H0. exists (proj1_sig x).
    repeat split ; auto. apply IHA1 ; auto. intro. apply H1. apply IHA2. auto.
  * simpl. simpl in H. destruct H. destruct H. destruct H0.
    assert ((fun x => s_is_n_reachable s x) x). unfold s_is_n_reachable.
    destruct w. simpl in H0. destruct s0. exists (S x1). simpl. exists x0 ; auto.
    pose (@exist (nodes(domain:=domain)) (fun x => s_is_n_reachable s x) x H2).
    exists s0. repeat split ; auto. apply IHA1. auto. intro. apply H1. apply IHA2 in H3. auto.
- destruct q.
  * split ; intro ; simpl ; intros ; simpl in H ; apply IHA ; auto.
  * split ; intro ; simpl ; intros ; simpl in H.
    + destruct H. apply IHA in H. exists x. auto.
    + destruct H. exists x. apply IHA. auto.
Qed.

End pruned_model.

Theorem sCounterCompleteness : forall (Γ Δ : @Ensemble form),
    (closed_S Γ) ->
    (closed_S Δ) ->
    (* Depending on the Lindenbaum lemma, delete the two above assumptions. *)
    (spair_der (Γ, Δ) -> False) ->
    ((glob_conseq Γ Δ) -> False).
Proof.
intros Γ Δ ClΓ ClΔ SD.
assert (J1: spair_der (DN_clos_set Γ, Δ) -> False).
intro. apply SD. unfold spair_der in H. unfold spair_der.
destruct H. destruct H. destruct H0. simpl in H0.
simpl in H1. exists x. repeat split ; auto. simpl.
pose (sFOBIC_comp _ H1 Γ). simpl in s. apply s. clear s. intros.
induction H2. apply Ids. apply IdRule_I. assumption.
apply DNs with (ps:=[(Γ, A)]). intros. inversion H3. subst. auto.
inversion H4. apply DNsRule_I.
assert (J2: wpair_der (DN_clos_set Γ, Δ) -> False).
intro. apply J1. apply pair_sFOBIC_extens_wFOBIC ; auto.
pose (DNClΓ:= DN_clos_preserv_closed _ ClΓ).
pose (wCounterCompleteness _ _ _ _ _ _ DNClΓ ClΔ J2).
intro. apply f. intro. intros. unfold glob_conseq in H.

pose (@exist (nodes(domain:=D)) (fun x => (s_is_n_reachable D M u) x) u).
assert (J4: s_is_n_reachable D M u u). unfold s_is_n_reachable. exists 0. simpl. auto.
pose (@exist (nodes(domain:=D)) (s_is_n_reachable D M u) u J4).

(* All formulae in Γ are globally true in the pruned canonical model. *)
assert (SAT: forall (w : (s_pruned_worlds D M u)) A, (In _ Γ A) ->
@ksat _ _ _ (s_pruned_model D M u) w rho A).
{ intros. apply autosimulation. destruct w. simpl.
  unfold s_is_n_reachable in s1. destruct s1.
  assert (J6: In form (DN_clos_set Γ) (DN_form x0 A)).
  apply DN_clos_DN_form ; auto.
  pose (H0 (DN_form x0 A) J6).
  pose (n_reachable_DN_clos _ _ _ _ _ _ k x). auto. }

assert (exists B : form, In form Δ B /\ (@ksat _ _ D (s_pruned_model D M u) s0 rho B)).
apply H. intros. apply SAT. auto. destruct H1. destruct H1. exists x. split. auto.
apply autosimulation in H2. auto.
Qed.

Theorem sCompleteness : forall (Γ Δ : @Ensemble form),
    (closed_S Γ) ->
    (closed_S Δ) ->
    (* Depending on the Lindenbaum lemma, delete the two above assumptions. *)
    (glob_conseq Γ Δ) ->
    spair_der (Γ, Δ).
Proof.
intros Γ Δ ClΓ ClΔ GC. pose (sCounterCompleteness Γ Δ).
pose (classic (spair_der (Γ, Δ))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.































Section pruned_Canon_model.

(* I can repeat the same argument using the canonical model, but as I am not sure
    about its shape, the result above is safer (if we have wCompleteness, in whatever
    way, then we get sCompleteness. *)


Definition s_C_is_n_reachable (s cp : Canon_worlds) : Prop :=
  exists n, @n_reachable term Canon_model n s cp.

Definition s_pruned_Canon_worlds (s : Canon_worlds) : Type :=
  { x : Canon_worlds | s_C_is_n_reachable s x}.

Definition s_pruned_Canon_relation (s : Canon_worlds) (cp0 cp1 : s_pruned_Canon_worlds s) : Prop :=
  Canon_relation (proj1_sig cp0) (proj1_sig cp1).

Lemma s_C_R_refl (s : Canon_worlds) (u : s_pruned_Canon_worlds s) : (s_pruned_Canon_relation s) u u.
Proof.
unfold s_pruned_Canon_relation.
intro. intros. assumption.
Qed.

Lemma s_C_R_trans (s : Canon_worlds) (u v w : s_pruned_Canon_worlds s) :
  ((s_pruned_Canon_relation s) u v) -> ((s_pruned_Canon_relation s) v w) -> ((s_pruned_Canon_relation s) u w).
Proof.
unfold s_pruned_Canon_relation.
intro. intros. unfold Canon_relation in H0. unfold Canon_relation in H.
unfold Canon_relation. intro. intros. apply H0. apply H. auto.
Qed.

Program Instance s_pruned_Canon_model (s : Canon_worlds) : kmodel term :=
      {|
        nodes := (s_pruned_Canon_worlds s) ;
        reachable := (s_pruned_Canon_relation s) ;
        k_interp := universal_interp ;
        k_P := fun C P v => In _ (fst (proj1_sig C)) (atom P v)
      |}.



Theorem autosimulation_C (s : Canon_worlds) : forall A (w : s_pruned_Canon_worlds s) rho,
                (@ksat _ _ _ (s_pruned_Canon_model s) w rho A)   <->   (@ksat _ _ _ Canon_model (proj1_sig w) rho A).
Proof.
induction A ; intros. 1-3: split ; intro ; auto.
- destruct b ; split ; intro.
  1-2: simpl ; simpl in H ; destruct H ; split ; [ apply IHA1 ; auto | apply IHA2 ; auto].
  1-2: simpl ; simpl in H ; destruct H ; [ apply IHA1 in H ; auto | apply IHA2 in H ; auto].
  * simpl in H. simpl. intros.
    assert ((fun x : Canon_worlds => s_C_is_n_reachable s x) v). unfold s_C_is_n_reachable.
    destruct w. simpl in H0. destruct s0. exists (S x0). simpl. exists x ; auto.
    pose (@exist (Canon_worlds) (fun x => s_C_is_n_reachable s x) v H2).
    pose (IHA2 s0). assert (proj1_sig s0 = v). auto. rewrite H3 in i. apply i.
    apply IHA2. apply IHA2. apply H ; auto. apply IHA1. rewrite H3 ; auto.
  * simpl. simpl in H. intros. apply IHA2. apply H ; auto. apply IHA1 ; auto.
  * simpl. simpl in H. destruct H. destruct H. destruct H0. exists (proj1_sig x).
    repeat split ; auto. apply IHA1 ; auto. intro. apply H1. apply IHA2. auto.
  * simpl. simpl in H. destruct H. destruct H. destruct H0.
    assert ((fun x : Canon_worlds => s_C_is_n_reachable s x) x). unfold s_C_is_n_reachable.
    destruct w. simpl in H0. destruct s0. exists (S x1). simpl. exists x0 ; auto.
    pose (@exist (Canon_worlds) (fun x => s_C_is_n_reachable s x) x H2).
    exists s0. repeat split ; auto. apply IHA1. auto. intro. apply H1. apply IHA2 in H3. auto.
- destruct q.
  * split ; intro ; simpl ; intros ; simpl in H ; apply IHA ; auto.
  * split ; intro ; simpl ; intros ; simpl in H.
    + destruct H. apply IHA in H. exists x. auto.
    + destruct H. exists x. apply IHA. auto.
Qed.

End pruned_Canon_model.


Theorem sCounterCompleteness_C : forall (Γ Δ : @Ensemble form),
    (closed_S Γ) ->
    (closed_S Δ) ->
    (* Depending on the Lindenbaum lemma, delete the two above assumptions. *)
    (spair_der (Γ, Δ) -> False) ->
    ((glob_conseq Γ Δ) -> False).
Proof.
intros Γ Δ ClΓ ClΔ SD.
assert (J1: spair_der (DN_clos_set Γ, Δ) -> False).
intro. apply SD. unfold spair_der in H. unfold spair_der.
destruct H. destruct H. destruct H0. simpl in H0.
simpl in H1. exists x. repeat split ; auto. simpl.
pose (sFOBIC_comp _ H1 Γ). simpl in s. apply s. clear s. intros.
induction H2. apply Ids. apply IdRule_I. assumption.
apply DNs with (ps:=[(Γ, A)]). intros. inversion H3. subst. auto.
inversion H4. apply DNsRule_I.
assert (J2: wpair_der (DN_clos_set Γ, Δ) -> False).
intro. apply J1. apply pair_sFOBIC_extens_wFOBIC ; auto.
apply Lindenbaum_lemma with (list_Funcs0:=list_Funcs) (list_Preds0:=list_Preds) in J2 ; auto.
2: apply DN_clos_preserv_closed ; auto.
destruct J2. destruct H. destruct H0. destruct H1. destruct H2. destruct H3.
assert (J3: ExAllCompNotDer x). unfold ExAllCompNotDer. auto.
pose (@exist (prod (Ensemble form) (Ensemble form)) ExAllCompNotDer x J3).
assert (J4: s_C_is_n_reachable s s). unfold s_C_is_n_reachable. exists 0. simpl. auto.
pose (@exist Canon_worlds (s_C_is_n_reachable s) s J4).

(* All formulae in Γ are globally true in the pruned canonical model. *)
assert (SAT: forall (cp : (s_pruned_Canon_worlds s)) A, (In _ Γ A) ->
@ksat _ _ _ (s_pruned_Canon_model s) cp var A).
{ intros. apply autosimulation_C. destruct cp. simpl.
  unfold s_C_is_n_reachable in s1. destruct s1.
  assert (J5: @ksat _ _ _ (Canon_model) s var (DN_form x1 A)).
  { pose (truth_lemma _ _ _ _ (size (DN_form x1 A)) (DN_form x1 A) s). apply i ; auto.
    simpl. apply H. apply DN_clos_DN_form. auto. }
  pose (n_reachable_DN_clos term Canon_model x1 var s _ J5 x0). apply k. auto. }


(* No formula in Δ is satisfied in s0 in the pruned canonical model. *)
assert (NotSAT: forall A, (In _ Δ A) ->
((@ksat _ _ _ (s_pruned_Canon_model s) s0 var A) -> False)).
{ intros. apply autosimulation_C in H6.
  pose (truth_lemma _ _ _ _ (size A) A (proj1_sig s0)). apply i in H6 ; auto.
  simpl in H6. apply H4. exists [A].
  repeat split. apply NoDup_cons ; auto ; apply NoDup_nil. intros.
  inversion H7. simpl. subst. apply H0. auto. inversion H8. simpl.
  apply MP with (ps:=[(fst x, A --> (A ∨ ⊥));(fst x, A)]). 2: apply MPRule_I.
  intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA2_I.
  exists A. exists ⊥. auto. inversion H8. subst. 2: inversion H9.
  apply Id. apply IdRule_I. auto. }

intro. unfold glob_conseq in H5.
assert (J6: (forall A, In form Γ A ->
forall (u : s_pruned_Canon_worlds s), @ksat _ _ _ (s_pruned_Canon_model s) u var A)).
{ intros. apply SAT ; auto. }

pose (H5 term (s_pruned_Canon_model s) var J6 s0). destruct e.
destruct H6. apply NotSAT with (A:=x0) ; auto.
Qed.

Theorem sCompleteness_C : forall (Γ Δ : @Ensemble form),
    (closed_S Γ) ->
    (closed_S Δ) ->
    (* Depending on the Lindenbaum lemma, delete the two above assumptions. *)
    (glob_conseq Γ Δ) ->
    spair_der (Γ, Δ).
Proof.
intros Γ Δ ClΓ ClΔ GC. pose (sCounterCompleteness_C Γ Δ).
pose (classic (spair_der (Γ, Δ))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.

End sCompleteness.
