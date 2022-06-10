Require Import ListEnumerabilityFacts.
Require Import FO_Bi_Int_Syntax.
Require Import Syntax_facts.

Require Import Lia.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Classical.

Require Import ConstructiveEpsilon.

Require Import enum_to_encode.

Section Enumeration.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(* Below is what I initially did: assume the existence of an encoding. *)

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.





Section Option.

Lemma eq_dec_option_form : forall (x y : option form),  {x = y} + {x <> y}.
Proof.
intros. destruct x ; destruct y ; auto. 2-3: right ; intro ; inversion H.
destruct (eq_dec_form f f0). subst. left ; auto. right. intro. inversion H. auto.
Qed.

Variable f : nat -> option form.
Hypothesis Hf : forall x, exists n, f n = Some x.

Definition f_unoption :
  nat -> form.
Proof.
  intros x. remember (f x) as opt. destruct opt.
  - exact f0.
  - exact bot.
Defined.

Lemma f_unoption_surj :
  forall x, exists n, f_unoption n = x.
Proof.
unfold f_unoption. intros. pose (Hf x). destruct e. exists x0. destruct (f x0). inversion H ; auto.
inversion H.
Qed.

End Option.






Section Encoding_Existence.

Definition list_binop_BI (n : nat) : list binop :=
  match n with
        | 0 => (Conj :: nil)
        | 1 => (Disj :: nil)
        | 2 => (Impl :: nil)
        | 3 => (Excl :: nil)
        | S (S (S (S n))) => (Conj :: nil)
        end.

Lemma enum_binop_BI' : list_enumerator__T list_binop_BI binop.
Proof.
unfold list_enumerator__T. intros. destruct x.
- exists 0 ; simpl ; auto.
- exists 1 ; simpl ; auto.
- exists 2 ; simpl ; auto.
- exists 3 ; simpl ; auto.
Qed.

Definition list_quantop_BI (n : nat) : list quantop :=
  match n with
        | 0 => (All :: nil)
        | 1 => (Ex :: nil)
        | S (S n) => (All :: nil)
        end.

Lemma enum_quantop_BI' : list_enumerator__T list_quantop_BI quantop.
Proof.
unfold list_enumerator__T. intros. destruct x.
- exists 0 ; simpl ; auto.
- exists 1 ; simpl ; auto.
Qed.

Lemma surj_fun_option_surj_fun : (exists (x0 : nat -> option form), forall f : form, exists n : nat, x0 n = Some f) ->
  (exists (x1 : nat -> form), forall f : form, exists n : nat, x1 n = f).
Proof.
intros. destruct H.
pose (f_unoption x). exists f. apply f_unoption_surj. auto.
Qed.

Lemma exists_encoding :  exists (z : form -> nat), (forall A B n, (z A = n) -> (z B = n) -> A = B).
Proof.
pose (enumT_form list_Funcs enum_Funcs' list_Preds enum_Preds'
list_binop_BI enum_binop_BI' list_quantop_BI enum_quantop_BI').
destruct e. unfold EnumerabilityFacts.enumerator__T' in H.
assert (J1: (exists x : nat -> option form, forall f : form, exists n : nat, x n = Some f)).
exists x ; auto.
pose (surj_fun_option_surj_fun J1). destruct e.
pose (f_inv form eq_dec_form x0 H0). exists n.
pose (f_inv_inj _ eq_dec_form x0 H0). intros. subst. auto.
Qed.

End Encoding_Existence.










(* Now I can safely assume the existence of the following encoding
    given the lemma exists_encoding. *)

Variable encode0 : form -> nat.
Hypothesis encode0_inj : forall (A B : form) (n0 : nat), encode0 A = n0 -> encode0 B = n0 -> A = B.

(* Definition encode0 := proj1_sig exists_encoding. *)

Definition encode : form -> nat := fun x => S (encode0 x).

Lemma encode_no_0 : forall A, (encode A = 0) -> False.
Proof.
intros. unfold encode in H. lia.
Qed.

Lemma encode_inj : forall A B n, (encode A = n) -> (encode B = n) -> A = B.
Proof.
intros. unfold encode in H. unfold encode in H0.
destruct n. exfalso. lia. inversion H. inversion H0. subst.
apply (proj2_sig exists_encoding) with (n:=encode0 A) ; auto.
Qed.

Lemma decoding_inh :
  {g : nat -> option (form) | (forall A, g (encode A) = Some A) /\
                                  (forall n, (forall (E : {A : _ | encode A = n}), (g n = Some (proj1_sig E))) /\
                                             (((exists A, encode A = n) -> False) -> g n = None)) }.
Proof.
apply constructive_definite_description.
assert (H : forall n, exists! op, (forall E : {A : form | encode A = n},
    op = Some (proj1_sig E)) /\ (((exists A : form, encode A = n) -> False) ->
    op = None)).
{ intro n. destruct (classic (exists A, encode A = n)).
  destruct H. exists (Some x). unfold unique. repeat split. intros.
  subst. simpl. destruct E. simpl. pose (encode_inj x x0 (encode x)).
  assert (encode x = encode x). auto. pose (e0 H). pose (e1 e). rewrite e2. auto.
  intro. exfalso. apply H0. exists x. auto. intros. destruct H0.
  assert ({A : form | encode A = n}). exists x. auto. pose (H0 X).
  destruct X. simpl in e. rewrite <- e0 in H. pose (encode_inj x x0 (encode x)).
  assert (encode x = encode x). auto. pose (e1 H2). symmetry in H. pose (e2 H).
  rewrite <- e3 in e. auto. exists None. unfold unique. repeat split. intros.
  exfalso. apply H. destruct E. exists x. auto. intros. destruct H0. apply H1 in H.
  auto. }
exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
split.
- split.
  + intros A.
    destruct (constructive_definite_description _ _).
    simpl. destruct a. assert ({A0 : form | encode A0 = encode A}). exists A. auto.
    pose (H0 X). destruct X. simpl in e. pose (encode_inj x0 A (encode x0)).
    assert (encode x0 = encode x0). auto. pose (e1 H2). assert (encode x0 = encode A).
    auto. symmetry in H3. pose (e2 H3). rewrite <- e3. auto.
  + intros n.
    now destruct (constructive_definite_description _ _).
- intros g' [H1 H2].
  apply functional_extensionality.
  intros n.
  destruct (constructive_definite_description _ _) as [x e].
  simpl. destruct e. destruct (classic (exists A, encode A = n)).
  + clear H3. destruct H4. assert ({A : form | encode A = n}). exists x0. auto.
    pose (H0 X). pose (H2 n). destruct a. pose (H4 X). destruct X. simpl in e0.
    simpl in e. rewrite e. rewrite e0. auto.
  + pose (H3 H4). rewrite e. pose (H2 n). destruct a. pose (H6 H4). rewrite e0. auto.
Qed.

Definition decoding : nat -> option (form) := proj1_sig decoding_inh.

Lemma encode_decode_Id : forall A, decoding (encode A) = Some A.
Proof.
intro. unfold decoding. destruct decoding_inh. destruct a. auto.
Qed.








End Enumeration.


