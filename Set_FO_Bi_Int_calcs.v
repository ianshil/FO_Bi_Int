Require Import FO_Bi_Int_Syntax.
Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Ensembles.
Local Set Implicit Arguments.
Local Unset Strict Implicit.




(* In this file we define two Hilbert calculi based on multisets for the propositonal
   bi-intuitionistic logics wBIL and sBIL. *)



(* Ensembles vs Ensembles_finis vs lists :
  - Ensembles is what I used for the propositional case, but I believe that using potentially infinite sets
    in the axiomatic system will force me to use extensions of languages in the Lindenbaum lemma (sounds
    complicated...).
  - Ensembles finis avoid this problem, as they are finite (and so always allow you to pick a variable not yet present
    in the set. However, this might be problematic to prove completeness of the strong system, as I brutally close
    under double negation the set (which then becomes infinite). However, I might manage to get there by using
    a finite closure over negations (to keep the set finite) as there is some notion of "modal" depth here.
  - Lists suffer from the same problems as finite sets I reckon. And they are further away from the work I
    did in the propositional case. *)



Section Calculi.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* **** Definition *)

(* Do I want a notion of substitution of formulae? *)

(* We define here the axioms. *)

Definition RA1 (A B C : form) : form := (A --> B) --> ((B --> C) --> (A --> C)).
Definition RA2 (A B : form) : form := A --> (A ∨ B).
Definition RA3 (A B : form) : form := B --> (A ∨ B).
Definition RA4 (A B C : form) : form := (A --> C) --> ((B --> C) --> ((A ∨ B) --> C)).
Definition RA5 (A B : form) : form := (A ∧ B) --> A.
Definition RA6 (A B : form) : form := (A ∧ B) --> B.
Definition RA7 (A B C : form) : form := (A --> B) --> ((A --> C) --> (A --> (B ∧ C))).
Definition RA8 (A B C : form) : form := (A --> (B --> C)) --> ((A ∧ B) --> C).
Definition RA9 (A B C : form) : form := ((A ∧ B) --> C) --> (A --> (B --> C)).
Definition RA10 (A B : form) : form := (A --> B) --> ((¬ B) --> ¬ A).
Definition RA11 (A B : form) : form := A --> (B ∨ (A --< B)).
Definition RA12 (A B : form) : form := (A --< B) --> ∞ (A --> B).
Definition RA13 (A B C : form) : form := ((A --< B) --< C) --> (A --< (B ∨ C)).
Definition RA14 (A B : form) : form := (¬ (A --< B)) --> (A --> B).
Definition RA15 (A : form) : form := A --> ⊤.
Definition RA16 (A : form) : form := ⊥ --> A.
Definition RA17 (A B : form) : form := (∀ (A[↑] --> B)) --> (A --> ∀ B).
Definition RA18 (A : form) (t : term) : form := (∀ A) --> A[t..].
Definition RA19 (A : form) (t : term) : form := A[t..] --> ∃ A.

Inductive BIAxioms (A : form) : Prop :=
 | RA1_I : (exists B C D, A = (RA1 B C D)) -> BIAxioms A
 | RA2_I : (exists B C, A = (RA2 B C)) -> BIAxioms A
 | RA3_I :  (exists B C, A = (RA3 B C)) -> BIAxioms A
 | RA4_I :  (exists B C D, A = (RA4 B C D)) -> BIAxioms A
 | RA5_I :  (exists B C, A = (RA5 B C)) -> BIAxioms A
 | RA6_I :  (exists B C, A = (RA6 B C)) -> BIAxioms A
 | RA7_I :  (exists B C D, A = (RA7 B C D)) -> BIAxioms A
 | RA8_I :  (exists B C D, A = (RA8 B C D)) -> BIAxioms A
 | RA9_I :  (exists B C D, A = (RA9 B C D)) -> BIAxioms A
 | RA10_I :  (exists B C, A = (RA10 B C)) -> BIAxioms A
 | RA11_I :  (exists B C, A = (RA11 B C)) -> BIAxioms A
 | RA12_I :  (exists B C, A = (RA12 B C)) -> BIAxioms A
 | RA13_I :  (exists B C D, A = (RA13 B C D)) -> BIAxioms A
 | RA14_I :  (exists B C, A = (RA14 B C)) -> BIAxioms A
 | RA15_I :  (exists B, A = (RA15 B)) -> BIAxioms A
 | RA16_I :  (exists B, A = (RA16 B)) -> BIAxioms A
 | RA17_I :  (exists B C, A = (RA17 B C)) -> BIAxioms A
 | RA18_I :  (exists B t, A = (RA18 B t)) -> BIAxioms A
 | RA19_I :  (exists B t, A = (RA19 B t)) -> BIAxioms A.

(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later.

   We start by giving the rules common to both calculi. *)

Inductive IdRule : rls (@Ensemble (form) * (form)) :=
  | IdRule_I : forall A (Γ : @Ensemble _),
                  (In _ Γ A) -> (IdRule nil (Γ, A)).

Inductive AxRule : rls ((@Ensemble (form)) * (form)) :=
  | AxRule_I : forall Γ (A : form),
          (BIAxioms A) -> AxRule nil (Γ, A)
.

Inductive MPRule : rls ((@Ensemble (form)) * (form)) :=
  | MPRule_I : forall A B Γ,
          MPRule ((Γ, (A --> B)) :: (Γ, A) :: nil)
                    (Γ, B)
.

Inductive GenRule : rls ((@Ensemble (form)) * (form)) :=
  | GenRule_I : forall (A : form) Γ,
          GenRule (((fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)), A) :: nil)
                     (Γ, ∀ A)
.

Inductive ECRule : rls ((@Ensemble (form)) * (form)) :=
  | ECRule_I : forall (A B : form) Γ,
          ECRule (((fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)), A --> (B[↑])) :: nil)
                     (Γ, (∃ A) --> B)
.

(* Then we turn to the distinctive rules of each calculus. *)

Inductive DNwRule : rls ((@Ensemble (form)) * (form)) :=
  | DNwRule_I : forall (A : form) Γ,
          DNwRule ((Empty_set _, A) :: nil)
                    (Γ, ¬ ∞ A)
.

Inductive DNsRule : rls ((@Ensemble (form)) * (form)) :=
  | DNsRule_I : forall (A : form) Γ,
          DNsRule ((Γ, A) :: nil)
                     (Γ, ¬ ∞ A)
.




(* At last we can define our calculus GLS and its proof-search version PSGLS. *)

Inductive wFOBIC_rules (s : ((@Ensemble (form)) * (form))) : Prop :=
  | Id : IdRule nil s -> wFOBIC_rules s
  | Ax : AxRule nil s -> wFOBIC_rules s
  | MP : forall ps, (forall prem, List.In prem ps -> wFOBIC_rules prem) -> MPRule ps s -> wFOBIC_rules s
  | DNw : forall ps, (forall prem, List.In prem ps -> wFOBIC_rules prem) -> DNwRule ps s -> wFOBIC_rules s
  | Gen : forall ps, (forall prem, List.In prem ps -> wFOBIC_rules prem) -> GenRule ps s -> wFOBIC_rules s
  | EC : forall ps, (forall prem, List.In prem ps -> wFOBIC_rules prem) -> ECRule ps s -> wFOBIC_rules s
.

Inductive sFOBIC_rules (s : ((@Ensemble form) * (form))) : Prop :=
  | Ids : IdRule nil s -> sFOBIC_rules s
  | Axs : AxRule nil s -> sFOBIC_rules s
  | MPs : forall ps, (forall prem, List.In prem ps -> sFOBIC_rules prem) -> MPRule ps s -> sFOBIC_rules s
  | DNs : forall ps, (forall prem, List.In prem ps -> sFOBIC_rules prem) -> DNsRule ps s -> sFOBIC_rules s
  | Gens : forall ps, (forall prem, List.In prem ps -> sFOBIC_rules prem) -> GenRule ps s -> sFOBIC_rules s
  | ECs : forall ps, (forall prem, List.In prem ps -> sFOBIC_rules prem) -> ECRule ps s -> sFOBIC_rules s
.
(* Define the general notion of derivable pair. *)

Fixpoint list_disj (l : list form) : form :=
match l with
 | nil => ⊥
 | h :: t => h ∨ (list_disj t)
end.

Fixpoint list_conj (l : list form) : form :=
match l with
 | nil => ⊤
 | h :: t => h ∧ (list_conj t)
end.

(* Why do I pick a NoDup list? Makes things easier I guess, as I can control the length.
    Logically I should be able to get rid of it though. *)

Definition wpair_der (G : prod (@Ensemble form) (@Ensemble form)) : Prop :=
    exists (l : list form), NoDup l /\ (forall A, List.In A l -> (In _ (snd G) A)) /\
        (wFOBIC_rules (fst G, list_disj l)).

Definition spair_der (G : prod (@Ensemble form) (@Ensemble form)) : Prop :=
    exists (l : list form), NoDup l /\ (forall A, List.In A l -> (In _ (snd G) A)) /\
        (sFOBIC_rules (fst G, list_disj l)).

Definition complete (G : prod (Ensemble form) (Ensemble form)) : Prop :=
    forall (A : form), In _ (fst G) A \/ In _ (snd G) A.


End Calculi.

