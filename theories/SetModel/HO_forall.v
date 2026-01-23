Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_prop HO_univ HO_box.

(* Proof-irrelevant pi types *)

Definition forallTy_HO (n : nat) (A : ZFSet -> ZFSet) (B : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => subsingl (∀ a ∈ 𝕌el n (A γ), ∅ ∈ B ⟨ γ ; a ⟩).

Lemma forallTy_HO_typing {n : nat} {Γ : ZFSet} {A : ZFSet -> ZFSet} {B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ Ω) :
  ∀ γ ∈ Γ, forallTy_HO n A B γ ∈ Ω.
Proof.
  intros γ Hγ. unfold forallTy_HO. apply subsingl_typing.
Qed.

(* Lambda abstraction *)

Lemma ilamTm_HO_typing (n : nat) {Γ : ZFSet} {A B : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ Ω)
  (Ht : ∀ γa ∈ ctxExt n Γ A, ∅ ∈ B γa) :
  ∀ γ ∈ Γ, ∅ ∈ forallTy_HO n A B γ.
Proof.
  intros γ Hγ. cbn. unfold forallTy_HO.
  apply subsingl_true_iff. intros a Ha. assert (⟨ γ ; a ⟩ ∈ ctxExt n Γ A) as Hγa.
  { apply setMkSigma_typing ; try assumption. intros γ' Hγ'. apply 𝕌el_typing. now apply HA. }
  specialize (Ht _ Hγa). cbn in Ht. specialize (HB _ Hγa). cbn in HB.
  refine (proof_irr' HB _ Ht).
Qed.

(* Application *)

Lemma iappTm_HO_typing (n : nat) {Γ : ZFSet} {A B u : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HB : ∀ γa ∈ ctxExt n Γ A, B γa ∈ Ω)
  (Ht : ∀ γ ∈ Γ, ∅ ∈ forallTy_HO n A B γ) (Hu : ∀ γ ∈ Γ, u γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, ∅ ∈ B ⟨ γ ; u γ ⟩.
Proof.
  intros γ Hγ. cbn. 
  specialize (Ht _ Hγ). cbn in Ht. unfold forallTy_HO in Ht. apply subsingl_true_if in Ht.
  apply Ht. now apply Hu.
Qed.

(* Implication *)

Definition implTy_HO' (Γ : ZFSet) (P : ZFSet -> ZFSet) (Q : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  forallTy_HO 0 (boxTy_HO P) (fun γa => Q (ctx_wk 0 Γ (boxTy_HO P) γa)).

Definition implTy_HO (P : ZFSet -> ZFSet) (Q : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => subsingl (P γ ⊂ Q γ).

Lemma implTy_HO_typing {Γ : ZFSet} {P : ZFSet -> ZFSet} {Q : ZFSet -> ZFSet}
  (HP : ∀ γ ∈ Γ, P γ ∈ Ω) (HQ : ∀ γ ∈ Γ, Q γ ∈ Ω) : ∀ γ ∈ Γ, implTy_HO P Q γ ∈ Ω.
Proof.
  intros. now apply subsingl_typing.
Qed.

Lemma implTy_HO_eq_implTy_HO' {Γ : ZFSet} {P : ZFSet -> ZFSet} {Q : ZFSet -> ZFSet}
  (HP : ∀ γ ∈ Γ, P γ ∈ Ω) (HQ : ∀ γ ∈ Γ, Q γ ∈ Ω) : ∀ γ ∈ Γ, implTy_HO P Q γ ≡ implTy_HO' Γ P Q γ.
Proof.
  intros γ Hγ. unfold implTy_HO. unfold implTy_HO'. unfold forallTy_HO.
  apply (fstS subsingl_ext). split.
  - intros H x Hx. refine (transpS (fun X => ∅ ∈ Q X) (sym _) _).
    { apply ctxExtβ1 ; try assumption. intros γ' Hγ'. now apply (boxTy_HO_typing (Γ := Γ)). }
    apply H. eapply proof_irr'. now apply HP. exact (transpS (fun X => _ ∈ X) (el_boxTy HP γ Hγ) Hx).
  - intros H x Hx. pose proof (sym (proof_irr (HP γ Hγ) x Hx)) as H0. destruct H0.
    specialize (H ∅ (transpS (fun X => _ ∈ X) (sym (el_boxTy HP γ Hγ)) Hx)).
    refine (transpS (fun X => ∅ ∈ Q X) _ H).
    apply ctxExtβ1 ; try assumption. intros γ' Hγ'. now apply (boxTy_HO_typing (Γ := Γ)).
    refine (transpS (fun X => _ ∈ X) (sym (el_boxTy HP γ Hγ)) Hx).
Qed.
    
