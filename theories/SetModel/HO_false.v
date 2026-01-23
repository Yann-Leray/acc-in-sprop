Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_prop.

(* False proposition *)

Definition falseTy_HO : ZFSet -> ZFSet := fun γ => subsingl FalseS.

Lemma falseTy_HO_typing (Γ : ZFSet) : ∀ γ ∈ Γ, falseTy_HO γ ∈ Ω.
Proof.
  intros. cbn. apply subsingl_typing.
Qed.

(* Eliminator of False *)

Definition emptyrecTm_HO (A : ZFSet -> ZFSet) (H : ZFSet -> ZFSet) := ∅.

Lemma emptyrecTm_HO_typing {n : nat} {Γ : ZFSet} {A H : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HH : ∀ γ ∈ Γ, H γ ∈ falseTy_HO γ) :
  ∀ γ ∈ Γ, emptyrecTm_HO A H ∈ 𝕌el n (A γ).
Proof.
  intros γ Hγ. specialize (HH γ Hγ). cbn in HH. apply subsingl_true_if in HH. destruct HH.
Qed.
