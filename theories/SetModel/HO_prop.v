Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_univ.

(* Universe of propositions *)

Definition propTy_HO : ZFSet -> ZFSet := fun _ => ⟨ Ω ; ⟨ ZFfour ; ∅ ⟩ ⟩.

Lemma propTy_HO_typing {n : nat} {Γ : ZFSet} : ∀ γ ∈ Γ, propTy_HO γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. apply setMkPair_typing.
  - apply Ω_typing.
  - apply setMkPair_typing.
    + apply four_typing.
    + apply empty_in_univ.
Qed.

Lemma el_propTy {n : nat} {γ : ZFSet} : 𝕌el n (propTy_HO γ) ≡ Ω.
Proof.
  apply setPairβ1.
  + apply Ω_typing.
  + apply setMkPair_typing. apply four_typing. apply empty_in_univ.
Qed.

(* Proof irrelevance *)

Definition propTy_HO_irr {Γ : ZFSet} {P p q : ZFSet -> ZFSet} (HP : ∀ γ ∈ Γ, P γ ∈ Ω) (Hp : ∀ γ ∈ Γ, p γ ∈ P γ)
  (Hq : ∀ γ ∈ Γ, q γ ∈ P γ) : ∀ γ ∈ Γ, p γ ≡ q γ.
Proof.
  intros γ Hγ. specialize (HP γ Hγ). specialize (Hp γ Hγ). specialize (Hq γ Hγ). cbn in *.
  refine (trans _ (sym _)). now apply (proof_irr HP). now apply (proof_irr HP).
Qed.

