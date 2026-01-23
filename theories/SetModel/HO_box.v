Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO.

(* Boxed propositions (think of them as a record with one field of type P) *)

Definition boxTy_HO (P : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun γ => ⟨ P γ ; ⟨ ZFfive ; ∅ ⟩ ⟩.

Lemma boxTy_HO_typing {n : nat} {Γ : ZFSet} {P : ZFSet -> ZFSet} (HP : ∀ γ ∈ Γ, P γ ∈ Ω) :
  ∀ γ ∈ Γ, boxTy_HO P γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. apply setMkPair_typing.
  - eapply ZFuniv_trans. now apply HP. now apply Ω_typing.
  - apply setMkPair_typing.
    + apply five_typing.
    + apply empty_in_univ.
Qed.

Lemma el_boxTy {n : nat} {Γ : ZFSet} {P : ZFSet -> ZFSet} (HP : ∀ γ ∈ Γ, P γ ∈ Ω) : ∀ γ ∈ Γ, 𝕌el n (boxTy_HO P γ) ≡ P γ.
Proof.
  intros γ Hγ. apply setPairβ1.
  + eapply ZFuniv_trans. now apply HP. now apply Ω_typing.
  + apply setMkPair_typing. apply five_typing. apply empty_in_univ.
Qed.

(* Boxing proofs / record constructor *)

Definition boxTm_HO (p : ZFSet -> ZFSet) : ZFSet -> ZFSet := p.

Lemma boxTm_HO_typing {n : nat} {Γ : ZFSet} {P p : ZFSet -> ZFSet} (HP : ∀ γ ∈ Γ, P γ ∈ Ω) (Hp : ∀ γ ∈ Γ, p γ ∈ P γ) :
  ∀ γ ∈ Γ, boxTm_HO p γ ∈ 𝕌el n (boxTy_HO P γ).
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (sym (el_boxTy HP γ Hγ)) _). now apply Hp.
Qed.

(* Unboxing proofs / projection *)

Definition unboxTm_HO (p : ZFSet -> ZFSet) : ZFSet -> ZFSet := p.

Lemma unboxTm_HO_typing {n : nat} {Γ : ZFSet} {P p : ZFSet -> ZFSet} (HP : ∀ γ ∈ Γ, P γ ∈ Ω)
  (Hp : ∀ γ ∈ Γ, p γ ∈ 𝕌el n (boxTy_HO P γ)) : ∀ γ ∈ Γ, unboxTm_HO p γ ∈ P γ.
Proof.
  intros γ Hγ. cbn. refine (transpS (fun X => _ ∈ X) (el_boxTy HP γ Hγ) _). now apply Hp.
Qed.

(* η for the record *)

Lemma boxTy_HO_η {n : nat} {Γ : ZFSet} {P p : ZFSet -> ZFSet} (HP : ∀ γ ∈ Γ, P γ ∈ Ω)
  (Hp : ∀ γ ∈ Γ, p γ ∈ 𝕌el n (boxTy_HO P γ)) : ∀ γ ∈ Γ, p γ ≡ boxTm_HO (unboxTm_HO p) γ.
Proof.
  intros γ Hγ. cbn. reflexivity.
Qed.

