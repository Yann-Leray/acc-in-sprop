Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.
Require Import HO HO_pi HO_univ.

Definition natTy_HO : ZFSet -> ZFSet := fun _ => ⟨ ω ; ⟨ ∅ ; ∅ ⟩ ⟩.

Lemma natTy_HO_typing {n : nat} {Γ : ZFSet} : ∀ γ ∈ Γ, natTy_HO γ ∈ 𝕌 n.
Proof.
  intros γ Hγ. apply setMkPair_typing.
  - now apply ZFuniv_uncountable.
  - apply setMkPair_typing.
    + apply zero_typing.
    + apply empty_in_univ.
Qed.

Lemma el_natTy {n : nat} {γ : ZFSet} : 𝕌el n (natTy_HO γ) ≡ ω.
Proof.
  apply setPairβ1.
  + apply ZFuniv_uncountable.
  + apply setMkPair_typing. apply zero_typing. apply empty_in_univ.
Qed.

Lemma hd_natTy {n : nat} {γ : ZFSet} :
  𝕌hd n (natTy_HO γ) ≡ ZFzero.
Proof.
  refine (trans (fequal (setFstPair ω (𝕍 n)) _) _).
  apply setPairβ2'.
  { apply setMkPair_typing.
    - now apply ZFuniv_uncountable.
    - apply setMkPair_typing.
      + apply zero_typing.
      + apply empty_in_univ. }
  apply setPairβ1. apply zero_typing. apply empty_in_univ.
Qed.

(* Zero *)

Definition zeroTm_HO : ZFSet -> ZFSet := fun _ => ∅.

Lemma zeroTm_HO_typing (n : nat) {γ : ZFSet} : zeroTm_HO γ ∈ 𝕌el n (natTy_HO γ).
Proof.
  refine (transpS (fun x => _ ∈ x) _ _).
  - symmetry. apply el_natTy. 
  - apply zero_typing.
Qed.

(* Successor *)

Definition sucTm_HO (t : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => ZFsuc (t γ).

Lemma sucTm_HO_typing {n : nat} {Γ γ : ZFSet} {t : ZFSet -> ZFSet}
  (Ht : ∀ γ ∈ Γ, t γ ∈ 𝕌el n (natTy_HO γ)) (Hγ : γ ∈ Γ) :
  sucTm_HO t γ ∈ 𝕌el n (natTy_HO γ).
Proof.
  refine (transpS (fun x => _ ∈ x) _ _).
  { symmetry. apply el_natTy. }
  apply suc_typing.
  refine (transpS (fun x => _ ∈ x) _ _).
  { apply (@el_natTy n γ). }
  now apply Ht.
Qed.

(* Recursor *)

Definition natrecTm_HO (n : nat) (P pz ps m : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => natrec2 n (fun m => 𝕌el n (P ⟨ γ ; m ⟩)) (pz γ) (fun m pm => ps ⟨ ⟨ γ ; m ⟩ ; pm ⟩) (m γ).

Lemma natrecTm_HO_typing_aux {n : nat} {Γ γ : ZFSet} {P ps : ZFSet -> ZFSet}
  (HP : ∀ γm ∈ ctxExt 0 Γ natTy_HO, P γm ∈ 𝕌 n)
  (Hps : ∀ γmp ∈ ctxExt n (ctxExt 0 Γ natTy_HO) P,
      ps γmp ∈ 𝕌el n (P ⟨ ctx_wk 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)
                        ; sucTm_HO (fun γmp => ctx_var0 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)) γmp ⟩))
  (Hγ : γ ∈ Γ) :
  ∀ x ∈ ω, ∀ px ∈ 𝕌el n (P ⟨ γ ; x ⟩), ps ⟨ ⟨ γ ; x ⟩ ; px ⟩ ∈ 𝕌el n (P ⟨ γ ; ZFsuc x ⟩).
Proof.
  intros x Hx px Hpx.
  assert (x ∈ 𝕌el 0 (natTy_HO γ)).
  { exact (transpS (fun X => x ∈ X) (sym el_natTy) Hx). }
  assert (⟨ ⟨ γ; x ⟩; px ⟩ ∈ ctxExt n (ctxExt 0 Γ natTy_HO) P) as H0.
  { apply setMkSigma_typing ; try assumption. intros y Hy. apply 𝕌el_typing. now apply HP.
    apply setMkSigma_typing ; try assumption. intros y Hy. apply 𝕌el_typing. now apply (natTy_HO_typing (Γ := Γ)). }
  specialize (Hps _ H0). cbn in Hps. refine (transp2S (fun X Y => _ ∈ 𝕌el n (P ⟨ X ; Y ⟩)) _ _ Hps).
  + refine (trans (fequal (ctx_wk 0 Γ natTy_HO) _) _).
    * apply ctxExtβ1 ; try assumption. apply setMkSigma_typing ; try assumption.
      intros y Hy. apply 𝕌el_typing. now apply (natTy_HO_typing (Γ := Γ)).
    * apply ctxExtβ1 ; try assumption. now apply natTy_HO_typing.
  + unfold sucTm_HO. refine (fequal ZFsuc _). refine (trans (fequal (ctx_var0 0 Γ natTy_HO) _) _).
    * apply ctxExtβ1 ; try assumption. apply setMkSigma_typing ; try assumption.
      intros y Hy. apply 𝕌el_typing. now apply (natTy_HO_typing (Γ := Γ)).
    * apply ctxExtβ2 ; try assumption. now apply natTy_HO_typing.
Qed.

Lemma natrecTm_HO_typing {n : nat} {Γ : ZFSet} {P pz ps m : ZFSet -> ZFSet}
  (HP : ∀ γm ∈ ctxExt 0 Γ natTy_HO, P γm ∈ 𝕌 n) (Hpz : ∀ γ ∈ Γ, pz γ ∈ 𝕌el n (P ⟨ γ ; zeroTm_HO γ ⟩))
  (Hps : ∀ γmp ∈ ctxExt n (ctxExt 0 Γ natTy_HO) P,
      ps γmp ∈ 𝕌el n (P ⟨ ctx_wk 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)
                        ; sucTm_HO (fun γmp => ctx_var0 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)) γmp ⟩))
  (Hm : ∀ γ ∈ Γ, m γ ∈ 𝕌el 0 (natTy_HO γ)) :
  ∀ γ ∈ Γ, natrecTm_HO n P pz ps m γ ∈ 𝕌el n (P ⟨ γ ; m γ ⟩).
Proof.
  intros γ Hγ. cbn. unfold natrecTm_HO. apply (natrec2_typing (P := fun m => 𝕌el n (P ⟨ γ ; m ⟩))).
  - intros x Hx. apply 𝕌el_typing. apply (typeExt_typing natTy_HO_typing HP). assumption.
    exact (transpS (fun X => x ∈ X) (sym el_natTy) Hx).
  - now apply Hpz.
  - now apply (natrecTm_HO_typing_aux HP Hps Hγ).
  - exact (transpS (fun X => m γ ∈ X) el_natTy (Hm γ Hγ)).
Qed.

Lemma natrecTm_HO_β1 {n : nat} {Γ : ZFSet} {P pz ps : ZFSet -> ZFSet}
  (HP : ∀ γm ∈ ctxExt 0 Γ natTy_HO, P γm ∈ 𝕌 n) (Hpz : ∀ γ ∈ Γ, pz γ ∈ 𝕌el n (P ⟨ γ ; zeroTm_HO γ ⟩))
  (Hps : ∀ γmp ∈ ctxExt n (ctxExt 0 Γ natTy_HO) P,
      ps γmp ∈ 𝕌el n (P ⟨ ctx_wk 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)
                        ; sucTm_HO (fun γmp => ctx_var0 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)) γmp ⟩)) :
  ∀ γ ∈ Γ, natrecTm_HO n P pz ps zeroTm_HO γ ≡ pz γ.
Proof.
  intros γ Hγ. cbn. unfold natrecTm_HO. unfold zeroTm_HO. apply natrec2_β1.
  - intros x Hx. apply 𝕌el_typing. apply (typeExt_typing natTy_HO_typing HP). assumption.
    exact (transpS (fun X => x ∈ X) (sym el_natTy) Hx).
  - now apply Hpz.
  - now apply (natrecTm_HO_typing_aux HP Hps Hγ).
Qed.

Lemma natrecTm_HO_β2 {n : nat} {Γ : ZFSet} {P pz ps m : ZFSet -> ZFSet}
  (HP : ∀ γm ∈ ctxExt 0 Γ natTy_HO, P γm ∈ 𝕌 n) (Hpz : ∀ γ ∈ Γ, pz γ ∈ 𝕌el n (P ⟨ γ ; zeroTm_HO γ ⟩))
  (Hps : ∀ γmp ∈ ctxExt n (ctxExt 0 Γ natTy_HO) P,
      ps γmp ∈ 𝕌el n (P ⟨ ctx_wk 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)
                        ; sucTm_HO (fun γmp => ctx_var0 0 Γ natTy_HO (ctx_wk n (ctxExt 0 Γ natTy_HO) P γmp)) γmp ⟩))
  (Hm : ∀ γ ∈ Γ, m γ ∈ 𝕌el 0 (natTy_HO γ)) :
  ∀ γ ∈ Γ, natrecTm_HO n P pz ps (sucTm_HO m) γ ≡ ps ⟨ ⟨ γ ; m γ ⟩ ; natrecTm_HO n P pz ps m γ ⟩.
Proof.
  intros γ Hγ. cbn. unfold natrecTm_HO. unfold sucTm_HO. refine (trans _ _).
  - apply natrec2_β2.
    + intros x Hx. apply 𝕌el_typing. apply (typeExt_typing natTy_HO_typing HP). assumption.
      exact (transpS (fun X => x ∈ X) (sym el_natTy) Hx).
    + now apply Hpz.
    + now apply (natrecTm_HO_typing_aux HP Hps Hγ).
    + exact (transpS (fun X => m γ ∈ X) el_natTy (Hm γ Hγ)).
  - reflexivity.
Qed.

