Require Import library.
Require Import ZF_axioms ZF_library ZF_nat.

(* Accessibility predicate
   The code is somewhat technical but not very difficult *)

Definition acc (A : ZFSet) (R : ZFSet -> ZFSet -> SProp) (a : ZFSet) : SProp :=
  ∀ X ∈ 𝒫 A, (∀ b ∈ A, (∀ c ∈ A, R c b -> c ∈ X) -> b ∈ X) -> a ∈ X.

Lemma acc_cong (A : ZFSet) (R1 R2 : ZFSet -> ZFSet -> SProp) (a : ZFSet)
  (HR : ∀ a ∈ A, ∀ b ∈ A, R2 a b -> R1 a b) : acc A R1 a -> acc A R2 a.
Proof.
  intros Ha X HX Hacc. apply Ha ; try assumption. intros b Hb Hb2. apply Hacc ; try assumption.
  intros c Hc Hc2. apply Hb2 ; try assumption. now apply HR.
Qed.

Lemma acc_intro (A : ZFSet) (R : ZFSet -> ZFSet -> SProp) (a : ZFSet)
  (Ha : a ∈ A) (IHa : ∀ b ∈ A, R b a -> acc A R b) : acc A R a.
Proof.
  intros X HX Hind. apply Hind. assumption.
  intros b Hb HRb. apply (IHa b Hb HRb X HX Hind).
Qed.

Lemma acc_ind (A : ZFSet) (R : ZFSet -> ZFSet -> SProp) (P : ZFSet -> SProp)
  (HP : ∀ a ∈ A, (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> P b) -> P a)
  (a : ZFSet) (Ha : a ∈ A) (H : acc A R a) : P a.
Proof.
  assert (a ∈ { b ϵ A ∣ acc A R b ∧ P b }).
  { apply (H { b ϵ A ∣ acc A R b ∧ P b }).
    - apply ZFinpower. intros b Hb. apply ZFincomp in Hb. now destruct Hb.
    - intros b Hb IHb. apply ZFincomp. split. 2: split.
      + assumption.
      + apply (acc_intro A R b Hb). intros c Hc HRc. specialize (IHb c Hc HRc).
        apply ZFincomp in IHb. now destruct IHb as [  _ [ H0 _ ] ].
      + apply (HP b Hb) ; intros c Hc HRc ; specialize (IHb c Hc HRc) ;
        apply ZFincomp in IHb ; now destruct IHb as [ H0 [ H1 H2 ] ]. }
  apply ZFincomp in H0. now destruct H0 as [ H0 [ H1 H2 ] ].
Qed.

Lemma acc_inv (A : ZFSet) (R : ZFSet -> ZFSet -> SProp) {a : ZFSet}
  (Ha : a ∈ A) (HRa : acc A R a) {b : ZFSet} (Hb : b ∈ A) (HRb : R b a) : acc A R b.
Proof.
  revert b Hb HRb. refine (acc_ind A R (fun a => forall b : ZFSet, b ∈ A -> R b a -> acc A R b) _ a Ha HRa).
  clear a Ha HRa. intros a Ha HRa IHa b Hb HRb. now apply HRa.
Qed.

Definition accrel (n : nat) (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  (P : ZFSet -> ZFSet) (rec : ZFSet -> ZFSet -> ZFSet) :=
  { x ϵ setSigma n A P ∣
      ∀ X ∈ 𝒫 (setSigma n A P),
      (∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n, 
          (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> ⟨ b ; setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ⟩ ∈ X) -> ⟨ a ; rec a f ⟩ ∈ X)
      -> x ∈ X }.

Lemma accrel_intro {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  {a : ZFSet} (Ha : a ∈ A) (HRa : acc A R a) {φ : ZFSet} (Hφ : φ ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n)
  (Hφ2 : ∀ b ∈ A, R b a -> ⟨ b ; setAppArr { b ϵ A ∣ R b a } (𝕍 n) φ b ⟩ ∈ accrel n A R P rec) :
  ⟨ a ; rec a φ ⟩ ∈ accrel n A R P rec.
Proof.
  apply ZFincomp. split.
  - apply setMkSigma_typing ; try assumption. apply Hrec ; try assumption.
    + now apply acc_inv.
    + intros b Hb HRb. specialize (Hφ2 b Hb HRb). apply ZFincomp in Hφ2. destruct Hφ2 as [ Hφ2 _ ].
      apply setMkSigma_detyping in Hφ2. now destruct Hφ2. exact HP.
  - intros X HX Hind. apply Hind ; try assumption.
    + now apply acc_inv.
    + intros b Hb HRb. specialize (Hφ2 b Hb HRb). apply ZFincomp in Hφ2. destruct Hφ2 as [ _ Hφ2 ].
      apply (Hφ2 X HX Hind).
Qed.

Definition accrelU (n : nat) (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  (P : ZFSet -> ZFSet) (rec : ZFSet -> ZFSet -> ZFSet) (a : ZFSet) (φ : ZFSet) :=
  { x ϵ accrel n A R P rec ∣ setFstSigma n A P x ≡ a -> setSndSigma n A P x ≡ rec a φ }.

Lemma accrelU_intro {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} {a α : ZFSet} {φ ψ : ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  (Ha : a ∈ A) (HRa : acc A R a)
  (Hφ : φ ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n) (Hφ2 : ∀ b ∈ A, R b a -> ⟨ b ; setAppArr { b ϵ A ∣ R b a } (𝕍 n) φ b ⟩ ∈ accrelU n A R P rec α ψ)
  (Hψ : ψ ∈ { b ϵ A ∣ R b α } ⇒ 𝕍 n) (Hψ2 : ∀ b ∈ A, R b α -> ⟨ b ; setAppArr { b ϵ A ∣ R b α } (𝕍 n) ψ b ⟩ ∈ accrel n A R P rec)
  (Hψu : ∀ b ∈ A, R b α -> ∀ pb ∈ P b, ⟨ b ; pb ⟩ ∈ accrel n A R P rec -> pb ≡ setAppArr { b ϵ A ∣ R b α } (𝕍 n) ψ b) :
  ⟨ a ; rec a φ ⟩ ∈ accrelU n A R P rec α ψ.
Proof.
  apply ZFincomp. split.
  - apply accrel_intro ; try assumption. intros b Hb HRb. specialize (Hφ2 b Hb HRb).
    apply ZFincomp in Hφ2. now destruct Hφ2.
  - intro H. assert (∀ b ∈ A, R b a -> setAppArr {b ϵ A ∣ R b a} (𝕍 n) φ b ∈ P b) as Hφ3.
    { intros b Hb HRb. specialize (Hφ2 b Hb HRb). apply ZFincomp in Hφ2. destruct Hφ2 as [ Hφ2 _ ].
      apply ZFincomp in Hφ2. destruct Hφ2 as [ Hφ2 _ ]. apply setMkSigma_detyping in Hφ2.
      now destruct Hφ2. assumption. }
    assert (setFstSigma n A P ⟨ a; rec a φ ⟩ ≡ a) as H0.
    { apply setSigmaβ1 ; try assumption. apply Hrec ; try assumption. now apply acc_inv. }
    pose proof (trans (sym H) H0) as H1. clear H H0. destruct H1.
    assert (setSndSigma n A P ⟨ α ; rec α φ ⟩ ≡ rec α φ) as H0.
    { apply setSigmaβ2 ; try assumption. apply Hrec ; try assumption. now apply acc_inv. }
    refine (trans H0 _). clear H0. assert (φ ≡ ψ) as Hφψ.
    { apply (setArr_funext Hφ Hψ). intros b Hb. apply ZFincomp in Hb. destruct Hb as [ Hb HRb ].
      refine (Hψu b Hb HRb (setAppArr {b0 ϵ A ∣ R b0 α} (𝕍 n) φ b) _ _).
      1,2: specialize (Hφ2 b Hb HRb) ; apply ZFincomp in Hφ2 ; destruct Hφ2 as [ Hφ2 _ ].
      now apply Hφ3. assumption. }
    destruct Hφψ. reflexivity.
Qed.

Lemma accrel_incl_accrelU {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} {α : ZFSet} {ψ : ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  (Hψ : ψ ∈ { b ϵ A ∣ R b α } ⇒ 𝕍 n) (Hψ2 : ∀ b ∈ A, R b α -> ⟨ b ; setAppArr { b ϵ A ∣ R b α } (𝕍 n) ψ b ⟩ ∈ accrel n A R P rec)
  (Hψu : ∀ b ∈ A, R b α -> ∀ pb ∈ P b, ⟨ b ; pb ⟩ ∈ accrel n A R P rec -> pb ≡ setAppArr { b ϵ A ∣ R b α } (𝕍 n) ψ b) :
  accrel n A R P rec ⊂ accrelU n A R P rec α ψ.
Proof.
  intros x Hx. pose proof Hx as Hx2. apply ZFincomp in Hx2. destruct Hx2 as [ Hx2 Hx3 ]. apply Hx3.
  - clear x Hx Hx2 Hx3. apply ZFinpower. intros x Hx. apply ZFincomp in Hx.
    destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. now destruct Hx as [ Hx _ ].
  - intros a Ha φ Hφ HRa IHa. apply accrelU_intro ; try assumption.
    now apply acc_intro. 
Qed.

Lemma accrel_funrel {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  {a : ZFSet} (Ha : a ∈ A) (HRa : acc A R a) : ∃! pa ∈ P a, ⟨ a ; pa ⟩ ∈ accrel n A R P rec.
Proof.
  unshelve eapply (acc_ind A R (fun a => ∃! pa ∈ P a, ⟨ a ; pa ⟩ ∈ accrel n A R P rec) _ a Ha HRa).
  clear a Ha HRa. intros a Ha HRa IHa.
  set (Rφ := fun x px => px ∈ P x ∧ ⟨ x ; px ⟩ ∈ accrel n A R P rec).
  assert (isFunRel { b ϵ A ∣ R b a } (𝕍 n) Rφ) as HRφ.
  { intros b Hb. apply ZFincomp in Hb. destruct Hb as [ Hb HRb ]. specialize (IHa b Hb HRb).
    destruct IHa as [ pb [ [ Hpb Hpb2 ] Hpb3 ] ]. exists pb. split.
    - split. eapply ZFuniv_trans. exact Hpb. now apply HP. now split.
    - intros pb' [ Hpb' [ Hpb'2 Hpb'3 ] ]. now apply Hpb3. }
  set (φ := relToGraph { b ϵ A ∣ R b a } (𝕍 n) Rφ).
  assert (φ ∈ { b ϵ A ∣ R b a } ⇒ (𝕍 n)) as Hφ.
  { now apply relToGraph_typing. }
  assert (∀ b ∈ A, R b a -> ⟨ b ; setAppArr { b ϵ A ∣ R b a } (𝕍 n) φ b ⟩ ∈ accrel n A R P rec) as Hφ2.
  { intros b Hb HRb. unshelve epose proof (funRelApp_inRel (a := b) HRφ _).
    - apply ZFincomp. now split.
    - destruct H as [ _ H ]. refine (transpS (fun X => ⟨ b ; X ⟩ ∈ _) (sym _) H).
      apply (relToGraphToRel' HRφ). now apply ZFincomp. }
  assert (∀ b ∈ A, R b a -> ∀ pb ∈ P b, ⟨ b ; pb ⟩ ∈ accrel n A R P rec -> pb ≡ setAppArr { b ϵ A ∣ R b a } (𝕍 n) φ b) as Hφu.
  { intros b Hb HRb pb Hpb Hpb2. specialize (IHa b Hb HRb). destruct IHa as [ qb [ Hqb0 Hqb1 ] ].
    refine (trans (sym _) _) ; [ now apply Hqb1 | ]. apply Hqb1. split ; [ | now apply Hφ2 ].
    pose proof (setAppArr_rel HRφ (sndS (ZFincomp _ _ b) (mkAndS Hb HRb))) as H. now destruct H. }
  assert (⟨ a; rec a φ ⟩ ∈ accrel n A R P rec) as H.
  { apply accrel_intro ; try assumption. now apply acc_intro. }
  exists (rec a φ). split.
  - split ; try assumption. apply Hrec ; try assumption.
    intros b Hb HRb. pose proof (setAppArr_rel HRφ (sndS (ZFincomp _ _ b) (mkAndS Hb HRb))) as H0. now destruct H0.
  - intros pa [ Hpa H0 ]. apply (accrel_incl_accrelU A R HP Hrec Hφ Hφ2 Hφu) in H0.
    apply ZFincomp in H0. destruct H0 as [ H0 H1 ]. unshelve refine (trans (sym (H1 _)) _).
    + now apply setSigmaβ1.
    + now apply setSigmaβ2. 
Qed.

Lemma accrel_funrel'' {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  {a x y : ZFSet} (Ha : a ∈ A) (HRa : acc A R a) :
  ⟨ a ; x ⟩ ∈ accrel n A R P rec -> ⟨ a ; y ⟩ ∈ accrel n A R P rec -> x ≡ y.
Proof.
  intros Hx Hy. pose proof (accrel_funrel A R HP Hrec Ha HRa) as H. destruct H as [ z [ [ Hz H1 ] H2 ] ].
  assert (x ∈ P a).
  { apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. apply setMkSigma_detyping in Hx. now destruct Hx. exact HP. }
  assert (y ∈ P a).
  { apply ZFincomp in Hy. destruct Hy as [ Hy _ ]. apply setMkSigma_detyping in Hy. now destruct Hy. exact HP. }
  refine (trans (b := z) _ _).
  - refine (sym _). apply H2. now split.
  - apply H2. now split.  
Qed.

Lemma accrel_funrel' {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a) :
  isFunRel { x ϵ A ∣ acc A R x } (setFamUnion n A P) (graphToRel (accrel n A R P rec)).
Proof.
  intros a Ha. apply ZFincomp in Ha. destruct Ha as [ Ha HRa ].
  pose proof (accrel_funrel A R HP Hrec Ha HRa) as H. destruct H as [ pa [ [ Hpa Hpa2 ] Hpa3 ] ].
  exists pa. split ; [ split | ].
  - apply (inSetFamUnion HP Ha Hpa).
  - exact Hpa2.
  - intros qa [ Hqa Hqa2 ]. apply Hpa3. split.
    + unfold graphToRel in Hqa2. apply ZFincomp in Hqa2. destruct Hqa2 as [ Hqa2 _ ].
      apply setMkSigma_detyping in Hqa2. now destruct Hqa2. exact HP.
    + exact Hqa2.
Qed.

Definition accrec (n : nat) (A : ZFSet) (R : ZFSet -> ZFSet -> SProp) (P : ZFSet -> ZFSet)
  (rec : ZFSet -> ZFSet -> ZFSet) (a : ZFSet) : ZFSet :=
  funRelApp A (setFamUnion n A P) (graphToRel (accrel n A R P rec)) a.

Lemma accrec_inrel {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  {a : ZFSet} (Ha : a ∈ A) (HRa : acc A R a) :
  ⟨ a ; accrec n A R P rec a ⟩ ∈ accrel n A R P rec.
Proof.
  change (graphToRel (accrel n A R P rec) a (funRelApp { x ϵ A ∣ acc A R x } (setFamUnion n A P) (graphToRel (accrel n A R P rec)) a)).
  apply funRelApp_inRel.
  - now apply accrel_funrel'.
  - apply ZFincomp. now split.
Qed.

Lemma accrec_typing {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  {a : ZFSet} (Ha : a ∈ A) (HRa : acc A R a) :
  accrec n A R P rec a ∈ P a.
Proof.
  pose proof (accrec_inrel A R HP Hrec Ha HRa).
  apply ZFincomp in H. destruct H as [ H _ ].
  apply setMkSigma_detyping in H. now destruct H. exact HP.
Qed.

Lemma accrec_β {n : nat} (A : ZFSet) (R : ZFSet -> ZFSet -> SProp)
  {P : ZFSet -> ZFSet} {rec : ZFSet -> ZFSet -> ZFSet} (HP : ∀ a ∈ A, P a ∈ 𝕍 n)
  (Hrec : ∀ a ∈ A, ∀ f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 n,
      (∀ b ∈ A, R b a -> acc A R b) -> (∀ b ∈ A, R b a -> setAppArr { b ϵ A ∣ R b a } (𝕍 n) f b ∈ P b) -> rec a f ∈ P a)
  {a : ZFSet} (Ha : a ∈ A) (HRa : acc A R a) :
  accrec n A R P rec a ≡ rec a (relToGraph { b ϵ A ∣ R b a } (𝕍 n) (HO_rel (fun b => accrec n A R P rec b))).
Proof.
  pose proof (accrec_inrel A R HP Hrec Ha HRa) as H.
  assert (⟨ a ; rec a (relToGraph {b ϵ A ∣ R b a} (𝕍 n) (HO_rel (fun b : ZFSet => accrec n A R P rec b))) ⟩ ∈ accrel n A R P rec) as H0.
  { apply (accrel_intro A R HP Hrec Ha HRa).
    - apply relToGraph_typing. apply HO_rel_typing. intros b Hb. apply ZFincomp in Hb.
      destruct Hb as [ Hb HRb ]. eapply ZFuniv_trans.
      + apply (accrec_typing A R HP Hrec Hb). apply (acc_inv A R Ha HRa Hb HRb).
      + now apply HP.
    - intros b Hb HRb.
      assert (setAppArr {b0 ϵ A ∣ R b0 a} (𝕍 n) (relToGraph {b0 ϵ A ∣ R b0 a} (𝕍 n)
                                                   (HO_rel (fun b0 : ZFSet => accrec n A R P rec b0))) b
                ≡ accrec n A R P rec b).
      { apply setAppArr_HO.
        - clear b Hb HRb. intros b Hb. apply ZFincomp in Hb. destruct Hb as [ Hb HRb ]. eapply ZFuniv_trans.
          + apply (accrec_typing A R HP Hrec Hb). apply (acc_inv A R Ha HRa Hb HRb).
          + now apply HP.
        - now apply ZFincomp. }
      refine (transpS (fun X => ⟨ b ; X ⟩ ∈ accrel n A R P rec) (sym H0) _). clear H0.
      apply (accrec_inrel A R HP Hrec Hb). apply (acc_inv A R Ha HRa Hb HRb). }
  apply (accrel_funrel'' A R HP Hrec Ha HRa H H0).
Qed.
