Require Import library.
Require Import ZF_axioms ZF_library.

(* Natural numbers *)

Definition ZFzero  := ∅.             (* nat *)
Definition ZFone   := ZFsuc ZFzero.  (* pi *)
Definition ZFtwo   := ZFsuc ZFone.   (* sigma *)
Definition ZFthree := ZFsuc ZFtwo.   (* type *)
Definition ZFfour  := ZFsuc ZFthree. (* prop *)
Definition ZFfive  := ZFsuc ZFfour.  (* box *)

Lemma zero_typing : ZFzero ∈ ω.
Proof.
  now apply ZFininfinity. 
Qed.

Lemma suc_typing {n : ZFSet} (Hn : n ∈ ω) : ZFsuc n ∈ ω.
Proof.
  apply ZFininfinity. intros P Pz Ps.
  apply Ps. now eapply ZFininfinity.
Qed.

Lemma one_typing : ZFone ∈ ω.
Proof.
  apply suc_typing. apply zero_typing.
Qed.

Lemma two_typing : ZFtwo ∈ ω.
Proof.
  apply suc_typing. apply one_typing.
Qed.

Lemma three_typing : ZFthree ∈ ω.
Proof.
  apply suc_typing. apply two_typing.
Qed.

Lemma four_typing : ZFfour ∈ ω.
Proof.
  apply suc_typing. apply three_typing.
Qed.

Lemma five_typing : ZFfive ∈ ω.
Proof.
  apply suc_typing. apply four_typing.
Qed.

Fixpoint nat_to_ω (n : nat) {struct n} :=
  match n with
  | 0    => ∅
  | S n' => ZFsuc (nat_to_ω n')
  end.

Lemma nat_to_ω_typing (n : nat) : nat_to_ω n ∈ ω.
Proof.
  induction n.
  - apply zero_typing.
  - now apply suc_typing.
Qed.

(* zero is not a successor *)

Lemma zero_ne_suc (x : ZFSet) : ∅ ≡ ZFsuc x -> FalseS.
Proof.
  intro H. eapply ZFinempty.
  refine (transpS (fun X => x ∈ X) (sym H) _).
  apply ZFinpairing. left. reflexivity.
Qed.

(* Induction principle *)

Lemma nat_ind {x : ZFSet} (Hx : x ∈ ω) (P : ZFSet -> SProp) (pz : P ∅) (ps : ∀ x ∈ ω, P x -> P (ZFsuc x)) : P x.
Proof.
  apply (fstS (ZFininfinity x) Hx (fun n => n ∈ ω ∧ P n)).
  - split. apply zero_typing. exact pz.
  - intros n [ Hn IH ]. split. now apply suc_typing. now apply ps.
Qed.

(* Injectivity of successor (one can probably find a better proof) *)

Lemma suc_inj {x y : ZFSet} (Hx : x ∈ ω) (Hy : y ∈ ω) : ZFsuc x ≡ ZFsuc y -> x ≡ y.
Proof.
  revert y Hy. apply (fstS (ZFininfinity x) Hx (fun a => ∀ y ∈ ω, ZFsuc a ≡ ZFsuc y -> a ≡ y)).
  - intros y Hy H. assert (y ∈ {∅; setSingl ∅}) as H0.
    { refine (transpS (fun X => y ∈ X) (sym H) _). apply ZFinpairing. now left. }
    apply ZFinpairing in H0. destruct H0 as [ H0 | H0 ].
    + exact (sym H0).
    + apply (transpS (fun X => ZFsuc ∅ ≡ ZFsuc X) H0) in H. assert (∅ ∈ ZFsuc (setSingl ∅)).
      { refine (transpS (fun X => ∅ ∈ X) H _). apply ZFinpairing. now left. }
      apply ZFinpairing in H1. destruct H1 as [ H1 | H1 ].
      * assert (∅ ∈ ∅). { refine (transpS (fun X => ∅ ∈ X) (sym H1) _). apply ZFinpairing. now left. }
        apply ZFinempty in H2. destruct H2.
      * assert (setSingl ∅ ∈ ∅). { refine (transpS (fun X => setSingl ∅ ∈ X) (sym H1) _). apply ZFinpairing. now left. }
        apply ZFinempty in H2. destruct H2.
  - clear x Hx. intros x IH y Hy H. assert (ZFsuc x ∈ ZFsuc y) as H0.
    { refine (transpS (fun X => ZFsuc x ∈ X) H _). apply ZFinpairing. now left. }
    apply ZFinpairing in H0. destruct H0 as [ H0 | H0 ].
    + exact H0.
    + assert (x ≡ y).
      { apply inSetSingl. refine (transpS (fun X => x ∈ X) H0 _). apply ZFinpairing. now left. }
      destruct H1. assert (setSingl x ≡ x).
      { apply inSetSingl. refine (transpS (fun X => setSingl x ∈ X) H0 _). apply ZFinpairing. now right. }
      exact (trans H0 H1).
Qed.

Lemma nat_to_ω_inj {n m : nat} : nat_to_ω n ≡ nat_to_ω m -> n ≡ m.
Proof.
  revert m. induction n.
  - intros m H. destruct m as [ | m ].
    + easy.
    + cbn in H. apply zero_ne_suc in H. destruct H.
  - intros m H. destruct m as [ | m ].
    + cbn in H. apply sym in H. apply zero_ne_suc in H. destruct H.
    + cbn in H. apply suc_inj in H ; try (now apply nat_to_ω_typing).
      refine (fequal S _). now apply IHn.
Qed.

(* Definition of the recursor (messy, should eventually be rewritten) *)

Definition natrel (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) :=
  { x ϵ setSigma n ω P ∣
      ∀ X ∈ 𝒫 (setSigma n ω P), ⟨ ∅ ; pz ⟩ ∈ X
      -> (∀ y ∈ X, ⟨ ZFsuc (setFstSigma n ω P y) ; ps (setSndSigma n ω P y) ⟩ ∈ X)
      -> x ∈ X }.

Lemma zero_in_natrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) : ⟨ ∅ ; pz ⟩ ∈ natrel n P pz ps. 
Proof.
  apply ZFincomp. split.
  - apply setMkSigma_typing. exact HP. apply zero_typing. exact Hpz.
  - intros X HX Hz Hs. exact Hz.
Qed.

Lemma suc_in_natrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {x : ZFSet} (Hx : x ∈ natrel n P pz ps) :
  ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setSndSigma n ω P x) ⟩ ∈ natrel n P pz ps. 
Proof.
  apply ZFincomp. split.
  - apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply setMkSigma_typing.
    + exact HP.
    + apply suc_typing. apply setFstSigma_typing. exact HP. exact Hx1.
    + apply Hps.
      * apply setFstSigma_typing. exact HP. exact Hx1.
      * apply setSndSigma_typing. exact HP. exact Hx1.
  - intros X HS Hz Hs. apply Hs. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. now apply Hx2.
Qed.

Lemma suc_in_natrel' {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m pm : ZFSet} (Hm : m ∈ ω) (Hpm : pm ∈ P m) (H : ⟨ m ; pm ⟩ ∈ natrel n P pz ps) :
  ⟨ ZFsuc m ; ps pm ⟩ ∈ natrel n P pz ps. 
Proof.
  refine (transpS (fun X => X ∈ _) _ (suc_in_natrel (x := ⟨ m ; pm ⟩) HP Hpz Hps _)).
  - refine (fequal2 (fun x y => ⟨ ZFsuc x ; ps y ⟩) _ _).
    + apply setSigmaβ1. exact HP. assumption. assumption.
    + apply setSigmaβ2. exact HP. assumption. assumption.
  - exact H.
Qed.

Definition natrelU_zero (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) :=
  { x ϵ natrel n P pz ps ∣ setFstSigma n ω P x ≡ ∅ -> setSndSigma n ω P x ≡ pz }.

Lemma zero_in_natrelU_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) 
  : ⟨ ∅ ; pz ⟩ ∈ natrelU_zero n P pz ps.
Proof.
  apply ZFincomp. split.
  - now apply zero_in_natrel.
  - intros _. apply setSigmaβ2 ; try assumption. apply zero_typing.
Qed.

Lemma suc_in_natrelU_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {x : ZFSet} (Hx : x ∈ natrelU_zero n P pz ps) :
  ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setSndSigma n ω P x) ⟩ ∈ natrelU_zero n P pz ps. 
Proof.
  apply ZFincomp. split.
  - apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. now apply suc_in_natrel.
  - assert (x ∈ setSigma n ω P) as Hx2.
    { apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. exact Hx. }
    intro H. assert (ZFsuc (setFstSigma n ω P x) ≡ ∅).
    { refine (trans (sym _) H). apply setSigmaβ1. apply HP.
      - apply suc_typing. apply setFstSigma_typing. exact HP. exact Hx2.
      - apply Hps.
        + apply setFstSigma_typing. exact HP. exact Hx2.
        + apply setSndSigma_typing. exact HP. exact Hx2. }
    pose proof (zero_ne_suc _ (sym H0)) as Habs. destruct Habs.
Qed.

Lemma natrel_incl_natrelU_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  natrel n P pz ps ⊂ natrelU_zero n P pz ps.
Proof.
  intros x Hx. pose proof Hx as Hx2. apply ZFincomp in Hx2. destruct Hx2 as [ Hx2 Hx3 ]. apply Hx3.
  - clear x Hx Hx2 Hx3. apply ZFinpower. intros x Hx. apply ZFincomp in Hx.
    destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. now destruct Hx as [ Hx _ ].
  - apply (zero_in_natrelU_zero HP Hpz).
  - intros x' Hx'. apply (suc_in_natrelU_zero HP Hpz Hps Hx').
Qed.

Lemma natrel_funrel_zero {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  ∃! x ∈ P ∅, ⟨ ∅ ; x ⟩ ∈ natrel n P pz ps.
Proof.
  exists pz. split.
  - split. exact Hpz. now apply zero_in_natrel.
  - intros x Hx. destruct Hx as [ Hx1 Hx2 ]. apply natrel_incl_natrelU_zero in Hx2 ; try assumption.
    apply ZFincomp in Hx2. destruct Hx2 as [ Hx2 Hx3 ]. refine (trans (sym (Hx3 _)) _).
    + apply setSigmaβ1. exact HP. apply zero_typing. assumption.
    + apply setSigmaβ2. exact HP. apply zero_typing. assumption.
Qed.

Definition natrelU_suc (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) (m pm : ZFSet) :=
  { x ϵ natrel n P pz ps ∣ setFstSigma n ω P x ≡ m -> setSndSigma n ω P x ≡ pm }.

Lemma zero_in_natrelU_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {m pm : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) 
  : ⟨ ∅ ; pz ⟩ ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm).
Proof.
  apply ZFincomp. split.
  - now apply zero_in_natrel.
  - intro H. assert (∅ ≡ ZFsuc m) as Habs.
    { refine (trans (sym _) H). apply setSigmaβ1 ; try assumption. apply zero_typing. }
    apply zero_ne_suc in Habs. destruct Habs.
Qed.

Lemma suc_in_natrelU_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {m pm : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hm : m ∈ ω)
  (Hpm : pm ∈ P m) (IH1 : ⟨ m ; pm ⟩ ∈ natrel n P pz ps) (IH2 : ∀ pm' ∈ P m, ⟨ m ; pm' ⟩ ∈ natrel n P pz ps -> pm ≡ pm')
  {x : ZFSet} (Hx : x ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm)) :
  ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setSndSigma n ω P x) ⟩ ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm).
Proof.
  apply ZFincomp. split.
  - apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. now apply suc_in_natrel.
  - intro H. assert (x ∈ setSigma n ω P) as Hx0.
    { apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. now destruct Hx as [ Hx _ ]. }
    assert (setFstSigma n ω P x ∈ ω) as Hx1.
    { now apply setFstSigma_typing. }
    assert (setSndSigma n ω P x ∈ P (setFstSigma n ω P x)) as Hx2.
    { now apply setSndSigma_typing. }
    assert (setFstSigma n ω P x ≡ m) as Hx3.
    { apply suc_inj ; try assumption. refine (trans (sym _) H).
      apply setSigmaβ1 ; try assumption. now apply suc_typing. now apply Hps. }
    clear H. set (pm' := setSndSigma n ω P x). assert (x ≡ ⟨ m ; pm' ⟩) as Hx4.
    { refine (trans _ (fequal (fun X => ⟨ X ; pm' ⟩) Hx3)). now apply setSigmaη. }
    assert (⟨ m ; pm' ⟩ ∈ natrel n P pz ps) as H0.
    { refine (transpS (fun X => X ∈ _) Hx4 _). apply ZFincomp in Hx. now destruct Hx as [ Hx _ ]. }
    apply IH2 in H0.
    2:{ refine (transpS (fun X => pm' ∈ P X) Hx3 _). now apply setSndSigma_typing. }
    refine (trans _ (fequal ps (sym H0))). apply setSigmaβ2 ; try assumption.
    + apply suc_typing. now apply setFstSigma_typing.
    + apply Hps. now apply setFstSigma_typing. now apply setSndSigma_typing.
Qed.

Lemma natrel_incl_natrelU_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {m pm : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hm : m ∈ ω)
  (Hpm : pm ∈ P m) (IH1 : ⟨ m ; pm ⟩ ∈ natrel n P pz ps) (IH2 : ∀ pm' ∈ P m, ⟨ m ; pm' ⟩ ∈ natrel n P pz ps -> pm ≡ pm') :
  natrel n P pz ps ⊂ natrelU_suc n P pz ps (ZFsuc m) (ps pm).
Proof.
  intros x Hx. pose proof Hx as Hx2. apply ZFincomp in Hx2. destruct Hx2 as [ Hx2 Hx3 ]. apply Hx3.
  - clear x Hx Hx2 Hx3. apply ZFinpower. intros x Hx. apply ZFincomp in Hx.
    destruct Hx as [ Hx _ ]. apply ZFincomp in Hx. now destruct Hx as [ Hx _ ].
  - apply (zero_in_natrelU_suc HP Hpz).
  - intros x' Hx'. now apply (suc_in_natrelU_suc HP Hpz Hps).
Qed.

Lemma natrel_funrel_suc {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m : ZFSet} (Hm : m ∈ ω) (IH : ∃! x ∈ P m, ⟨ m ; x ⟩ ∈ natrel n P pz ps) :
  ∃! x ∈ P (ZFsuc m), ⟨ ZFsuc m ; x ⟩ ∈ natrel n P pz ps.
Proof.
  destruct IH as [ pm [ [ Hpm Hpm1 ] Hpm2 ] ]. exists (ps pm). split.
  - split. now apply Hps. now apply suc_in_natrel'.
  - intros y [ Hy1 Hy2 ]. assert (⟨ ZFsuc m; y ⟩ ∈ natrelU_suc n P pz ps (ZFsuc m) (ps pm)) as Hy3.
    { apply (natrel_incl_natrelU_suc HP Hpz Hps) ; try assumption. intros pm' Hpm' H. now apply Hpm2. }
    apply ZFincomp in Hy3. destruct Hy3 as [ Hy3 Hy4 ]. refine (trans (sym (Hy4 _)) _).
    + apply setSigmaβ1. exact HP. apply suc_typing. assumption. assumption.
    + apply setSigmaβ2. exact HP. apply suc_typing. assumption. assumption.
Qed.

Lemma natrel_funrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  ∀ m ∈ ω, ∃! x ∈ P m, ⟨ m ; x ⟩ ∈ natrel n P pz ps.
Proof.
  intros m0 Hm0. cbn. apply (nat_ind Hm0). 
  - now apply natrel_funrel_zero.
  - intros m Hm IH. now apply natrel_funrel_suc.
Qed.

Lemma natrel_funrel' {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  isFunRel ω (setFamUnion n ω P) (graphToRel (natrel n P pz ps)).
Proof.
  intros m Hm. pose proof (natrel_funrel HP Hpz Hps m Hm) as H. cbn in H.
  destruct H as [ pm [ [ Hpm H1 ] H2 ] ]. exists pm. split.
  - split.
    + exact (inSetFamUnion HP Hm Hpm).
    + exact H1.
  - intros y [ Hy1 Hy2 ]. apply H2. unfold graphToRel in Hy2. split.
    + apply ZFincomp in Hy2. destruct Hy2 as [ Hy2 _ ]. apply setMkSigma_detyping in Hy2.
      now destruct Hy2. exact HP.
    + exact Hy2.
Qed.

Lemma natrel_funrel'' {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m x y : ZFSet} (Hm : m ∈ ω) : ⟨ m ; x ⟩ ∈ natrel n P pz ps -> ⟨ m ; y ⟩ ∈ natrel n P pz ps -> x ≡ y.
Proof.
  intros Hx Hy. pose proof (natrel_funrel HP Hpz Hps m Hm) as H. destruct H as [ z [ [ Hz H1 ] H2 ] ].
  assert (x ∈ P m).
  { apply ZFincomp in Hx. destruct Hx as [ Hx _ ]. apply setMkSigma_detyping in Hx. now destruct Hx. exact HP. }
  assert (y ∈ P m).
  { apply ZFincomp in Hy. destruct Hy as [ Hy _ ]. apply setMkSigma_detyping in Hy. now destruct Hy. exact HP. }
  refine (trans (b := z) _ _).
  - refine (sym _). apply H2. now split.
  - apply H2. now split.
Qed.

Definition natrec (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet) (x : ZFSet) : ZFSet :=
  funRelApp ω (setFamUnion n ω P) (graphToRel (natrel n P pz ps)) x.

Lemma natrel_cong {l : nat} {P1 P2 : ZFSet -> ZFSet} {pz1 pz2 : ZFSet} {ps1 ps2 : ZFSet -> ZFSet} 
  (HPe : ∀ n ∈ ω, P1 n ≡ P2 n)
  (Hpze : pz1 ≡ pz2)
  (Hpse : ∀ n ∈ ω, ∀ p ∈ P1 n, ps1 p ≡ ps2 p) :
  natrel l P1 pz1 ps1 ≡ natrel l P2 pz2 ps2.
Proof.
  unfold natrel. apply ZFext.
  - intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
    { refine (transpS (fun X => x ∈ X) _ Hx1). now apply setSigma_cong. }
    intros y Hy1 Hy2 Hy3. apply Hx2.
    + refine (transpS (fun X => y ∈ 𝒫 X) (sym _) Hy1). now apply setSigma_cong.
    + destruct Hpze. assumption.
    + intros z Hz. refine (transp2S (fun X Y => ⟨ ZFsuc X ; Y ⟩ ∈ y) (sym _) (sym _) (Hy3 z Hz)).
      unfold setFstSigma. refine (fequal (fun X => setFstPair ω X z) _). now apply setFamUnion_cong.
      assert (setSndSigma l ω P1 z ≡ setSndSigma l ω P2 z).
      { unfold setSndSigma. refine (fequal (fun X => setSndPair ω X z) _). now apply setFamUnion_cong. }
      destruct H. assert (z ∈ setSigma l ω P1) as Hz2.
      { apply ZFinpower in Hy1. apply Hy1 in Hz. refine (transpS (fun X => z ∈ X) (sym _) Hz). now apply setSigma_cong. }
      refine (Hpse (setFstSigma l ω P1 z) _ _ _). unfold setFstSigma. apply setFstPair_typing.
      * unfold setSigma in Hz2. apply ZFincomp in Hz2. now destruct Hz2.
      * unfold setSndSigma. unfold setSigma in Hz2. apply ZFincomp in Hz2. now destruct Hz2. 
  - intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
    { refine (transpS (fun X => x ∈ X) (sym _) Hx1). now apply setSigma_cong. }
    intros y Hy1 Hy2 Hy3. apply Hx2.
    + refine (transpS (fun X => y ∈ 𝒫 X) _ Hy1). now apply setSigma_cong.
    + destruct Hpze. assumption.
    + intros z Hz. refine (transp2S (fun X Y => ⟨ ZFsuc X ; Y ⟩ ∈ y) _ _ (Hy3 z Hz)).
      unfold setFstSigma. refine (fequal (fun X => setFstPair ω X z) _). now apply setFamUnion_cong.
      assert (setSndSigma l ω P1 z ≡ setSndSigma l ω P2 z).
      { unfold setSndSigma. refine (fequal (fun X => setSndPair ω X z) _). now apply setFamUnion_cong. }
      destruct H. assert (z ∈ setSigma l ω P1) as Hz2.
      { apply ZFinpower in Hy1. apply Hy1 in Hz. refine (transpS (fun X => z ∈ X) (sym _) Hz). now apply setSigma_cong. }
      refine (Hpse (setFstSigma l ω P1 z) _ _ _). unfold setFstSigma. apply setFstPair_typing.
      * unfold setSigma in Hz2. apply ZFincomp in Hz2. now destruct Hz2.
      * unfold setSndSigma. unfold setSigma in Hz2. apply ZFincomp in Hz2. now destruct Hz2.
Qed.

Lemma natrec_cong {l : nat} {P1 P2 : ZFSet -> ZFSet} {pz1 pz2 m1 m2 : ZFSet} {ps1 ps2 : ZFSet -> ZFSet} 
  (HPe : ∀ n ∈ ω, P1 n ≡ P2 n)
  (Hpze : pz1 ≡ pz2)
  (Hpse : ∀ n ∈ ω, ∀ p ∈ P1 n, ps1 p ≡ ps2 p)
  (Hme : m1 ≡ m2) :
  natrec l P1 pz1 ps1 m1 ≡ natrec l P2 pz2 ps2 m2.
Proof.
  unfold natrec. destruct Hme. refine (fequal2 (fun X Y => funRelApp ω X (graphToRel Y) m1) _ _).
  - now apply setFamUnion_cong.
  - now apply natrel_cong.
Qed.

Lemma natrec_inrel {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {x : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hx : x ∈ ω) :
  ⟨ x ; natrec n P pz ps x ⟩ ∈ natrel n P pz ps.
Proof.
  change (graphToRel (natrel n P pz ps) x (natrec n P pz ps x)).
  apply funRelApp_inRel. now apply natrel_funrel'. assumption.
Qed.

Lemma natrec_typing {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet} {x : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) (Hx : x ∈ ω) :
  natrec n P pz ps x ∈ P x.
Proof.
  pose proof (natrec_inrel HP Hpz Hps Hx).
  unfold graphToRel in H. apply ZFincomp in H. destruct H as [ H _ ].
  apply setMkSigma_detyping in H. now destruct H. exact HP.
Qed.

Lemma natrec_β1 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m)) :
  natrec n P pz ps ∅ ≡ pz.
Proof.
  pose proof (natrec_inrel HP Hpz Hps zero_typing) as H.
  assert (⟨ ∅ ; pz ⟩ ∈ natrel n P pz ps) as H0. { now apply zero_in_natrel. }
  unshelve eapply (natrel_funrel'' HP Hpz Hps _ H H0). now apply zero_typing.
Qed.

Lemma natrec_β2 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps pm ∈ P (ZFsuc m))
  {m : ZFSet} (Hm : m ∈ ω) :
  natrec n P pz ps (ZFsuc m) ≡ ps (natrec n P pz ps m).
Proof.
  pose proof (natrec_inrel HP Hpz Hps (suc_typing Hm)) as H.
  assert (⟨ ZFsuc m ; ps (natrec n P pz ps m) ⟩ ∈ natrel n P pz ps) as H0.
  { apply suc_in_natrel' ; try assumption. now apply natrec_typing. now apply natrec_inrel. }
  unshelve eapply (natrel_funrel'' HP Hpz Hps _ H H0). now apply suc_typing.
Qed.

(* Variation on natrec where the successor case has an extra argument *)

Definition natrec2_pred (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet -> ZFSet) (m : ZFSet) : ZFSet :=
  { x ϵ setSigma n ω P ∣ setFstSigma n ω P x ≡ m }.

Definition natrec2_aux (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet -> ZFSet) (m : ZFSet) : ZFSet :=
  natrec n (natrec2_pred n P pz ps) ⟨ ∅ ; pz ⟩
           (fun x => ⟨ ZFsuc (setFstSigma n ω P x) ; ps (setFstSigma n ω P x) (setSndSigma n ω P x) ⟩) m.

Definition natrec2 (n : nat) (P : ZFSet -> ZFSet) (pz : ZFSet) (ps : ZFSet -> ZFSet -> ZFSet) (m : ZFSet) : ZFSet :=
  setSndSigma n ω P (natrec2_aux n P pz ps m).

Lemma natrec2_cong {l : nat} {P1 P2 : ZFSet -> ZFSet} {pz1 pz2 m1 m2 : ZFSet} {ps1 ps2 : ZFSet -> ZFSet -> ZFSet} 
  (HPe : ∀ n ∈ ω, P1 n ≡ P2 n)
  (Hpze : pz1 ≡ pz2)
  (Hpse : ∀ n ∈ ω, ∀ p ∈ P1 n, ps1 n p ≡ ps2 n p)
  (Hme : m1 ≡ m2) :
  natrec2 l P1 pz1 ps1 m1 ≡ natrec2 l P2 pz2 ps2 m2.
Proof.
  unfold natrec2. unfold setSndSigma. refine (fequal2 (setSndPair ω) _ _).
  - now apply setFamUnion_cong.
  - unfold natrec2_aux. apply natrec_cong ; try assumption.
    + intros n Hn. unfold natrec2_pred. apply ZFext.
      * intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
        refine (transpS (fun X => x ∈ X) _ Hx1). now apply setSigma_cong.
        refine (trans (sym _) Hx2). unfold setFstSigma. refine (fequal (fun X => setFstPair ω X x) _).
        now apply setFamUnion_cong.
      * intros x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ]. apply ZFincomp. split.
        refine (transpS (fun X => x ∈ X) (sym _) Hx1). now apply setSigma_cong.
        refine (trans (sym _) Hx2). unfold setFstSigma. refine (fequal (fun X => setFstPair ω X x) (sym _)).
        now apply setFamUnion_cong.
    + now destruct Hpze.
    + intros n Hn p Hp. assert (setFstSigma l ω P1 p ≡ setFstSigma l ω P2 p) as H1.
      { unfold setFstSigma. refine (fequal (fun X => setFstPair ω X p) _). now apply setFamUnion_cong. }
      assert (setSndSigma l ω P1 p ≡ setSndSigma l ω P2 p) as H2.
      { unfold setFstSigma. refine (fequal (fun X => setSndPair ω X p) _). now apply setFamUnion_cong. }
      refine (fequal2 (fun X Y => ⟨ ZFsuc X ; Y ⟩) _ _).
      * apply H1.
      * destruct H1. destruct H2. unfold natrec2_pred in Hp. apply ZFincomp in Hp.
        destruct Hp as [ Hp1 Hp2 ]. apply ZFincomp in Hp1. destruct Hp1 as [ Hp0 Hp1 ].
        apply Hpse ; try assumption. unfold setFstSigma. now apply setFstPair_typing. 
Qed.

Lemma natrec2_typing_aux1 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  ∀ m ∈ ω, natrec2_pred n P pz ps m ∈ 𝕍 n.
Proof.
  intros x Hx. apply setComp_sorting. apply setSigma_typing. 2:assumption. now apply ZFuniv_uncountable.
Qed.

Lemma natrec2_typing_aux2 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  ⟨ ∅; pz ⟩ ∈ natrec2_pred n P pz ps ∅.
Proof.
  apply ZFincomp. split.
  - apply setMkSigma_typing ; try assumption. now apply zero_typing.
  - apply setSigmaβ1 ; try assumption. now apply zero_typing.
Qed.

Lemma natrec2_typing_aux3 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  ∀ m ∈ ω, ∀ x ∈ natrec2_pred n P pz ps m,
    ⟨ ZFsuc (setFstSigma n ω P x); ps (setFstSigma n ω P x) (setSndSigma n ω P x) ⟩ ∈ natrec2_pred n P pz ps (ZFsuc m).
Proof.
  intros m Hm x Hx. apply ZFincomp in Hx. destruct Hx as [ Hx1 Hx2 ].
  unshelve epose proof (Hps (setFstSigma n ω P x) _ (setSndSigma n ω P x) _).
  now apply setFstSigma_typing. now apply setSndSigma_typing. cbn in H. apply ZFincomp. split.
  - apply setMkSigma_typing ; try assumption. apply suc_typing. now apply setFstSigma_typing.
  - refine (trans (setSigmaβ1 HP _ H) (fequal ZFsuc Hx2)). apply suc_typing. now apply setFstSigma_typing.
Qed.

Lemma natrec2_aux_typing {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} {m : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) (Hm : m ∈ ω) :
  natrec2_aux n P pz ps m ∈ natrec2_pred n P pz ps m.
Proof.
  apply (natrec_typing (P := natrec2_pred n P pz ps)) ; try assumption.
  - apply (natrec2_typing_aux1 HP Hpz Hps).
  - apply (natrec2_typing_aux2 HP Hpz Hps).
  - apply (natrec2_typing_aux3 HP Hpz Hps).
Qed.

Lemma natrec2_typing {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} {m : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) (Hm : m ∈ ω) :
  natrec2 n P pz ps m ∈ P m.
Proof.
  pose proof (natrec2_aux_typing HP Hpz Hps Hm) as H. apply ZFincomp in H. destruct H as [ H1 H2 ].
  unfold natrec2. refine (transpS (fun X => setSndSigma n ω P (natrec2_aux n P pz ps m) ∈ P X) H2 _).
  now apply setSndSigma_typing.
Qed.

Lemma natrec2_β1 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} 
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) :
  natrec2 n P pz ps ∅ ≡ pz.
Proof.
  refine (trans (fequal (setSndSigma n ω P) _) _).
  - apply (natrec_β1 (natrec2_typing_aux1 HP Hpz Hps) (natrec2_typing_aux2 HP Hpz Hps) (natrec2_typing_aux3 HP Hpz Hps)).
  - apply setSigmaβ2 ; try assumption. now apply zero_typing.
Qed.

Lemma natrec2_β2 {n : nat} {P : ZFSet -> ZFSet} {pz : ZFSet} {ps : ZFSet -> ZFSet -> ZFSet} {m : ZFSet}
  (HP : ∀ m ∈ ω, P m ∈ 𝕍 n) (Hpz : pz ∈ P ∅) (Hps : ∀ m ∈ ω, ∀ pm ∈ P m, ps m pm ∈ P (ZFsuc m)) (Hm : m ∈ ω) :
  natrec2 n P pz ps (ZFsuc m) ≡ ps m (natrec2 n P pz ps m).
Proof.
  refine (trans (fequal (setSndSigma n ω P) _) _).
  { apply (natrec_β2 (natrec2_typing_aux1 HP Hpz Hps) (natrec2_typing_aux2 HP Hpz Hps) (natrec2_typing_aux3 HP Hpz Hps) Hm). }
  change (setSndSigma n ω P ⟨ ZFsuc (setFstSigma n ω P (natrec2_aux n P pz ps m)) ;
                              ps (setFstSigma n ω P (natrec2_aux n P pz ps m)) (natrec2 n P pz ps m) ⟩
            ≡ ps m (natrec2 n P pz ps m)).
  assert (setFstSigma n ω P (natrec2_aux n P pz ps m) ≡ m) as H.
  { pose proof (natrec2_aux_typing HP Hpz Hps Hm). apply ZFincomp in H. now destruct H. }
  refine (trans (fequal (fun X => setSndSigma n ω P ⟨ ZFsuc X ; ps X (natrec2 n P pz ps m) ⟩) H) _).
  apply setSigmaβ2 ; try assumption.
  - now apply suc_typing.
  - apply Hps. assumption. now apply natrec2_typing.
Qed.


