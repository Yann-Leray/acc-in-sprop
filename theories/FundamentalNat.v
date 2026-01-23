

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From AccInSProp
    Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl
    Util BasicAST Typing BasicMetaTheory
    Reduction LRDef LRBasicProps FundamentalAux.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.


Lemma ϵzero' : ϵNat zero zero.
Proof.
    eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
Qed.

Lemma ϵsucc' {t u} : ϵNat t u -> ϵNat (succ t) (succ u).
Proof.
    intros. eapply ϵsucc; eauto 7 using val_redd_to_whnf, typing, ctx_typing, ϵNat_escape, validity_conv_left, validity_conv_right.
Qed.

Lemma prefundamental_nat :
    ⊩< ty 0 > Nat ≡ Nat ↓ ϵNat.
Proof.
    eapply LR_nat; eauto using val_redd_to_whnf, typing, ctx_typing.
    reflexivity.
Qed.

Lemma fundamental_nat Γ :
    ⊢d Γ ->
    Γ ⊨< Ax (ty 0) > Nat ≡ Nat : Sort (ty 0).
Proof.
    unfold LRv. intros. simpl. rewrite <- helper_LR.
    eexists. eapply prefundamental_nat.
Qed.

Lemma fundamental_zero Γ :
    ⊢d Γ ->
    Γ ⊨< ty 0 > zero ≡ zero : Nat.
Proof.
    unfold LRv. intros. simpl.
    eexists. split. eauto using prefundamental_nat.
    eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
Qed.

Lemma fundamental_succ Γ t1 t2 :
    Γ ⊢d< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty 0 > succ t1 ≡ succ t2 : Nat.
Proof.
    intros. unfold LRv. intros.
    eexists. split. eauto using prefundamental_nat.
    eapply LRv_to_LR_tm in H0; eauto using prefundamental_nat, ϵsucc'.
Qed.

Lemma fundamental_conv Γ l A B t1 t2 :
    Γ ⊢d< l > t1 ≡ t2 : A ->
    Γ ⊨< l > t1 ≡ t2 : A ->
    Γ ⊢d< Ax l > A ≡ B : Sort l ->
    Γ ⊨< Ax l > A ≡ B : Sort l ->
    Γ ⊨< l > t1 ≡ t2 : B.
Proof.
    intros t1_conv_t2 LRv_t12 A_conv_B LRv_AB. unfold LRv. intros σ1 σ2 ϵσ12.
    assert (Γ ⊨< Ax l > B ≡ B : Sort l) as LRv_BB by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_AB as temp; eauto.
    destruct temp as (ϵAB & LR_AB).
    eapply LRv_to_LR_tm in LRv_t12 as LRv_t12; eauto.
    eapply LRv_to_LR_ty in LRv_BB as temp; eauto.
    destruct temp as (ϵBB & LR_BB).
    assert (ϵBB <~> ϵAB) as ϵBB_iff_ϵAB by eauto using LR_sym, LR_irrel.
    exists ϵBB. split; eauto.
    rewrite ϵBB_iff_ϵAB. eauto.
Qed.

Lemma nth_error_succ {X: Type} (x:X) l n a :
    nth_error (cons x l) (S n) = Some a ->
    nth_error l n = Some a.
Proof.
    intros. unfold nth_error in H. simpl in H. eauto.
Qed.





Lemma prefundamental_rec k P1 p_zero1 p_succ1 P2 p_zero2 p_succ2 ϵP:
    ∙ ,, (ty 0, Nat) ⊢d< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    ∙  ⊢d< ty k > p_zero1 ≡ p_zero2 : P1 <[ zero..] ->
    (∙ ,, (ty 0, Nat)),, (ty k, P1) ⊢d< ty k > p_succ1 ≡ p_succ2 : P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (forall n1 n2 (ϵn : ϵNat n1 n2),
        ⊩< ty k > P1 <[ n1..] ≡ P2 <[ n2..] ↓ ϵP n1 n2) ->
    ϵP zero zero p_zero1 p_zero2 ->
    (forall n1 n2 (ϵn : ϵNat n1 n2) t1 t2,
        ϵP n1 n2 t1 t2 ->
        ϵP (succ n1) (succ n2) (p_succ1 <[t1 .: n1 ..]) (p_succ2 <[t2 .: n2 ..])) ->
    forall n1 n2 (ϵn : ϵNat n1 n2), ϵP n1 n2 (rec (ty k) P1 p_zero1 p_succ1 n1) (rec (ty k) P2 p_zero2 p_succ2 n2).
Proof.
    intros. generalize n1 n2 ϵn. clear n1 n2 ϵn.
    apply ϵNat_ind; intros.
    - pose (LR' := H2 _ _ ϵzero').
      pose (LR'' := H2 _ _ (ϵzero _ _ H5 H6)).
      assert (ϵNat t1 zero) as ϵt1zero. eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
      pose (LR''' := H4 _ _ ϵt1zero).
      assert (ϵP zero zero <~> ϵP t1 zero) by eauto using LR_sym, LR_irrel.
      assert (ϵP t1 t2 <~> ϵP t1 zero) by eauto using LR_sym, LR_irrel.
      rewrite H8. rewrite <- H7.
      destruct H5, H6.
      eapply LR_irred_tm; eauto.
      eapply redd_rec_zero; eauto using validity_conv_left.
      eapply redd_conv. eapply redd_rec_zero;
      eauto 11 using validity_conv_right, subst_conv, substs_one, type_zero, type_conv, ctx_typing, subst_id_var1, conv_ty_in_ctx_conv, refl_subst, conv_refl, validity_conv_left, ctx_typing, validity_ty_ctx.
      eapply subst_conv; eauto using conv_sym, substs_one, LR_escape_tm, prefundamental_nat, ϵzero', ctx_nil.

    - pose (LR' := H2 _ _ (ϵsucc' H7)).
      pose (LR'' := H2 _ _ (ϵsucc _ _ _ _ H5 H6 H7)).
      assert (ϵNat t1 (succ t2')) as ϵt1succt2'. eapply ϵsucc; eauto using val_redd_to_whnf, typing, redd_whnf_to_conv, validity_conv_right.
      pose (LR''' := H2 _ _ ϵt1succt2').
      assert (ϵP (succ t1') (succ t2') <~> ϵP t1 (succ t2')) by eauto using LR_sym, LR_irrel.
      assert (ϵP t1 t2 <~> ϵP t1 (succ t2')) by eauto using LR_sym, LR_irrel.
      rewrite H10. rewrite <- H9.
      destruct H5, H6.
      eapply LR_irred_tm; eauto.
      eapply redd_rec_succ; eauto using validity_conv_left.
      eapply redd_conv.
      eapply redd_rec_succ; eauto 11 using validity_conv_right, subst_conv, substs_one, type_zero, type_conv, ctx_typing, substs_one, conv_ty_in_ctx_conv, refl_subst, conv_refl, subst_id_var1, ctx_typing, validity_ty_ctx.
      eapply subst_conv; eauto using conv_sym, substs_one, ϵsucc', prefundamental_nat, LR_escape_tm, ctx_nil.
Qed.



Lemma fundamental_rec Γ k P1 p_zero1 p_succ1 t1 P2 p_zero2 p_succ2 t2 :
    Γ,, (ty 0, Nat) ⊢d< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    Γ,, (ty 0, Nat) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    Γ ⊢d< ty k > p_zero1 ≡ p_zero2 : P1 <[ zero..] ->
    Γ ⊨< ty k > p_zero1 ≡ p_zero2 : P1 <[ zero..] ->
    (Γ,, (ty 0, Nat)),, (ty k, P1) ⊢d< ty k > p_succ1 ≡ p_succ2 : P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (Γ,, (ty 0, Nat)),, (ty k, P1) ⊨< ty k > p_succ1 ≡ p_succ2 : P1 <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    Γ ⊢d< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty 0 > t1 ≡ t2 : Nat ->
    Γ ⊨< ty k > rec (ty k) P1 p_zero1 p_succ1 t1 ≡ rec (ty k) P2 p_zero2 p_succ2 t2 : P1 <[ t1..].
Proof.
    intros P1_conv_P2 LRv_P12 pzero1_conv_pzero2 LRv_pzero12
        psucc1_conv_psucc2 LRv_psucc12 t1_conv_t2 LRv_t12.
    unfold LRv. intros σ1 σ2 ϵσ12.

    assert (Γ ⊨< ty 0 > t1 ≡ t1 : Nat) as LRv_t11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_tm in LRv_t12 as ϵt12; eauto using prefundamental_nat.
    eapply LRv_to_LR_tm in LRv_t11 as ϵt11; eauto using prefundamental_nat.

    eapply getLR_of_motive in ϵσ12 as temp; eauto. 2: simpl;eauto using prefundamental_nat.
    destruct temp as (eP & eP_eq & LR_P11 & LR_P12 & LR_P11').

    exists (eP (t1 <[ σ1]) (t2 <[ σ2])).
    (* exists eP. *)
    split; rasimpl. eauto.

    eapply prefundamental_rec; eauto.
    - eapply subst_conv; eauto using lift_subst, LR_subst_escape, validity_ty_ctx, validity_conv_left, ctx_typing, typing.
    - eapply subst_conv; eauto using LR_subst_escape, ctx_nil. rasimpl. reflexivity.
    - eapply subst_conv; eauto using lift_subst2, LR_subst_escape, validity_ty_ctx, validity_conv_left.
      econstructor. eauto using ctx_typing, typing.
      eapply subst_ty; eauto using validity_conv_left, ctx_typing, typing.
      eapply WellSubst_up; eauto using LR_subst_escape, validity_subst_conv_left, typing, ctx_typing.
      substify. rasimpl. reflexivity.
    - intros. rasimpl. eapply LR_P12. eauto.
    - pose (LR_Pzero := LR_P11 _ _ ϵzero'). eapply LRv_to_LR_tm in LRv_pzero12 as LR_pzero; eauto. rasimpl. eauto.
    - intros. rasimpl.
      pose (LR_Psucc := LR_P11 _ _ ϵn).
      assert (⊩s (t0 .: (n1 .: σ1)) ≡ (t3 .: (n2 .: σ2)) : (Γ ,, (ty 0, Nat)),, (ty k, P1))
        as ϵtnσ by eauto using LR_subst, prefundamental_nat.
      eapply LRv_to_LR_tm in LRv_psucc12; eauto. simpl. rasimpl. eauto using ϵsucc'.
Qed.


Lemma fundamental_rec_zero Γ k P p_zero p_succ :
    Γ,, (ty 0, Nat) ⊢d< Ax (ty k) > P : Sort (ty k) ->
    Γ,, (ty 0, Nat) ⊨< Ax (ty k) > P ≡ P : Sort (ty k) ->
    Γ ⊢d< ty k > p_zero : P <[ zero..] ->
    Γ ⊨< ty k > p_zero ≡ p_zero : P <[ zero..] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊢d< ty k > p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊨< ty k > p_succ ≡ p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    Γ ⊨< ty k > rec (ty k) P p_zero p_succ zero ≡ p_zero : P <[ zero..].
Proof.
    intros WtP LR_P Wtpzero LR_pzero Wtpsucc LR_psucc.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply fundamental_rec in ϵσ as temp; eauto using conv_refl, fundamental_zero, conv_zero, validity_ty_ctx.
    destruct temp as (ϵPzero & LR_Pzero & ϵpzero). exists ϵPzero. split; eauto.
    eapply LR_redd_tm; eauto.
    eauto using LR_escape_tm, validity_conv_left, redd_refl.
    eapply LR_escape_tm in ϵpzero; eauto. eapply validity_conv_right in ϵpzero.
    asimpl in ϵpzero. eapply type_inv in ϵpzero. dependent destruction ϵpzero.
    eapply red_to_redd.
    eapply red_conv. 2:eapply conv_sym; eauto.
    eapply red_rec_zero; eauto using conv_refl.
Qed.

Lemma fundamental_rec_succ Γ k P p_zero p_succ t :
    Γ,, (ty 0, Nat) ⊢d< Ax (ty k) > P : Sort (ty k) ->
    Γ,, (ty 0, Nat) ⊨< Ax (ty k) > P ≡ P : Sort (ty k) ->
    Γ ⊢d< ty k > p_zero : P <[ zero..] ->
    Γ ⊨< ty k > p_zero ≡ p_zero : P <[ zero..] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊢d< ty k > p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    (Γ,, (ty 0, Nat)),, (ty k, P) ⊨< ty k > p_succ ≡ p_succ : P <[ succ (var 1) .: ↑ >> (↑ >> var)] ->
    Γ ⊢d< ty 0 > t : Nat ->
    Γ ⊨< ty 0 > t ≡ t : Nat ->
    Γ ⊨< ty k > rec (ty k) P p_zero p_succ (succ t) ≡ p_succ <[ rec (ty k) P p_zero p_succ t .: t..] : P <[ (succ t)..].
Proof.
    intros WtP LR_P Wtpzero LR_pzero Wtpsucc LR_psucc Wtt LR_t.
    unfold LRv. intros σ1 σ2 ϵσ.
    assert (Γ ⊨< ty 0 > succ t ≡ succ t : Nat) as LR_succt by eauto using fundamental_succ, conv_refl.
    eapply fundamental_rec in LR_succt as temp; eauto using conv_refl, conv_succ.
    eapply temp in ϵσ as temp2. clear temp.
    destruct temp2 as (ϵPSt & LR_PSt & ϵst).
    eexists. split; eauto.
    eapply LR_redd_tm; eauto.
    eauto using LR_escape_tm, validity_conv_left, redd_refl.
    eapply LR_escape_tm in ϵst;eauto.
    eapply validity_conv_right in ϵst. asimpl in ϵst.
    eapply type_inv in ϵst. dependent destruction ϵst.
    eapply red_to_redd. eapply red_conv. 2:eapply conv_sym;eauto.
    eapply type_inv in t_Wt. dependent destruction t_Wt.
    eapply red_meta_conv.
    eapply red_rec_succ; eauto using conv_refl.
    all:rasimpl; reflexivity.
Qed.
