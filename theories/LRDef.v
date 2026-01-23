
From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From AccInSProp Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl Util BasicAST Typing BasicMetaTheory Reduction. 
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import CombineNotations.



Definition TmRel := term -> term -> Prop.

Definition LogRel := term -> term -> TmRel -> Prop.

Definition same_rel (R1 R2 : term -> term -> Prop) := forall t u, R1 t u <-> R2 t u.

Notation "R1 <~> R2" :=  (forall t u, R1 t u <-> R2 t u) (at level 50, R2 at next level).

Definition LRΩ : LogRel := fun A B R => ∙ ⊢d< Ax prop > A ≡ B : Sort prop /\ forall t u : term, R t u <-> ∙ ⊢d< prop > t ≡ u : A.

Inductive ϵNat : TmRel :=
| ϵzero t1 t2 :
    ∙ ⊢d< ty 0 > t1 -->>! zero : Nat ->
    ∙ ⊢d< ty 0 > t2 -->>! zero : Nat ->
    ϵNat t1 t2
| ϵsucc t1 t2 t1' t2' :
    ∙ ⊢d< ty 0 > t1 -->>! succ t1' : Nat ->
    ∙ ⊢d< ty 0 > t2 -->>! succ t2' : Nat ->
    ϵNat t1' t2' ->
    ϵNat t1 t2.



Definition ϵPi i j S1 S2 (ϵS : TmRel) T1 T2 (ϵT : term -> term -> TmRel) : TmRel
    := fun f1 f2 =>
        ∙ ⊢d< Ru i j > f1 ≡ f2 : Pi i j S1 T1 /\
        forall s1 s2 (ϵs : ϵS s1 s2), ϵT s1 s2 (app i j S1 T1 f1 s1) (app i j S2 T2 f2 s2).

(* we use a module to hide the implementation details *)
Module Type LogRelM.
    Axiom LR : level -> LogRel.


    Notation "⊩< l > A ≡ B ↓ R" :=  (LR l A B R) (at level 50, l, A, B, R at next level).

    Axiom LR_prop : forall A1 A2 R,
        ∙ ⊢d< Ax prop > A1 ≡ A2 : Sort prop ->
        R <~> (fun t u => ∙ ⊢d< prop > t ≡ u : A1) ->
        ⊩< prop > A1 ≡ A2 ↓ R.

    Axiom LR_nat : forall A1 A2 R,
        ∙ ⊢d< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0) ->
        ∙ ⊢d< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0) ->
        R <~> ϵNat ->
        ⊩< ty 0 > A1 ≡ A2 ↓ R.

    Axiom LR_U : forall l A1 A2 R,
        ∙ ⊢d< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l) ->
        ∙ ⊢d< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l) ->
        R <~> (fun B1 B2 => exists R, ⊩< l > B1 ≡ B2 ↓ R) ->
        ⊩< Ax l > A1 ≡ A2 ↓ R.

    Axiom LR_pi : forall i k A1 A2 S1 S2 ϵS T1 T2 ϵT R,
        ∙ ⊢d< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) ->
        ∙ ⊢d< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
        ∙ ,, (i, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
        ⊩< i > S1 ≡ S2 ↓ ϵS ->
        (forall s1 s2 (ϵs : ϵS s1 s2), ⊩< (ty k) > (T1 <[ s1 ..]) ≡ (T2 <[ s2 ..]) ↓ (ϵT s1 s2)) ->
        R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
        ⊩< Ru i (ty k) > A1 ≡ A2 ↓ R.

    Axiom LR_ind : forall
        (P : forall l A B R, Prop)
        (p_prop : forall A B R (p : LRΩ A B R), P prop A B R)
        (p_nat : forall A1 A2 R
            (A1_red_nat : ∙ ⊢d< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0))
            (A2_red_nat : ∙ ⊢d< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0)),
            R <~> ϵNat ->
            P (ty 0) A1 A2 R)
        (p_U : forall l A1 A2 R
            (A1_red_U : ∙ ⊢d< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l))
            (A2_red_U : ∙ ⊢d< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l)),
            (forall B1 B2 R, ⊩< l > B1 ≡ B2 ↓ R -> P l B1 B2 R) ->
            R <~> (fun B1 B2 => exists R, ⊩< l > B1 ≡ B2 ↓ R) ->
            P (Ax l) A1 A2 R)
        (p_pi : forall i k A1 A2 S1 S2 ϵS T1 T2 ϵT R
            (A1_red_pi : ∙ ⊢d< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)))
            (A2_red_pi : ∙ ⊢d< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)))
            (T1_eq_T2 : ∙ ,, (i, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k))
            (LR_S : ⊩< i > S1 ≡ S2 ↓ ϵS)
            (LR_T : forall s1 s2 (ϵs : ϵS s1 s2),
                        ⊩< ty k > T1 <[ s1 ..] ≡ T2 <[ s2 ..] ↓ ϵT s1 s2),
            R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
            P i S1 S2 ϵS ->
            (forall s1 s2 (ϵs : ϵS s1 s2), P (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
            P (Ru i (ty k)) A1 A2 R)
        (l : level) (A B : term) (R : TmRel) (x : ⊩< l > A ≡ B ↓ R), P l A B R.
End LogRelM.


Module LogRelImpl : LogRelM.

    Definition lvl_to_nat l :=
        match l with
        | prop => O
        | ty n => S n
        end.

    Definition nat_to_lvl n :=
        match n with
        | O => prop
        | S n => ty n
        end.

    Lemma lvl_to_nat_to_lvl l : nat_to_lvl (lvl_to_nat l) = l.
    Proof.
        destruct l.
        - auto.
        - auto.
    Qed.


    Notation "l ⊴ l'" :=  ((lvl_to_nat l) <= (lvl_to_nat l')) (at level 50, l' at next level).

    Notation "l ◃ l'" :=  ((lvl_to_nat l) < (lvl_to_nat l')) (at level 50, l' at next level).


    Lemma lvl_leq_prop l : prop ⊴ l.
    Proof.
        simpl. destruct l; lia.
    Qed.


    Lemma lvl_eq_to_leq {i j} : i = j -> i ⊴ j.
    Proof.
        intro H. rewrite H. auto.
    Qed.


    Lemma leq_ru_left {i} {k} : i ⊴ Ru i (ty k).
    Proof.
        destruct i; simpl; lia.
    Qed.

    Lemma leq_ru_right {i} {k} : ty k ⊴ Ru i (ty k).
    Proof.
        destruct i; simpl; lia.
    Qed.


    Lemma lt_ty_ax {l} : l ◃ ty (ax l).
    Proof.
        destruct l; simpl; lia.
    Qed.

    Lemma aux {i j k} : j ◃ ty k -> j ◃ ty (ru i k).
    Proof.
        intro H. unfold ru. destruct i; simpl in *; lia.
    Qed.


    Inductive LRTy : forall (k : nat) (rec : forall j, j ◃ (ty k) -> LogRel), LogRel :=
    | LRTy_nat A1 A2 rec R :
        ∙ ⊢d< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0) ->
        ∙ ⊢d< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0) ->
        R <~> ϵNat ->
        LRTy 0 rec A1 A2 R
    | LRTy_pi1 i k A1 A2 S1 S2 ϵS T1 T2 ϵT R
        (rec : forall j, j ◃ ty k -> LogRel)
        (q : i ◃ ty k) :
        ∙ ⊢d< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) ->
        ∙ ⊢d< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
        ∙ ,, (i, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
        rec i q S1 S2 ϵS ->
        (forall s1 s2 (ϵs : ϵS s1 s2),
            LRTy k rec (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
        R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
        LRTy k rec A1 A2 R
    | LRTy_pi2 k A1 A2 S1 S2 ϵS T1 T2 ϵT R
        (rec : forall j, j ◃ ty k -> LogRel) :
        ∙ ⊢d< Ax (Ru (ty k) (ty k)) > A1 -->>! Pi (ty k) (ty k) S1 T1 : Sort (Ru (ty k) (ty k)) ->
        ∙ ⊢d< Ax (Ru (ty k) (ty k)) > A2 -->>! Pi (ty k) (ty k) S2 T2 : Sort (Ru (ty k) (ty k)) ->
        ∙ ,, (ty k, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
        LRTy k rec S1 S2 ϵS ->
        (forall s1 s2 (ϵs : ϵS s1 s2),
            LRTy k rec (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
        R <~> (ϵPi (ty k) (ty k) S1 S2 ϵS T1 T2 ϵT) ->
        LRTy k rec A1 A2 R
    | LRTy_pi3 n k A1 A2 S1 S2 ϵS T1 T2 ϵT R
        (rec : forall j, j ◃ ty n -> LogRel)
        (q : k < n) :
        ∙ ⊢d< Ax (Ru (ty n) (ty k)) > A1 -->>! Pi (ty n) (ty k) S1 T1 : Sort (Ru (ty n) (ty k)) ->
        ∙ ⊢d< Ax (Ru (ty n) (ty k)) > A2 -->>! Pi (ty n) (ty k) S2 T2 : Sort (Ru (ty n) (ty k)) ->
        ∙ ,, (ty n, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
        LRTy n rec S1 S2 ϵS ->
        (forall s1 s2 (ϵs : ϵS s1 s2),
            rec (ty k) (ltac :(simpl; lia)) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
        R <~> (ϵPi (ty n) (ty k) S1 S2 ϵS T1 T2 ϵT) ->
        LRTy n rec A1 A2 R
    | LRTy_U l A1 A2 rec R :
        ∙ ⊢d< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l) ->
        ∙ ⊢d< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l) ->
        R <~> (fun B1 B2 => exists R, rec l lt_ty_ax B1 B2 R) ->
        LRTy (ax l) rec A1 A2 R.

    Definition LR' (l : level) (s : Acc (λ i j : level, i ◃ j) l) : LogRel.
        refine (@Fix_F _ (fun i j => i ◃ j) (fun _ => LogRel) _ l _).
        - intros. destruct x.
            + apply (LRTy n). apply X.
            + apply LRΩ.
        - exact s.
    Defined.

    Lemma LRTy_respects_iff_aux n A B R rec rec' :
        (forall l p A B R, rec l p A B R <-> rec' l p A B R) ->
        LRTy n rec A B R -> LRTy n rec' A B R.
    Proof.
        intros rec_iff_rec' lr. induction lr; try rewrite rec_iff_rec' in *.
        - econstructor; eauto.
        - econstructor; eauto.
        - eapply LRTy_pi2; eauto.
        - eapply LRTy_pi3; eauto.
        intros. rewrite <- rec_iff_rec'. eauto.
        - eapply LRTy_U; eauto. setoid_rewrite <- rec_iff_rec'. eauto.
    Qed.

    Lemma wf_lvl_lt : well_founded (λ i j : level, i ◃ j).
    Proof.
        apply wf_inverse_image. apply lt_wf.
    Qed.

    Lemma LR_acc_irrel l s s' A B R :
        LR' l s A B R -> LR' l s' A B R.
    Proof.
        generalize l s s' A B R. clear l s s' A B R.
        refine (@well_founded_ind _ (fun i j => i ◃ j) _ _ _).
        apply wf_lvl_lt.
        intros. destruct x.
        - unfold LR'. unfold LR' in H0. rewrite <- Fix_F_eq in *.
        eapply LRTy_respects_iff_aux in H0. eapply H0.
        intros. split. intros. unfold LR' in H. eapply H in H1. eapply H1. eauto.
        intros. unfold LR' in H. eapply H in H1. eapply H1. eauto.
        - unfold LR' in *. rewrite <- Fix_F_eq in *. eauto.
    Qed.

    Lemma LR_prop_eq s : LR' prop s = LRΩ.
    Proof.
        unfold LR'. rewrite <- Fix_F_eq. auto.
    Qed.



    Definition LR l := LR' l (wf_lvl_lt l).

    Lemma LR_ty_eq i s A B R :
        LR' (ty i) s A B R <-> LRTy i (fun l x => LR l) A B R.
    Proof.
        unfold LR'. unfold LR.

        rewrite <- Fix_F_eq.
        split.
        intros. eapply LRTy_respects_iff_aux in H. eapply H.
        intros. split; intros.
        pose (K := LR_acc_irrel _ (Acc_inv s p) (wf_lvl_lt l)).
        unfold LR' in K.
        eapply K in H0. eauto.
        pose (K := LR_acc_irrel _ (wf_lvl_lt l) (Acc_inv s p)).
        unfold LR' in K.
        eapply K in H0. eauto.

        intros. eapply LRTy_respects_iff_aux in H. eapply H.
        intros. split; intros.
        pose (K := LR_acc_irrel _ (wf_lvl_lt l) (Acc_inv s p)).

        unfold LR' in K.
        eapply K in H0. eauto.
        pose (K := LR_acc_irrel _ (Acc_inv s p) (wf_lvl_lt l)).
        unfold LR' in K.
        eapply K in H0. eauto.
    Qed.



    Definition LR_prop A1 A2 R :
        ∙ ⊢d< Ax prop > A1 ≡ A2 : Sort prop ->
        R <~> (fun t u => ∙ ⊢d< prop > t ≡ u : A1) ->
        LR prop A1 A2 R.
    Proof.
        intros.
        unfold LR. rewrite LR_prop_eq. split; eauto.
    Qed.

    Definition LR_nat A1 A2 R :
        ∙ ⊢d< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0) ->
        ∙ ⊢d< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0) ->
        R <~> ϵNat ->
        LR (ty 0) A1 A2 R.
    Proof.
        intros. unfold LR. rewrite LR_ty_eq.
        constructor; eauto.
    Qed.

    Definition LR_U l A1 A2 R :
        ∙ ⊢d< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l) ->
        ∙ ⊢d< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l) ->
        R <~> (fun B1 B2 => exists R, LR l B1 B2 R) ->
        LR (Ax l) A1 A2 R.
    Proof.
        intros. unfold Ax. unfold LR. rewrite LR_ty_eq.
        constructor; eauto.
    Qed.


    Definition LR_pi i k A1 A2 S1 S2 ϵS T1 T2 ϵT R :
        ∙ ⊢d< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) ->
        ∙ ⊢d< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) ->
        ∙ ,, (i, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
        LR i S1 S2 ϵS ->
        (forall s1 s2 (ϵs : ϵS s1 s2), LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
        R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
        LR (Ru i (ty k)) A1 A2 R.
    Proof.
        intros. unfold Ru. unfold LR. rewrite LR_ty_eq.
        assert (i ⊴ (ty k) \/ ty k ◃ i) by eauto using Nat.le_gt_cases.
        destruct H5. inversion H5.
        - pose proof (f_equal nat_to_lvl H7) as H'. rewrite lvl_to_nat_to_lvl in H'. rewrite H' in *.
        simpl. assert (max k k = k) by lia. rewrite H6. eapply LRTy_pi2; eauto.
        unfold LR in H2. simpl in H2. rewrite <- LR_ty_eq.  eauto.
        unfold LR in H3. intros. rewrite <- LR_ty_eq. eauto.
        - assert (ru i k = k). unfold ru. destruct i. simpl in H7. lia. auto.
        rewrite H8. eapply LRTy_pi1; eauto.
        simpl. lia.
        unfold LR in H3. intros.
        rewrite <- LR_ty_eq. eauto.
        - destruct i. 2:inversion H5.
        simpl in H5. assert (ru (ty n) k = n). unfold ru. lia.
        rewrite H6. eapply LRTy_pi3; eauto. lia.
        rewrite <- LR_ty_eq. eauto.
    Qed.



    Definition LR_ind
        (P : forall l A B R, Prop)
        (p_prop : forall A B R (p : LRΩ A B R), P prop A B R)
        (p_nat : forall A1 A2 R
            (A1_red_nat : ∙ ⊢d< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0))
            (A2_red_nat : ∙ ⊢d< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0)),
            R <~> ϵNat ->
            P (ty 0) A1 A2 R)
        (p_U : forall l A1 A2 R
            (A1_red_U : ∙ ⊢d< Ax (Ax l) > A1 -->>! Sort l : Sort (Ax l))
            (A2_red_U : ∙ ⊢d< Ax (Ax l) > A2 -->>! Sort l : Sort (Ax l)),
            (forall B1 B2 R, LR l B1 B2 R -> P l B1 B2 R) ->
            R <~> (fun B1 B2 => exists R, LR l B1 B2 R) ->
            P (Ax l) A1 A2 R)
        (p_pi : forall i k A1 A2 S1 S2 ϵS T1 T2 ϵT R
            (A1_red_pi : ∙ ⊢d< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)))
            (A2_red_pi : ∙ ⊢d< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)))
            (T1_eq_T2 : ∙ ,, (i, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k))
            (LR_S : LR i S1 S2 ϵS)
            (LR_T : forall s1 s2 (ϵs : ϵS s1 s2),
                    LR (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)),
            R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
            P i S1 S2 ϵS ->
            (forall s1 s2 (ϵs : ϵS s1 s2), P (ty k) (T1 <[ s1 ..]) (T2 <[ s2 ..]) (ϵT s1 s2)) ->
            P (Ru i (ty k)) A1 A2 R)
        (l : level) (A B : term) (R : TmRel) (x : LR l A B R) : P l A B R.
    Proof.
        generalize l A B R x.
        clear A B R l x.
        refine (@well_founded_ind _ (fun l l' => l ◃ l') _ _ _).
        apply wf_inverse_image. apply lt_wf.
        intros l H A B R x.
        destruct l.
        - unfold LR in x. rewrite LR_ty_eq in x.
        set (rec := (λ (l : level) (_ : l ◃ ty n), LR l)).
            assert (rec = (λ (l : level) (_ : l ◃ ty n), LR l)) by reflexivity.
            rewrite <- H0 in x.
            induction x.
            + apply p_nat; auto.
            + rewrite H0 in H4. rewrite H0 in H5.
            setoid_rewrite <- LR_ty_eq in H5.
            assert (k = ru i k). unfold ru. destruct i. simpl in q. lia. lia.
            rewrite H8 at 1. eapply p_pi; eauto.
            + rewrite H0 in H4. setoid_rewrite <- LR_ty_eq in H4.
            rewrite H0 in x. rewrite <- LR_ty_eq in x.
            assert (k = ru (ty k) k). simpl. lia.
            rewrite H7 at 1. eapply p_pi; eauto.
            + rewrite H0 in *. rewrite <- LR_ty_eq in x.
            assert (ty n = Ru (ty n) (ty k)). simpl. f_equal. lia. rewrite H6 at 1.
            eapply p_pi; eauto.
            intros. apply H. simpl. lia. auto.
            + rewrite H0 in H3. eapply p_U; eauto.
        - unfold LR in x. rewrite LR_prop_eq in x. apply p_prop. auto.
    Qed.
End LogRelImpl.

Export LogRelImpl.



Reserved Notation "⊩s σ ≡ τ : Δ" (at level 50, σ, τ, Δ at next level).


(* reducibility for substitutions *)
Inductive LR_subst : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
| LR_sempty (σ τ : nat -> term) : ⊩s σ ≡ τ : ∙
| LR_scons (σ τ : nat -> term) (Δ : ctx) l A R :
  ⊩s (↑ >> σ) ≡ (↑ >> τ) : Δ ->
  ⊩< l > A <[ (↑ >> σ) ] ≡ A <[ (↑ >> τ)] ↓ R ->
  R (σ var_zero) (τ var_zero) ->
  ⊩s σ ≡ τ : Δ ,, (l , A)
where "⊩s σ ≡ τ : Δ" := (LR_subst Δ σ τ).




(* validity *)
Definition LRv Γ l t u A :=
    forall σ1 σ2,
        ⊩s σ1 ≡ σ2 : Γ ->
        exists R,
            ⊩< l > A <[ σ1 ] ≡ A <[ σ2 ] ↓ R
            /\ R (t <[ σ1 ]) (u <[ σ2 ]).
Notation "Γ ⊨< l > t ≡ u : A" := (LRv Γ l t u A) (at level 50, l, t, u, A at next level).



