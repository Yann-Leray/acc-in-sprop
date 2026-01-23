Set Universe Polymorphism.

From Corelib.ssr Require Import ssreflect.
Require Import Sigma sum Observational Logic.

Set Warnings "-notation-overridden".

Inductive le : nat -> nat -> SProp :=
| le_O : forall n, le 0 n
| le_S : forall n m, le n m -> le (S n) (S m).

Notation "m <= n" := (le m n).
Notation "n >= d" := (d <= n).

Lemma le_refl : forall n, n <= n.
Proof.
induction n; econstructor; eauto.
Qed.

Notation "x < y" := (S x <= y).
Notation "n > d" := (d < n).

Lemma lt_O_false : forall {n}, not (n < 0).
Proof.
intros ?. inversion 1.
Qed. 

Lemma lt_S_false : forall {n}, not (n < n).
Proof.
induction n; inversion 1; subst; eauto.
Qed. 

Lemma le_S_inv n m : S n <= S m -> n <= m.
Proof.
inversion 1; eauto.
Qed.

Lemma le_trans {n m p} : n <= m -> m <= p -> n <= p.
Proof.
revert n m; induction p; intros; destruct n; destruct m; 
try apply le_refl; eauto.
- inversion H0.
- econstructor.
- inversion H.
- eapply le_S_inv in H, H0. econstructor. eapply IHp; eauto.
Qed. 

Lemma le_lt_trans {n m p} : n < m -> m <= p -> n < p.
Proof.
eapply le_trans.
Qed.

Lemma lt_le_trans {n m p} : n <= m -> m < p -> n < p.
Proof.
intros; eapply le_trans; eauto. by econstructor.
Qed.

Notation "A ∨ B" := (sum@{SProp SProp SProp;_ _} A B) (at level 50).

Lemma le_split n m : n <= m -> (n < m) ∨ (n ~ m).
Proof.
revert m; induction n; destruct m.
- intros _. by right.
- intros _; left. repeat constructor.
- intro H. inversion H.
- intros Hm. eapply le_S_inv in Hm. destruct (IHn _ Hm).
+ by left; repeat econstructor.
+ right. by eapply ap.
Qed. 

Lemma le_S_split n m : n <= S m -> (n <= m) ∨ (n ~ S m).
Proof.
intro Hm. eapply le_split in Hm.
destruct Hm.
- left. by eapply le_S_inv in l.
- by right.
Qed. 

Lemma le_S_n : forall n, n <= S n.
Proof.
induction n; econstructor; eauto.
Qed.

Lemma lt_S n : n < S n.
Proof.
eapply le_refl.
Qed.

Lemma le_le n k : n <= n + k.
Proof.
  revert k; induction n; simpl; intros; try econstructor; eauto.
Qed.

Lemma lt_lt n k : 0 < k -> n < n + k.
Proof.
  revert k; induction n; simpl; intros; eauto. econstructor; eauto.
Qed.

Lemma lt_irreflexive n : n < n -> SFalse.
Proof.
induction n; intro H. 
- inversion H.
- by apply le_S_inv in H.
Qed.

Lemma le_minus n p : n - p <= n.
Proof.
revert p; induction n; destruct p; try eapply le_refl.
eapply le_trans. 
- eapply IHn.
- eapply le_S_n.
Qed.

Lemma minus_zero p : p - 0 ~ p.
Proof. 
induction p; try reflexivity.
Qed. 

Lemma le_to_minus n m p : n <= m -> n <= p -> p - m <= p - n.
Proof.
revert m p; induction n.
- intros; eapply le_trans; try apply le_minus.
   rewrite minus_zero. eapply le_refl.
- intros. destruct p, m; simpl; try apply le_refl.
  * inversion H.
  * eapply le_S_inv in H, H0. cbn; by eapply IHn.
Qed. 

Lemma le_to_minus' n q p : p <= q -> p - n <= q - n.
Proof.
revert q p; induction n.
- intros. now repeat rewrite minus_zero.
- intros. destruct p,q ; simpl; try apply le_refl.
  * econstructor.
  * inversion H.
  * eapply le_S_inv in H. cbn; by eapply IHn.
Qed. 

Lemma lt_to_minus n m p : n < m -> n < p -> p - m < p - n.
Proof.
revert m p; induction n.
- intros; destruct m.
+ inversion H.
+ destruct p; [inversion H0|].
cbn. eapply lt_le_trans. eapply le_minus. eapply lt_S. 
- intros. destruct p; [inversion H0|].
destruct m; [inversion H|].
eapply le_S_inv in H, H0. cbn; by eapply IHn.
Qed. 

Lemma lt_to_minus' n q p : n <= p -> p < q -> p - n < q - n.
Proof.
revert q p; induction n.
- intros. now repeat rewrite minus_zero.
- destruct q; intros p H H'. 
 + inversion H'.
 + simpl. destruct p.
   * inversion H.
   * simpl. eapply le_S_inv in H, H'. now eapply IHn.
Qed.

Lemma minus_less n m: n - m <= n.
revert m; induction n; destruct m; cbn; try econstructor; try apply le_refl.
eapply le_trans; eauto. eapply le_S_n.
Qed. 

Lemma minus_S n m: m < n -> S (n - S m) ~ (n - m).
Proof.
revert m; induction n; cbn; intros. 
- inversion H.
- destruct m.
+ now rewrite minus_zero.
+ eapply IHn. by eapply le_S_inv in H.
Qed. 

Lemma minus_refl n: n - n ~ 0.
Proof. 
induction n; try reflexivity; eauto.
Qed. 

Lemma plus_zero p : (p + 0)%nat ~ p.
Proof. 
induction p; try reflexivity. simpl. by eapply ap. 
Qed. 

Lemma plus_one n : (n + 1)%nat ~ S n%nat.
Proof.
 induction n; simpl; try reflexivity. by apply ap.
Qed.   

Lemma plus_commS n m : (n + S m)%nat ~ S (n + m)%nat.
Proof.
  revert m; induction n; destruct m; simpl; intros; try reflexivity.
  - apply ap. rewrite plus_one. now rewrite plus_zero.
  - eapply ap; eauto.
Qed. 

Lemma plus_comm n m : (n + m)%nat ~ (m + n)%nat.
Proof. 
  revert m; induction n; destruct m; simpl; intros.
  - reflexivity.
  - eapply ap. now rewrite plus_zero.
  - eapply ap. now rewrite plus_zero.
  - eapply ap. rewrite IHn. now rewrite plus_commS.
Qed.

Lemma minus_plus_gen n k l : (n + (k + l)) - l ~ (n + k)%nat.
Proof.
  revert n k; induction l; destruct k, n; intros; simpl; try reflexivity; try apply ap. 
  - eapply plus_zero.
  - now rewrite plus_zero.
  - eapply minus_refl.
  - rewrite (IHl _ 1). rewrite plus_one. now rewrite plus_zero.
  - rewrite (IHl _ 1). now rewrite plus_one.
  - rewrite (plus_commS k l). rewrite (IHl _ (S (S k))).
    apply plus_commS.
Qed. 

Lemma minus_le k l : k <= l -> (k - l)%nat ~ 0.
Proof.
  revert l; induction k; destruct l; simpl; intros; try reflexivity.
  - inversion H.
  - eapply le_S_inv in H; eauto.
Qed.

Lemma minus_plus k l : k <= l -> (k + (l - k))%nat ~ l.
Proof.
  revert l; induction k; destruct l; simpl; intros H; try reflexivity.
  - inversion H.
  - eapply le_S_inv in H. eapply ap; eauto.
Qed.      

Lemma minus_refl_k n k : (n + k - k) ~ n %nat.
Proof.
  revert n; induction k; destruct n; simpl; intros; try reflexivity.
  - eapply ap, plus_zero.
  - eapply minus_refl.
  - rewrite plus_commS. rewrite <- minus_S. apply ap. now cbn.
    rewrite plus_comm. econstructor. eapply le_le.
Qed.    

Lemma minus_plus_minus n k l : k <= l -> (n + k - l) ~ (n - (l - k))%nat.
Proof.
  intro H. 
  set (l - k). rewrite <- (minus_plus _ _ H). unfold n0.
  generalize (l - k). clear H l n0. intro l.
  revert k n; induction l; simpl; intros.
  - rewrite plus_zero. rewrite minus_refl_k. now rewrite minus_zero.
  - repeat rewrite plus_commS.
    destruct n; simpl; eauto.
    eapply minus_le. eapply le_trans; try apply le_S_n. econstructor. eapply le_le.
Qed.

Lemma minus_plus_le n k m : n + k <= m -> n <= m - k.
Proof.
  intro H. assert (n + k - k ~ n). 
  { rewrite (minus_plus_gen _ 0). now rewrite plus_zero. }
  rewrite <- H0. by eapply le_to_minus'.
Qed. 

Lemma plus_le k n m : n <= m -> n + k <= m + k.
Proof.
  induction k; simpl; intros.
  - now repeat rewrite plus_zero.
  - repeat rewrite plus_commS. constructor. now eapply IHk.
Qed.

Lemma minus_plus_le' n k m : k <= m -> n <= m - k -> n + k <= m.
Proof.
  intros Hkn H. eapply (plus_le k) in H.
  rewrite (plus_comm (m-k)) in H.
  eapply le_trans; eauto.
  rewrite (minus_plus _ _ Hkn).
  apply le_refl.
Qed. 

Lemma minus_gt n m: m <= n -> m - n ~ 0.
revert n; induction m; destruct n; cbn; try econstructor; try apply le_refl.
- inversion 1.
- intros H; eapply le_S_inv in H. by eapply IHm.
Qed. 

Lemma dec_le n m : sum (n < m) (m <= n).
Proof.
revert m; induction n ; destruct m.
- right; eapply le_refl.
- left; repeat econstructor.
- right; econstructor.
- destruct (IHn m).
+ left. by econstructor.
+ right. by econstructor.
Defined. 

Lemma exc_le n m : n < m -> m <= n -> SFalse.
Proof.
revert m; induction n ; destruct m.
- intro H. destruct (lt_O_false H).
- intros _ H. destruct (lt_O_false H). 
- intro H. destruct (lt_O_false H).
- intros H H'. eapply le_S_inv in H, H'. eapply IHn; eauto.
Qed. 

Definition le_lt_dec n m : sum (n <= m) (m < n).
Proof.
induction n as [|n IHn] in m |- * using nat_rect .
- left; econstructor.
- destruct m as [|m].
+ right; repeat econstructor.
+ destruct (IHn m); [left|right]; now constructor.
Defined.

Lemma le_excl n m : n < m -> m <= n -> SFalse.
Proof.
induction n as [|n IHn] in m |- * using nat_sind .
- intros H H'. destruct m. destruct (lt_O_false H). destruct (lt_O_false H').
- destruct m as [|m]; intros H H'. 
+ inversion H.
+ eapply le_S_inv in H. apply (IHn _ H).
by eapply le_S_inv in H'.
Qed.

Infix "<=?" := Nat.leb (at level 70) : nat_scope.
Infix "<?" := Nat.ltb (at level 70) : nat_scope.
Infix "=?" := Nat.eqb (at level 70) : nat_scope.
Infix "?=" := Nat.compare (at level 70) : nat_scope.

Lemma leb_le n m : (n <=? m) ~ true -> n <= m.
Proof.
  revert m.
  induction n as [|n IHn]; intro m; destruct m; simpl.
  - intro; constructor.
  - intro; constructor.
  - now intro.
  - intro. constructor; eauto.
Qed.

Lemma ltb_lt n m : (n <? m) ~ true -> n < m.
Proof.
  eapply leb_le.
Qed. 

Lemma ltb_ge n m : (n <? m) ~ false -> m <= n.
Proof.
  revert m.
  induction n as [|n IHn]; intro m; destruct m; cbn.
  - intro; constructor.
  - now intro.
  - intro; econstructor.  
  - intro. constructor; eauto.
Qed.


Lemma leb_correct m n : m <= n -> (m <=? n) ~ true.
Proof.
  revert m.
  induction n as [|n IHn]; intro m; destruct m; simpl; try reflexivity.
  - inversion 1.
  - inversion 1. now eapply IHn.
Qed.  

Definition leb_correct_conv m n : m < n ->  (n <=? m) ~ false.
  revert m.
  induction n as [|n IHn]; intro m; destruct m; simpl; try reflexivity; inversion 1.
  now eapply IHn.
Qed.

Lemma le_dec n m: sum (n <= m) (not (n <= m)).
  destruct (le_lt_dec n m).
  - left ; eauto.
  - right. intro. eapply exc_le; eauto.
Defined.

Lemma not_le_lt n m : not (m <= n) -> n < m.
Proof.
intro Hnm.  
case (le_lt_dec m n); eauto.
intro H; destruct (Hnm H).
Qed. 

Definition le_compare_dec n m : m <= n -> sum (m ~ n) (m < n).
Proof.
induction n as [|n IHn] in m |- * using nat_rect .
- left. now inversion H.
- destruct m as [|m].
+ right; repeat econstructor.
+ intro H. eapply le_S_inv in H. destruct (IHn m H); [left|right]; try now constructor.
  now apply ap.
Defined.


Lemma max_l m n : n <= Nat.max n m. 
Proof.
  revert m; induction n; destruct m; simpl; econstructor.
  - eapply le_refl.
  - eapply IHn.
Qed.    

Lemma max_r m n : m <= Nat.max n m. 
Proof.
  revert m; induction n; destruct m; simpl; econstructor.
  - eapply le_refl.
  - eapply IHn.
Qed.    

Lemma max_lr m n p : p >= n -> p >= m -> p >= Nat.max n m. 
Proof.
  revert m p; induction n; destruct m; simpl; intros; try econstructor; eauto.
  destruct p; [inversion H|]. econstructor. 
  eapply le_S_inv in H, H0. now eapply IHn.
Qed.    

Lemma minus_S_le p n : p >= n -> S (p - n) ~ (S p - n).
induction p as [|p IHp] in n |- *.
- destruct n; inversion 1. reflexivity.
- destruct n; simpl. reflexivity.
  intros H. eapply le_S_inv in H. now eapply IHp. 
Qed. 

Lemma compare_eq_iff n m : (n ?= m) ~ Datatypes.Eq <--> n ~ m.
Proof.
  revert m; induction n as [|n IHn]; intro m; destruct m; simpl; split ; 
  try reflexivity; try solve [inversion 1].
  - intro H. now apply ap, IHn.
  - intro H. apply IHn. now inversion H. 
Qed.

Lemma nat_compare_gt n m : m < n -> (n ?= m) ~ Gt.
Proof.
  revert m; induction n; cbn; intros.
  - inversion H. 
  - destruct m; try reflexivity.
    eapply IHn. inversion H; eauto.
Qed.

Definition gt_eq_gt_dec : forall n m : nat, sum (m > n) (sum (m ~ n) (n > m)).
Proof. 
 intros n m.
 destruct (dec_le n m).
 - now left.
 - destruct (le_compare_dec n m l).
  + now right; left.
  + now right; right.
Defined.      