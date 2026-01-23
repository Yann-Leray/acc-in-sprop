Set Universe Polymorphism.

From Stdlib Require Import Arith.
Require Import Lia.

Coercion is_true : bool >-> Sortclass.

#[global]
Instance iff_flip_impl_subrelation : RelationClasses.subrelation iff (CRelationClasses.flip Basics.impl) | 2.
Proof. firstorder. Defined.

#[global]
Instance iff_impl_subrelation : RelationClasses.subrelation iff Basics.impl | 2.
Proof. firstorder. Defined.

Lemma is_true_true : true. Proof. reflexivity. Defined.
Lemma not_false_is_true : ~ false. Proof. intro e; inversion e. Defined.

#[global]
Hint Resolve is_true_true not_false_is_true : core.

Definition reflectEq {a b : nat} : a = b -> a =? b.
 revert b; induction a; destruct b; cbn; eauto.
all: inversion 1.   
Defined.

Definition coReflectEq {a b : nat} : a =? b -> a = b. 
revert b; induction a; destruct b; cbn; eauto.
all: inversion 1.   
Defined.

Definition makeComputeEq (a b : nat) : a = b -> a = b := fun e => coReflectEq (reflectEq e).

Definition reflectLeq (a b : nat) : a <= b -> a <=? b.
revert b; induction a; destruct b; cbn; eauto.
- intro e. inversion e.
- intro e; eapply IHa. abstract lia.
Defined.

Lemma le_cong a b: a <= b -> S a <= S b.
Proof.
 induction 1; constructor; trivial.
Defined.

Definition coReflectLeq (a b : nat) : a <=? b -> a <= b.
revert b; induction a; destruct b; cbn; eauto.
- intros _. induction b; eauto.
- inversion 1.  
- intro e; eapply IHa in e. now apply le_cong.
Defined.

Definition makeComputeLeq (a b : nat) : a <= b -> a <= b := fun e => coReflectLeq _ _ (reflectLeq _ _ e).

Definition reflectLt (a b : nat) : a < b -> a <? b.
revert b; induction a; destruct b; cbn; eauto.
- intro e. inversion e.
- intro e. inversion e.
- intro e; eapply IHa. abstract lia.
Defined.

Definition coReflectLt (a b : nat) : a <? b -> a < b.
revert b; induction a; destruct b; cbn; eauto.
- inversion 1.  
- intros _. induction b; eauto.
- inversion 1.  
- intro e; eapply IHa in e. now apply le_cong.
Defined.

Definition makeComputeLt (a b : nat) : a < b -> a < b := fun e => coReflectLt _ _ (reflectLt _ _ e).

Ltac lia_comp := first [eapply makeComputeEq | eapply makeComputeLeq | eapply makeComputeLt]; abstract lia.

Definition proj1 {A B} : A /\ B -> A.
Proof.
  destruct 1; trivial.
Defined.

Theorem proj2 {A B} : A /\ B -> B.
Proof.
  destruct 1; trivial.
Defined.

Definition leb_correct_conv : forall m n : nat, m <? n -> (n <=? m) = false.
induction m; destruct n; eauto.
Defined.

Definition compare_eq_iff : forall n m : nat, (n ?= m) = Eq <-> n = m.
induction n; destruct m; cbn; split; try reflexivity.
all: try solve [inversion 1]. 
- intros ?. eapply f_equal. specialize (IHn m).
  eapply iff_impl_subrelation in IHn. eapply IHn; eassumption.
- intros ?. 
  eapply iff_flip_impl_subrelation in IHn. eapply IHn. lia_comp.
Defined.  

Definition nat_compare_gt : forall n m : nat, n > m <-> (n ?= m) = Gt.
induction n; destruct m; cbn; split; eauto.
all: try solve [inversion 1].
- intros ?. lia_comp.
- intros ?. eapply iff_impl_subrelation in IHn. eapply IHn. lia_comp.
- intros ?. eapply iff_flip_impl_subrelation in IHn. eapply IHn in H. lia_comp.
Defined.  

Definition nat_compare_lt : forall n m : nat, n < m <-> (n ?= m) = Lt.
induction n; destruct m; cbn; split; eauto.
all: try solve [inversion 1].
- intros ?. lia_comp.
- intros ?. eapply iff_impl_subrelation in IHn. eapply IHn. lia_comp.
- intros ?. eapply iff_flip_impl_subrelation in IHn. eapply IHn in H. lia_comp.
Defined.  

Definition compare_spec: forall x y : nat, CompareSpec (x = y) (x < y) (y < x) (x ?= y).
induction x; destruct y.
- constructor 1. reflexivity.
- constructor 2. lia_comp.
- constructor 3. lia_comp.
- cbn. destruct (IHx y).       
  + constructor 1. lia_comp. 
  + constructor 2. lia_comp.
  + constructor 3. lia_comp.
Defined.  

Definition le_dec : forall (n m : nat), {n <= m} + {~ n <= m}.
Proof.
  induction n; destruct m.
  - constructor 1. reflexivity.
  - constructor 1. lia_comp.
  - constructor 2. intro e. inversion e.
  - destruct (IHn m).       
  + constructor 1. lia_comp. 
  + constructor 2. intro e; apply n0. lia_comp.
Defined. 

Definition lt_dec : forall n m : nat, {n < m} + {~ n < m}.
Proof.
  intros n m; destruct (le_dec (S n) m); eauto. 
Defined. 
