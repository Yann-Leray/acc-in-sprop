Set Universe Polymorphism.

From Stdlib Require Import Arith.
Require Import ComputeEq.
From SystemF Require Import Sigma.

Lemma gcd_obligation_1
     : forall n n0 : nat,
  S n0 > S n -> S n + (S n0 - S n) < S n + S n0.
Proof.
  intros. 
  lia_comp.
Defined.

Lemma gcd_obligation_2 : forall n n0 : nat,
  S n > S n0 -> S n - S n0 + S n0 < S n + S n0.
  intros; lia_comp.
Defined.  

Lemma wf_lt : well_founded 
  (fun y x : Σ _ : nat, nat => proj1 x + proj2 x > proj1 y + proj2 y).
Proof.
  intros [a b]; cbn; revert b.
  induction a; intro b.
  - induction b; econstructor.
    + intros ? H. inversion H.
    + intros [a' b'] H; cbn in *. econstructor.
      intros. eapply IHb; cbn in *.
      lia_comp.
  - econstructor; intros [a' b'] H; cbn in *.
    eapply (IHa (S b)); cbn. lia_comp.
Defined.

Definition gcd_clause_3 : forall n n0 : nat,
  {S n0 > S n} + {S n = S n0} + {S n > S n0} -> 
  (forall x x0 : nat, x + x0 < S n + S n0 -> nat) -> nat.
  intros n n0 refine gcd.
  destruct refine.
  - destruct s.
   + refine (gcd (S n) (S n0 - S n) _).
      now apply gcd_obligation_1.
   + exact (S n).
  - refine (gcd (S n - S n0) (S n0) _).
      now apply gcd_obligation_2.
Defined.

Definition gcd_functional  : forall x y : nat,
  (forall x0 x1 : nat, x0 + x1 < x + y -> nat) -> nat.
  intros x y gcd.
  destruct x as [| n].
  - exact y.
  - destruct y as [| n0].
    + exact (S n).
    + exact (gcd_clause_3 n n0 (gt_eq_gt_dec (S n) (S n0)) gcd).
Defined.

Definition FixWf {A : Type} {R} (wf : well_founded R) (P : A -> Type) :
  (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x.
  intros f a. 
  refine (@Acc_rect A R P _ a (wf a)).
  intros. now eapply f.
Defined.    

Definition gcd (a b : nat) : nat :=
  FixWf wf_lt _
  (fun x H => gcd_functional (proj1 x) (proj2 x) (fun a0 b0 : nat => H (a0; b0)))
  (a ; b).

From Ltac2 Require Import Ltac2.

From Ltac2 Require Import Message.

From Ltac2 Require Import Ref.

Fixpoint power : nat -> nat -> nat := 
  fun pow n => match n with 
    |  0  => 1 
    | S n => (pow * power pow n)%nat
  end.
  
Notation "x ^ n" := (power x n).

Goal (gcd (2 ^ 5) 2 <? 5) = true.
Proof.
  print (of_string "Prop scenario: gcd (2 ^ 5) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

Goal (gcd (2 ^ 6) 2 <? 5) = true.
Proof.
  print (of_string "Prop scenario: gcd (2 ^ 6) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

Goal (gcd (2 ^ 7) 2 <? 5) = true.
Proof.
  print (of_string "Prop scenario: gcd (2 ^ 7) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

Goal (gcd (2 ^ 8) 2 <? 5) = true.
Proof.
  print (of_string "Prop scenario: gcd (2 ^ 8) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

Goal (gcd (2 ^ 9) 2 <? 5) = true.
Proof.
  print (of_string "Prop scenario: gcd (2 ^ 9) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

Goal (gcd (2 ^ 10) 2 <? 5) = true.
Proof.
  print (of_string "Prop scenario: gcd (2 ^ 10) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort.

Goal (gcd (2 ^ 11) 2 <? 5) = true.
Proof.
  print (of_string "Prop scenario: gcd (2 ^ 11) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort.
