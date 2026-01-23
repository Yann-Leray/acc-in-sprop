Set Universe Polymorphism.

From SystemF Require Import sum Observational Acc Logic Arith List Substitution Confluence Sigma.

Lemma gcd_obligation_1
     : forall n n0 : nat,
  S n0 > S n -> S n + (S n0 - S n) < S n + S n0.
Proof.
  intros n n0 e.
  rewrite minus_plus. 
  - rewrite plus_comm. eapply lt_lt. repeat econstructor.
  - eapply lt_le_trans; eauto. eapply le_S_n.
Qed.

Lemma gcd_obligation_2 : forall n n0 : nat,
  S n > S n0 -> S n - S n0 + S n0 < S n + S n0.
  intros n n0 e.
  rewrite plus_comm. rewrite (plus_comm (S n)). 
  now eapply gcd_obligation_1.
Qed.  

Lemma wf_lt : well_founded (fun y x : Σ _ : nat, nat => proj1 x + proj2 x > proj1 y + proj2 y).
Proof.
  intros [a b]; cbn; revert b.
  induction a; intro b.
  - induction b; econstructor.
    + intros ? H. inversion H.
    + intros [a' b'] H; cbn in *. econstructor.
      intros. eapply IHb; cbn in *.
      eapply le_lt_trans; eauto. now eapply le_S_inv in H.
  - econstructor; intros [a' b'] H; cbn in *.
    eapply (IHa (S b)); cbn. now rewrite plus_commS.
Qed.

Definition gcd_clause_3 : forall n n0 : nat,
  sum (S n0 > S n) (sum (S n0 ~ S n) (S n > S n0)) -> 
  (forall x x0 : nat, x + x0 < S n + S n0 -> nat) -> nat.
  intros n n0 refine gcd.
  destruct refine.
  - refine (gcd (S n) (S n0 - S n) _).
      now apply gcd_obligation_1.
  - destruct s.
    + exact (S n).
    + refine (gcd (S n - S n0) (S n0) _).
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

Ltac2 Notation "auto_Acc_unfold" := let n := ref 0 in 
    unfold gcd, FixWf;
    repeat (incr n; rewrite Acc_el_comp; lazy);
    print (concat (of_string "number of reduction steps: ")
                  (of_int (get n))).

Goal (gcd (2 ^ 5) 2 <? 5) ~ true.
Proof.  
  print (of_string "prop scenario: gcd (2 ^ 5) 2 <? 5 ~ true ").
  Time auto_Acc_unfold; reflexivity. 
Abort. 

Goal (gcd (2 ^ 6) 2 <? 5) ~ true.
Proof.
  print (of_string "prop scenario: gcd (2 ^ 6) 2 <? 5 ~ true ").
  Time auto_Acc_unfold; reflexivity. 
Abort. 

Goal (gcd (2 ^ 7) 2 <? 5) ~ true.
Proof.
  print (of_string "prop scenario: gcd (2 ^ 7) 2 <? 5 ~ true ").
  Time auto_Acc_unfold; reflexivity. 
Abort. 

Goal (gcd (2 ^ 8) 2 <? 5) ~ true.
Proof.
  print (of_string "prop scenario: gcd (2 ^ 8) 2 <? 5 ~ true ").
  print (of_string "** Uncomment in the file if you want to see the result **").
  (* Time auto_Acc_unfold; reflexivity.  *)
Abort. 

Goal (gcd (2 ^ 9) 2 <? 5) ~ true.
Proof.
  print (of_string "prop scenario: gcd (2 ^ 9) 2 <? 5 ~ true ").
  print (of_string "** Uncomment in the file if you want to see the result **").
  (*   Time auto_Acc_unfold; reflexivity. *)
Abort. 

Goal (gcd (2 ^ 10) 2 <? 5) ~ true.
Proof.
  print (of_string "prop scenario: gcd (2 ^ 10) 2 <? 5 ~ true ").
  print (of_string "** Uncomment in the file if you want to see the result **").
  (* Timeout 600 Time auto_Acc_unfold; reflexivity. *)
Abort.


#[rewrite_rules(Acc_el_def)]
Goal (gcd (2 ^ 5) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ 5) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

#[rewrite_rules(Acc_el_def)]
Goal (gcd (2 ^ 6) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ 6) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

#[rewrite_rules(Acc_el_def)]
Goal (gcd (2 ^ 7) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ 7) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

#[rewrite_rules(Acc_el_def)]
Goal (gcd (2 ^ 8) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ 8) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

#[rewrite_rules(Acc_el_def)]
Goal (gcd (2 ^ 9) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ 9) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort. 

#[rewrite_rules(Acc_el_def)]
Goal (gcd (2 ^ 10) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ 10) 2 <? 5 ~ true ").
  Time lazy; reflexivity. 
Abort.

#[rewrite_rules(Acc_el_def)]
Goal (gcd (2 ^ 11) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ 11) 2 <? 5 ~ true ").
  Time reflexivity. 
Abort.

#[rewrite_rules(Acc_el_def)]
Goal forall n, (gcd (2 ^ n) 2 <? 5) ~ true.
Proof.
  print (of_string "def scenario: gcd (2 ^ n) 2 <? 5 ~ true ").
  Fail Timeout 2 hnf; reflexivity. 
Abort.