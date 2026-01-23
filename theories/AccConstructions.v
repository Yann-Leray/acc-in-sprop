
(* This file shows that the simplified elimination principle for Acc in Typing.v is enough 
  to derive the usual elimination principle.  *)


Axiom Acc : forall (A : Type) (R : A -> A -> SProp) (a : A), SProp.

Axiom acc_in : forall A R a (f : forall y, R a y -> Acc A R y), Acc A R a.

(* Simplified elimination principle targeting SProp, in which p does not have access to f, only to ϵf *)
Axiom Acc_simp_el_sprop : forall A R (P : A -> SProp) (p : forall (a : A) (ϵf : forall y : A, R a y -> P y), P a) (y : A) (r : Acc A R y), P y.


(* For the constructions of Acc_el_sprop and Acc_dep_el_sprop, we have be able 
  to take the sigma type of A : SProp and B : A -> SProp, but this is actually 
  derivable thanks to impredicativity *)
Definition Σ_ΩΩ (A : SProp) (B : A -> SProp) : SProp := forall P, (forall a:A, B a -> P) -> P.

Definition fst_ΩΩ {A B}: Σ_ΩΩ A B -> A := fun f => f A (fun a b => a).

Definition snd_ΩΩ {A B}: forall (x : Σ_ΩΩ A B), B (fst_ΩΩ x) := fun f => f (B (fst_ΩΩ f)) (fun a b => b).

Definition mkΣ_ΩΩ {A B} (a : A) (b : B a) : Σ_ΩΩ A B := fun P f => f a b.


(* Usual non-dependent elimination principle, in which p has access to f *)
Lemma Acc_el_sprop A R (P : A -> SProp) (p : forall (a : A) (f:forall y, R a y -> Acc A R y) (ϵf:forall y, R a y -> P y), P a) (y : A) (r : Acc A R y) : P y.
Proof.
  intros.
  eapply (@snd_ΩΩ (Acc A R y) (fun _ => P y)).
  eapply (Acc_simp_el_sprop _ _ (fun a => Σ_ΩΩ (Acc A R a) (fun _ => P a))).
  2:exact r.
  intros. eapply mkΣ_ΩΩ.
  - eapply acc_in. intros. eapply ϵf in H. eapply (fst_ΩΩ H).
  - eapply p.
    + intros z r'. eapply ϵf in r'. eapply (fst_ΩΩ r').
    + intros z r'. eapply ϵf in r'. eapply (snd_ΩΩ r'). 
Defined.

(* Using the above, we can derive acc_inv, showing that the addition of this constant in the
  definition of our type system is actually not needed. *)
Lemma acc_inv A R a : Acc A R a -> forall b, R a b -> Acc A R b.
Proof.
  intros.
  eapply (Acc_el_sprop _ _ (fun a => R a b -> Acc A R b)). 3:exact H0. 2:exact H.
  intros. eapply f. exact H1.
Defined.


(* However, having acc_inv as a primitive allows us to avoid writing the definition of acc_inv 
  in terms of Acc_simp_el_sprop, which is quite verbose. Indeed, the implementation of accinv would require 
  us to write the term printed by the following command in the syntax specified in AST.v, and then 
  retype it using the rules of Typing.v. by the above proofs, this would be theoretically possible
  but practically infeasible. *)
Eval cbv in acc_inv.


(* Using Acc_el_sprop and relying on proof irrelevance, we can also derive the full dependent 
  elimination principle for SProp. In practice, this principle is not that useful, because in 
  most cases the predicate does not depend in the proof of accessibility. *)
Lemma Acc_dep_el_sprop A R (P : forall x:A, Acc A R x -> SProp) 
  (p : forall (a : A) (f : forall y, R a y -> Acc A R y) 
        (ϵf : forall y (r:R a y), P y (f y r)), P a (acc_in A R a f)) 
  (y : A) (r : Acc A R y) : P y r.
Proof.
    intros. 
    unshelve eapply (@snd_ΩΩ (Acc A R y) (fun r => P y r) _).
    unshelve eapply (Acc_el_sprop _ R (fun y => Σ_ΩΩ (Acc A R y) (fun r => P y r)) _ _ r). clear y r.
    simpl. intros.  unshelve eapply mkΣ_ΩΩ.
    eapply acc_in. eapply f. eapply p. intros.  
    pose (h := snd_ΩΩ (ϵf _ r)). simpl in h.
    eapply h.
Defined.


(* Simplified elimination principle targeting Type, in which p does not have access to f, only to ϵf *)
Axiom Acc_simp_el_type : forall A R (P : A -> Type) (p : forall (a : A) (ϵf : forall y : A, R a y -> P y), P a) (y : A) (r : Acc A R y), P y.

(* For this construction, we have be able to take the sigma type of A : SProp and B : A -> Type.
  This time, we cannot use impredicativity, so we assume we have it in the theory *)
Inductive Σ_ΩU (A : SProp) (B : A -> Type) : Type := 
    | mkΣ_ΩU : forall x : A, B x -> Σ_ΩU A B. 

Definition fst_ΩU {A} {B} : Σ_ΩU A B -> A := fun x => match x with | mkΣ_ΩU _ _ x _ => x end.

Definition snd_ΩU {A} {B} : forall x : Σ_ΩU A B, B (fst_ΩU x) := fun x => match x with | mkΣ_ΩU _ _ _ x => x end.


(* Usual non-dependent elimination principle for Type, in which p has access to f *)
Lemma Acc_el_type A R (P : A -> Type) (p : forall (a : A) (f:forall y, R a y -> Acc A R y) (ϵf:forall y, R a y -> P y), P a) (y : A) (r : Acc A R y) : P y.
Proof.
  intros.
  eapply (@snd_ΩU (Acc A R y) (fun r => P y)).
  eapply (Acc_simp_el_type _ _ (fun a => Σ_ΩU (Acc A R a) (fun _ => P a))).
  2:exact r.
  intros. eapply mkΣ_ΩU.
  - eapply acc_in. intros. eapply ϵf in H. eapply (fst_ΩU H).
  - eapply p.
    + intros z r'. eapply ϵf in r'. eapply (fst_ΩU r').
    + intros z r'. eapply ϵf in r'. eapply (snd_ΩU r'). 
Defined.

(* Full dependent elimination principle for Type *)
Lemma Acc_dep_el_type A R (P : forall x:A, Acc A R x -> Type) 
  (p : forall (a : A) (f : forall y, R a y -> Acc A R y) 
        (ϵf : forall y (r:R a y), P y (f y r)), P a (acc_in A R a f)) 
  (y : A) (r : Acc A R y) : P y r.
Proof.
    intros. 
    unshelve eapply (@snd_ΩU (Acc A R y) (fun r => P y r) _).
    unshelve eapply (Acc_el_type _ R (fun y => Σ_ΩU (Acc A R y) (fun r => P y r)) _ _ r). clear y r.
    simpl. intros.  unshelve eapply mkΣ_ΩU.
    eapply acc_in. eapply f. eapply p. intros.  
    pose (h := snd_ΩU (ϵf _ r)). simpl in h.
    eapply h.
Defined.
