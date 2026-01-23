Set Universe Polymorphism.

From SystemF Require Import sum Observational.

(** * Strong normalization of system F

  We now move to the strong normalization proof. We follow the
  proof of Girard-Taylor-Lafont's "Proofs and Types"
  ----
  The set of normalizing terms is inductively defined *)

Inductive Acc A (R:A -> A -> SProp) (x: A) : SProp := 
    acc_in : (forall y:A, R y x -> Acc A R y) -> Acc A R x.

Definition acc_inv A R x (p : Acc A R x) :  forall y:A, R y x -> Acc A R y.
  induction p. eapply a. 
Qed.

(** A relation is well-founded if every element is accessible *)

Definition well_founded A R := forall a:A, Acc A R a.

Arguments Acc {A}.
Arguments well_founded {A}.

Symbol acc_el : forall (A : Type) (R : A -> A -> SProp) 
  (a : A)
  (P : forall a:A, Type)
  (p : forall (x : A), (forall (b : A) (r : R b x), P b) -> P x)
  (q: Acc R a), P a.

#[local] 
Rewrite Rule Acc_el_def :=
  | @{u u'} |-
  acc_el@{u u'} ?A ?R ?a ?P ?p ?q =>
  ?p ?a (fun b r => acc_el@{u u'} ?A ?R b ?P ?p (acc_inv ?A ?R ?a ?q b r)).

Axiom Acc_el_comp : forall A R a P p q, 
  acc_el A R a P p q ~ p a (fun b r => acc_el A R b P p (acc_inv A R a q b r)).

Definition FixWf {A : Type} {R} (wf : well_founded R) (P : A -> Type) :
  (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x :=
  fun f a => acc_el A R a P f (wf a).
