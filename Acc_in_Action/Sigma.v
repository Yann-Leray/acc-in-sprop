Set Universe Polymorphism. 

#[global]
Set Polymorphic Inductive Cumulativity. 

Inductive sigma@{s s' s'';u v} (A:Type@{s;u}) (P:A -> Type@{s';v}) : Type@{s'';max(u,v)}
  :=  exist : forall x:A, P x -> sigma A P.

Arguments exist {_ _}.

Definition proj1@{s s';u v} {A:Type@{s;u}} {P:A -> Type@{s';v}}
  (p : sigma@{s s' s;_ _} A P) : A := match p with exist a _ => a end.

Definition proj2@{s;u v} {A:Type@{s;u}} {P:A -> Type@{s;v}} (p : sigma@{_ _ s;_ _} A P) : P (proj1 p) := match p with exist _ b => b end.

Definition π1@{s s';u v} {A:Type@{s;u}} {P:A -> Type@{s';v}} (p : sigma@{_ _ Type;_ _} A P) : A :=
  match p return A with exist a _ => a end.

Definition π2@{s s';u v} {A:Type@{s;u}} {P:A -> Type@{s';v}} (p : sigma@{_ _ Type;_ _} A P) : P (π1 p) := match p with exist _ b => b end.

#[warnings="-notation-overridden"]
Notation "'Σ' x .. y , B" := (sigma _ (fun x => .. (sigma _ (fun y => B)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' B ']'")
  : type_scope.

#[warnings="-notation-overridden"]
Notation "( x ; .. ; y ; z )" := (exist x .. (exist y z) ..) : core_scope.

(* Rule order is important to give printing priority to fully typed exists *)
Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'∃' x .. y , B" := (sigma@{_ SProp SProp ; _ Set} _ (fun x => .. (sigma@{_ SProp SProp ; _ Set} _ (fun y => B)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∃'  '/  ' x  ..  y ,  '/  ' B ']'")
  : type_scope.

Notation "P 'and' Q" := (∃ _ : P, Q) (at level 80).


#[projections(primitive)]
Record prod@{s;u v} (A:Type@{s;u}) (B:Type@{s;v}) : Type@{s;max(u,v)} := 
  { fst : A ; snd : B }.

Arguments fst {A B} _.
Arguments snd {A B} _.

Notation "P /\ Q" := (prod P Q).
