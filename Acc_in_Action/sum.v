Set Universe Polymorphism. 

#[global]
Set Polymorphic Inductive Cumulativity. 

Inductive sum@{s s' s'';u v} (A : Type@{s;u}) (B : Type@{s';v}) : Type@{s'';max(u,v)} :=
  | left : A -> sum A B
  | right : B -> sum A B.

Register sum as core.sum.type.
Register left as core.sum.inl.
Register right as core.sum.inr.

Arguments left {A B} _, [A] B _.
Arguments right {A B} _ , A [B] _.

Hint Resolve left right : core.
Notation "A + B" := (sum A B).
Notation "{ A } + { B }" := (sum@{SProp SProp Type;_ _} A B) (only parsing).
Notation "A \/ B" := (sum@{Prop Prop Prop;_ _} A B).
