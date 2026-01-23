From AccInSProp Require Import core unscoped.
From AccInSProp Require Import BasicAST.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Module Core.

Inductive term : Type :=
  | var : nat -> term
  | Sort : level -> term
  | assm : aref -> term
  | Pi : level -> level -> term -> term -> term
  | lam : level -> level -> term -> term -> term -> term
  | app : level -> level -> term -> term -> term -> term -> term
  | Nat : term
  | zero : term
  | succ : term -> term
  | rec : level -> term -> term -> term -> term -> term
  | acc : level -> term -> term -> term -> term
  | accin : level -> term -> term -> term -> term -> term
  | accinv : level -> term -> term -> term -> term -> term -> term -> term
  | accel :
      level -> level -> term -> term -> term -> term -> term -> term -> term
  | accelcomp :
      level -> level -> term -> term -> term -> term -> term -> term -> term
  | obseq : level -> term -> term -> term -> term
  | obsrefl : level -> term -> term -> term
  | J : level -> term -> term -> term -> term -> term -> term -> term
  | cast : level -> term -> term -> term -> term -> term
  | injpi1 : level -> level -> term -> term -> term -> term -> term -> term
  | injpi2 :
      level -> level -> term -> term -> term -> term -> term -> term -> term.

Lemma congr_Sort {s0 : level} {t0 : level} (H0 : s0 = t0) : Sort s0 = Sort t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Sort x) H0)).
Qed.

Lemma congr_assm {s0 : aref} {t0 : aref} (H0 : s0 = t0) : assm s0 = assm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => assm x) H0)).
Qed.

Lemma congr_Pi {s0 : level} {s1 : level} {s2 : term} {s3 : term} {t0 : level}
  {t1 : level} {t2 : term} {t3 : term} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) : Pi s0 s1 s2 s3 = Pi t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => Pi x s1 s2 s3) H0))
               (ap (fun x => Pi t0 x s2 s3) H1))
            (ap (fun x => Pi t0 t1 x s3) H2))
         (ap (fun x => Pi t0 t1 t2 x) H3)).
Qed.

Lemma congr_lam {s0 : level} {s1 : level} {s2 : term} {s3 : term} {s4 : term}
  {t0 : level} {t1 : level} {t2 : term} {t3 : term} {t4 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  : lam s0 s1 s2 s3 s4 = lam t0 t1 t2 t3 t4.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans eq_refl (ap (fun x => lam x s1 s2 s3 s4) H0))
                  (ap (fun x => lam t0 x s2 s3 s4) H1))
               (ap (fun x => lam t0 t1 x s3 s4) H2))
            (ap (fun x => lam t0 t1 t2 x s4) H3))
         (ap (fun x => lam t0 t1 t2 t3 x) H4)).
Qed.

Lemma congr_app {s0 : level} {s1 : level} {s2 : term} {s3 : term} {s4 : term}
  {s5 : term} {t0 : level} {t1 : level} {t2 : term} {t3 : term} {t4 : term}
  {t5 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3)
  (H4 : s4 = t4) (H5 : s5 = t5) :
  app s0 s1 s2 s3 s4 s5 = app t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl
                        (ap (fun x => app x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => app t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => app t0 t1 x s3 s4 s5) H2))
               (ap (fun x => app t0 t1 t2 x s4 s5) H3))
            (ap (fun x => app t0 t1 t2 t3 x s5) H4))
         (ap (fun x => app t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma congr_Nat : Nat = Nat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_zero : zero = zero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_succ {s0 : term} {t0 : term} (H0 : s0 = t0) : succ s0 = succ t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => succ x) H0)).
Qed.

Lemma congr_rec {s0 : level} {s1 : term} {s2 : term} {s3 : term} {s4 : term}
  {t0 : level} {t1 : term} {t2 : term} {t3 : term} {t4 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) :
  rec s0 s1 s2 s3 s4 = rec t0 t1 t2 t3 t4.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans eq_refl (ap (fun x => rec x s1 s2 s3 s4) H0))
                  (ap (fun x => rec t0 x s2 s3 s4) H1))
               (ap (fun x => rec t0 t1 x s3 s4) H2))
            (ap (fun x => rec t0 t1 t2 x s4) H3))
         (ap (fun x => rec t0 t1 t2 t3 x) H4)).
Qed.

Lemma congr_acc {s0 : level} {s1 : term} {s2 : term} {s3 : term} {t0 : level}
  {t1 : term} {t2 : term} {t3 : term} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) : acc s0 s1 s2 s3 = acc t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => acc x s1 s2 s3) H0))
               (ap (fun x => acc t0 x s2 s3) H1))
            (ap (fun x => acc t0 t1 x s3) H2))
         (ap (fun x => acc t0 t1 t2 x) H3)).
Qed.

Lemma congr_accin {s0 : level} {s1 : term} {s2 : term} {s3 : term}
  {s4 : term} {t0 : level} {t1 : term} {t2 : term} {t3 : term} {t4 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  : accin s0 s1 s2 s3 s4 = accin t0 t1 t2 t3 t4.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans eq_refl (ap (fun x => accin x s1 s2 s3 s4) H0))
                  (ap (fun x => accin t0 x s2 s3 s4) H1))
               (ap (fun x => accin t0 t1 x s3 s4) H2))
            (ap (fun x => accin t0 t1 t2 x s4) H3))
         (ap (fun x => accin t0 t1 t2 t3 x) H4)).
Qed.

Lemma congr_accinv {s0 : level} {s1 : term} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {s6 : term} {t0 : level} {t1 : term} {t2 : term}
  {t3 : term} {t4 : term} {t5 : term} {t6 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5)
  (H6 : s6 = t6) : accinv s0 s1 s2 s3 s4 s5 s6 = accinv t0 t1 t2 t3 t4 t5 t6.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans eq_refl
                           (ap (fun x => accinv x s1 s2 s3 s4 s5 s6) H0))
                        (ap (fun x => accinv t0 x s2 s3 s4 s5 s6) H1))
                     (ap (fun x => accinv t0 t1 x s3 s4 s5 s6) H2))
                  (ap (fun x => accinv t0 t1 t2 x s4 s5 s6) H3))
               (ap (fun x => accinv t0 t1 t2 t3 x s5 s6) H4))
            (ap (fun x => accinv t0 t1 t2 t3 t4 x s6) H5))
         (ap (fun x => accinv t0 t1 t2 t3 t4 t5 x) H6)).
Qed.

Lemma congr_accel {s0 : level} {s1 : level} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {s6 : term} {s7 : term} {t0 : level} {t1 : level}
  {t2 : term} {t3 : term} {t4 : term} {t5 : term} {t6 : term} {t7 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  accel s0 s1 s2 s3 s4 s5 s6 s7 = accel t0 t1 t2 t3 t4 t5 t6 t7.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans
                           (eq_trans eq_refl
                              (ap (fun x => accel x s1 s2 s3 s4 s5 s6 s7) H0))
                           (ap (fun x => accel t0 x s2 s3 s4 s5 s6 s7) H1))
                        (ap (fun x => accel t0 t1 x s3 s4 s5 s6 s7) H2))
                     (ap (fun x => accel t0 t1 t2 x s4 s5 s6 s7) H3))
                  (ap (fun x => accel t0 t1 t2 t3 x s5 s6 s7) H4))
               (ap (fun x => accel t0 t1 t2 t3 t4 x s6 s7) H5))
            (ap (fun x => accel t0 t1 t2 t3 t4 t5 x s7) H6))
         (ap (fun x => accel t0 t1 t2 t3 t4 t5 t6 x) H7)).
Qed.

Lemma congr_accelcomp {s0 : level} {s1 : level} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {s6 : term} {s7 : term} {t0 : level} {t1 : level}
  {t2 : term} {t3 : term} {t4 : term} {t5 : term} {t6 : term} {t7 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  accelcomp s0 s1 s2 s3 s4 s5 s6 s7 = accelcomp t0 t1 t2 t3 t4 t5 t6 t7.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans
                           (eq_trans eq_refl
                              (ap (fun x => accelcomp x s1 s2 s3 s4 s5 s6 s7)
                                 H0))
                           (ap (fun x => accelcomp t0 x s2 s3 s4 s5 s6 s7) H1))
                        (ap (fun x => accelcomp t0 t1 x s3 s4 s5 s6 s7) H2))
                     (ap (fun x => accelcomp t0 t1 t2 x s4 s5 s6 s7) H3))
                  (ap (fun x => accelcomp t0 t1 t2 t3 x s5 s6 s7) H4))
               (ap (fun x => accelcomp t0 t1 t2 t3 t4 x s6 s7) H5))
            (ap (fun x => accelcomp t0 t1 t2 t3 t4 t5 x s7) H6))
         (ap (fun x => accelcomp t0 t1 t2 t3 t4 t5 t6 x) H7)).
Qed.

Lemma congr_obseq {s0 : level} {s1 : term} {s2 : term} {s3 : term}
  {t0 : level} {t1 : term} {t2 : term} {t3 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  obseq s0 s1 s2 s3 = obseq t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => obseq x s1 s2 s3) H0))
               (ap (fun x => obseq t0 x s2 s3) H1))
            (ap (fun x => obseq t0 t1 x s3) H2))
         (ap (fun x => obseq t0 t1 t2 x) H3)).
Qed.

Lemma congr_obsrefl {s0 : level} {s1 : term} {s2 : term} {t0 : level}
  {t1 : term} {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  obsrefl s0 s1 s2 = obsrefl t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => obsrefl x s1 s2) H0))
            (ap (fun x => obsrefl t0 x s2) H1))
         (ap (fun x => obsrefl t0 t1 x) H2)).
Qed.

Lemma congr_J {s0 : level} {s1 : term} {s2 : term} {s3 : term} {s4 : term}
  {s5 : term} {s6 : term} {t0 : level} {t1 : term} {t2 : term} {t3 : term}
  {t4 : term} {t5 : term} {t6 : term} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  : J s0 s1 s2 s3 s4 s5 s6 = J t0 t1 t2 t3 t4 t5 t6.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans eq_refl
                           (ap (fun x => J x s1 s2 s3 s4 s5 s6) H0))
                        (ap (fun x => J t0 x s2 s3 s4 s5 s6) H1))
                     (ap (fun x => J t0 t1 x s3 s4 s5 s6) H2))
                  (ap (fun x => J t0 t1 t2 x s4 s5 s6) H3))
               (ap (fun x => J t0 t1 t2 t3 x s5 s6) H4))
            (ap (fun x => J t0 t1 t2 t3 t4 x s6) H5))
         (ap (fun x => J t0 t1 t2 t3 t4 t5 x) H6)).
Qed.

Lemma congr_cast {s0 : level} {s1 : term} {s2 : term} {s3 : term} {s4 : term}
  {t0 : level} {t1 : term} {t2 : term} {t3 : term} {t4 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) :
  cast s0 s1 s2 s3 s4 = cast t0 t1 t2 t3 t4.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans eq_refl (ap (fun x => cast x s1 s2 s3 s4) H0))
                  (ap (fun x => cast t0 x s2 s3 s4) H1))
               (ap (fun x => cast t0 t1 x s3 s4) H2))
            (ap (fun x => cast t0 t1 t2 x s4) H3))
         (ap (fun x => cast t0 t1 t2 t3 x) H4)).
Qed.

Lemma congr_injpi1 {s0 : level} {s1 : level} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {s6 : term} {t0 : level} {t1 : level} {t2 : term}
  {t3 : term} {t4 : term} {t5 : term} {t6 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5)
  (H6 : s6 = t6) : injpi1 s0 s1 s2 s3 s4 s5 s6 = injpi1 t0 t1 t2 t3 t4 t5 t6.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans eq_refl
                           (ap (fun x => injpi1 x s1 s2 s3 s4 s5 s6) H0))
                        (ap (fun x => injpi1 t0 x s2 s3 s4 s5 s6) H1))
                     (ap (fun x => injpi1 t0 t1 x s3 s4 s5 s6) H2))
                  (ap (fun x => injpi1 t0 t1 t2 x s4 s5 s6) H3))
               (ap (fun x => injpi1 t0 t1 t2 t3 x s5 s6) H4))
            (ap (fun x => injpi1 t0 t1 t2 t3 t4 x s6) H5))
         (ap (fun x => injpi1 t0 t1 t2 t3 t4 t5 x) H6)).
Qed.

Lemma congr_injpi2 {s0 : level} {s1 : level} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {s6 : term} {s7 : term} {t0 : level} {t1 : level}
  {t2 : term} {t3 : term} {t4 : term} {t5 : term} {t6 : term} {t7 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  injpi2 s0 s1 s2 s3 s4 s5 s6 s7 = injpi2 t0 t1 t2 t3 t4 t5 t6 t7.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans
                        (eq_trans
                           (eq_trans eq_refl
                              (ap (fun x => injpi2 x s1 s2 s3 s4 s5 s6 s7) H0))
                           (ap (fun x => injpi2 t0 x s2 s3 s4 s5 s6 s7) H1))
                        (ap (fun x => injpi2 t0 t1 x s3 s4 s5 s6 s7) H2))
                     (ap (fun x => injpi2 t0 t1 t2 x s4 s5 s6 s7) H3))
                  (ap (fun x => injpi2 t0 t1 t2 t3 x s5 s6 s7) H4))
               (ap (fun x => injpi2 t0 t1 t2 t3 t4 x s6 s7) H5))
            (ap (fun x => injpi2 t0 t1 t2 t3 t4 t5 x s7) H6))
         (ap (fun x => injpi2 t0 t1 t2 t3 t4 t5 t6 x) H7)).
Qed.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | var s0 => var (xi_term s0)
  | Sort s0 => Sort s0
  | assm s0 => assm s0
  | Pi s0 s1 s2 s3 =>
      Pi s0 s1 (ren_term xi_term s2) (ren_term (upRen_term_term xi_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      lam s0 s1 (ren_term xi_term s2) (ren_term (upRen_term_term xi_term) s3)
        (ren_term (upRen_term_term xi_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      app s0 s1 (ren_term xi_term s2) (ren_term (upRen_term_term xi_term) s3)
        (ren_term xi_term s4) (ren_term xi_term s5)
  | Nat => Nat
  | zero => zero
  | succ s0 => succ (ren_term xi_term s0)
  | rec s0 s1 s2 s3 s4 =>
      rec s0 (ren_term (upRen_term_term xi_term) s1) (ren_term xi_term s2)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s3)
        (ren_term xi_term s4)
  | acc s0 s1 s2 s3 =>
      acc s0 (ren_term xi_term s1)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s2)
        (ren_term xi_term s3)
  | accin s0 s1 s2 s3 s4 =>
      accin s0 (ren_term xi_term s1)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s2)
        (ren_term xi_term s3) (ren_term xi_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      accinv s0 (ren_term xi_term s1)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s2)
        (ren_term xi_term s3) (ren_term xi_term s4) (ren_term xi_term s5)
        (ren_term xi_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      accel s0 s1 (ren_term xi_term s2)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s5)
        (ren_term xi_term s6) (ren_term xi_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      accelcomp s0 s1 (ren_term xi_term s2)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s5)
        (ren_term xi_term s6) (ren_term xi_term s7)
  | obseq s0 s1 s2 s3 =>
      obseq s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term xi_term s3)
  | obsrefl s0 s1 s2 =>
      obsrefl s0 (ren_term xi_term s1) (ren_term xi_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      J s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term (upRen_term_term xi_term) s3) (ren_term xi_term s4)
        (ren_term xi_term s5) (ren_term xi_term s6)
  | cast s0 s1 s2 s3 s4 =>
      cast s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term xi_term s3) (ren_term xi_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      injpi1 s0 s1 (ren_term xi_term s2) (ren_term xi_term s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term xi_term) s5) (ren_term xi_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      injpi2 s0 s1 (ren_term xi_term s2) (ren_term xi_term s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term xi_term) s5) (ren_term xi_term s6)
        (ren_term xi_term s7)
  end.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (var var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Fixpoint subst_term (sigma_term : nat -> term) (s : term) {struct s} : 
term :=
  match s with
  | var s0 => sigma_term s0
  | Sort s0 => Sort s0
  | assm s0 => assm s0
  | Pi s0 s1 s2 s3 =>
      Pi s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      lam s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3)
        (subst_term (up_term_term sigma_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      app s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5)
  | Nat => Nat
  | zero => zero
  | succ s0 => succ (subst_term sigma_term s0)
  | rec s0 s1 s2 s3 s4 =>
      rec s0 (subst_term (up_term_term sigma_term) s1)
        (subst_term sigma_term s2)
        (subst_term (up_term_term (up_term_term sigma_term)) s3)
        (subst_term sigma_term s4)
  | acc s0 s1 s2 s3 =>
      acc s0 (subst_term sigma_term s1)
        (subst_term (up_term_term (up_term_term sigma_term)) s2)
        (subst_term sigma_term s3)
  | accin s0 s1 s2 s3 s4 =>
      accin s0 (subst_term sigma_term s1)
        (subst_term (up_term_term (up_term_term sigma_term)) s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      accinv s0 (subst_term sigma_term s1)
        (subst_term (up_term_term (up_term_term sigma_term)) s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5) (subst_term sigma_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      accel s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term (up_term_term sigma_term)) s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term (up_term_term sigma_term)) s5)
        (subst_term sigma_term s6) (subst_term sigma_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      accelcomp s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term (up_term_term sigma_term)) s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term (up_term_term sigma_term)) s5)
        (subst_term sigma_term s6) (subst_term sigma_term s7)
  | obseq s0 s1 s2 s3 =>
      obseq s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3)
  | obsrefl s0 s1 s2 =>
      obsrefl s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      J s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5) (subst_term sigma_term s6)
  | cast s0 s1 s2 s3 s4 =>
      cast s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      injpi1 s0 s1 (subst_term sigma_term s2) (subst_term sigma_term s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term sigma_term) s5) (subst_term sigma_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      injpi2 s0 s1 (subst_term sigma_term s2) (subst_term sigma_term s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term sigma_term) s5) (subst_term sigma_term s6)
        (subst_term sigma_term s7)
  end.

Lemma upId_term_term (sigma : nat -> term) (Eq : forall x, sigma x = var x) :
  forall x, up_term_term sigma x = var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_term (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = var x) (s : term) {struct s} :
subst_term sigma_term s = s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1) (idSubst_term sigma_term Eq_term s2)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s3)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s3)
        (idSubst_term sigma_term Eq_term s4)
        (idSubst_term sigma_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 => congr_succ (idSubst_term sigma_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s3)
        (idSubst_term sigma_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s2)
        (idSubst_term sigma_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
        (idSubst_term sigma_term Eq_term s5)
        (idSubst_term sigma_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s3)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s4)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s5)
        (idSubst_term sigma_term Eq_term s6)
        (idSubst_term sigma_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s3)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s4)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s5)
        (idSubst_term sigma_term Eq_term s6)
        (idSubst_term sigma_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s3)
        (idSubst_term sigma_term Eq_term s4)
        (idSubst_term sigma_term Eq_term s5)
        (idSubst_term sigma_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s4)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s5)
        (idSubst_term sigma_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s4)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s5)
        (idSubst_term sigma_term Eq_term s6)
        (idSubst_term sigma_term Eq_term s7)
  end.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | var s0 => ap (var) (Eq_term s0)
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s3)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s3)
        (extRen_term xi_term zeta_term Eq_term s4)
        (extRen_term xi_term zeta_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 => congr_succ (extRen_term xi_term zeta_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s3)
        (extRen_term xi_term zeta_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s2)
        (extRen_term xi_term zeta_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
        (extRen_term xi_term zeta_term Eq_term s5)
        (extRen_term xi_term zeta_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s3)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s4)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s5)
        (extRen_term xi_term zeta_term Eq_term s6)
        (extRen_term xi_term zeta_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s3)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s4)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s5)
        (extRen_term xi_term zeta_term Eq_term s6)
        (extRen_term xi_term zeta_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s3)
        (extRen_term xi_term zeta_term Eq_term s4)
        (extRen_term xi_term zeta_term Eq_term s5)
        (extRen_term xi_term zeta_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s4)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s5)
        (extRen_term xi_term zeta_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s4)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s5)
        (extRen_term xi_term zeta_term Eq_term s6)
        (extRen_term xi_term zeta_term Eq_term s7)
  end.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_term (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s3)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s3)
        (ext_term sigma_term tau_term Eq_term s4)
        (ext_term sigma_term tau_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 => congr_succ (ext_term sigma_term tau_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s3)
        (ext_term sigma_term tau_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s2)
        (ext_term sigma_term tau_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
        (ext_term sigma_term tau_term Eq_term s5)
        (ext_term sigma_term tau_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s3)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s4)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s5)
        (ext_term sigma_term tau_term Eq_term s6)
        (ext_term sigma_term tau_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s3)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s4)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s5)
        (ext_term sigma_term tau_term Eq_term s6)
        (ext_term sigma_term tau_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s3)
        (ext_term sigma_term tau_term Eq_term s4)
        (ext_term sigma_term tau_term Eq_term s5)
        (ext_term sigma_term tau_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s4)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s5)
        (ext_term sigma_term tau_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s4)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s5)
        (ext_term sigma_term tau_term Eq_term s6)
        (ext_term sigma_term tau_term Eq_term s7)
  end.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} : ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | var s0 => ap (var) (Eq_term s0)
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s3)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 =>
      congr_succ (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s5)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s3)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s4)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s5)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s6)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s3)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s4)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s5)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s6)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s5)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s4)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s5)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s4)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s5)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s6)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s7)
  end.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s3)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 =>
      congr_succ (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s5)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s3)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s4)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s5)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s6)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s3)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s4)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term))
           s5)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s6)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s5)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s4)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s5)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s4)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s5)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s6)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s7)
  end.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_term : nat -> nat)
  (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_term (sigma_term : nat -> term)
(zeta_term : nat -> nat) (theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s3)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 =>
      congr_succ
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s5)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s3)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s4)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s5)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s6)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s3)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s4)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term))
           s5)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s6)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s5)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s4)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s5)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s4)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s5)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s6)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s7)
  end.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_term : nat -> term)
  (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_term (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s3)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 =>
      congr_succ
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s5)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s3)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s4)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s5)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s6)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s3)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s4)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term))
           s5)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s6)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s5)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s4)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s5)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s4)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s5)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s6)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s7)
  end.

Lemma renRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : term)
  :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (var) xi x = sigma x) :
  forall x, funcomp (var) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_term (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (var) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_term s = subst_term sigma_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | assm s0 => congr_assm (eq_refl s0)
  | Pi s0 s1 s2 s3 =>
      congr_Pi (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      congr_lam (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s3)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      congr_app (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
        (rinst_inst_term xi_term sigma_term Eq_term s5)
  | Nat => congr_Nat
  | zero => congr_zero
  | succ s0 => congr_succ (rinst_inst_term xi_term sigma_term Eq_term s0)
  | rec s0 s1 s2 s3 s4 =>
      congr_rec (eq_refl s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
  | acc s0 s1 s2 s3 =>
      congr_acc (eq_refl s0) (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
  | accin s0 s1 s2 s3 s4 =>
      congr_accin (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      congr_accinv (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
        (rinst_inst_term xi_term sigma_term Eq_term s5)
        (rinst_inst_term xi_term sigma_term Eq_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accel (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s3)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s4)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s5)
        (rinst_inst_term xi_term sigma_term Eq_term s6)
        (rinst_inst_term xi_term sigma_term Eq_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_accelcomp (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s3)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s4)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s5)
        (rinst_inst_term xi_term sigma_term Eq_term s6)
        (rinst_inst_term xi_term sigma_term Eq_term s7)
  | obseq s0 s1 s2 s3 =>
      congr_obseq (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
  | obsrefl s0 s1 s2 =>
      congr_obsrefl (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      congr_J (eq_refl s0) (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
        (rinst_inst_term xi_term sigma_term Eq_term s5)
        (rinst_inst_term xi_term sigma_term Eq_term s6)
  | cast s0 s1 s2 s3 s4 =>
      congr_cast (eq_refl s0) (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      congr_injpi1 (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s4)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s5)
        (rinst_inst_term xi_term sigma_term Eq_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_injpi2 (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s4)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s5)
        (rinst_inst_term xi_term sigma_term Eq_term s6)
        (rinst_inst_term xi_term sigma_term Eq_term s7)
  end.

Lemma rinstInst'_term (xi_term : nat -> nat) (s : term) :
  ren_term xi_term s = subst_term (funcomp (var) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (var) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (var) s = s.
Proof.
exact (idSubst_term (var) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise : pointwise_relation _ eq (subst_term (var)) id.
Proof.
exact (fun s => idSubst_term (var) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_term (s : term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (var x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (var)) sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_term : nat -> nat) (x : nat) :
  ren_term xi_term (var x) = var (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (var))
    (funcomp (var) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_term X Y :=
    up_term : X -> Y.

#[global] Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global] Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global] Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global]
Instance VarInstance_term : (Var _ _) := @var.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var x) ( at level 5, format "x __term")  :
subst_scope.

#[global]
Instance subst_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_term, Var, ids,
                                            Ren_term, Ren1, ren1,
                                            Up_term_term, Up_term, up_term,
                                            Subst_term, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress unfold up_term_term, upRen_term_term, up_ren
                 | progress cbn[subst_term ren_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1
                  in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_term: rewrite.

#[global] Hint Opaque ren_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

