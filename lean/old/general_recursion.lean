--- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad

-- TODO: replace default by inhabited
-- TODO: use an arbitrary well-founded relation

-- general_recursion.lean
-- ======================

import logic data.nat.sub algebra.relation data.prod
import tools.fake_simplifier

-- for the example at the end
import data.sigma

open nat relation relation.iff_ops prod
open fake_simplifier decidable
open eq.ops

open sigma

-- TODO: move to data.nat.basic
theorem ne_zero_succ_pred {n : ℕ} (H : n ≠ 0) : succ (pred n) = n :=
eq.symm (or.resolve_right (zero_or_succ_pred n) H)

-- TODO: move to data.nat.order
theorem ne_zero_pred_lt {n : ℕ} (H : n ≠ 0) : pred n < n := 
eq.subst (ne_zero_succ_pred H) !self_lt_succ

-- TODO: move to logic.core.decidable
definition by_cases_pos {a : Prop} {b : Type} {C : decidable a} (Hab : a → b) (Hnab : ¬a → b) 
    (Ha : a) : 
  by_cases Hab Hnab = Hab Ha :=
decidable.rec (take Ha : a, rfl) (take Hna : ¬a, absurd Ha Hna) C

definition by_cases_neg {a : Prop} {b : Type} {C : decidable a} (Hab : a → b) (Hnab : ¬a → b) 
    (Hna : ¬a) : 
  by_cases Hab Hnab = Hnab Hna :=
decidable.rec (take Ha : a, absurd Ha Hna) (take Hna : ¬a, rfl) C


namespace gen_rec

-- A general recursion principle
-- -----------------------------
--
-- Data:
--
--   dom : Type
--   codom : dom → Type
--   default : ∀x, codom x
--   measure : dom → ℕ
--   rec_call : (∀x : dom, codom x) → (∀x : dom, codom x)
--
-- and a proof
--
--   rec_decreasing : ∀g1 g2 x, (∀z, measure z < measure x → g1 z = g2 z) → 
--                      rec_call g1 x = rec_call g2 x
--
-- which says that the recursive call only depends on values with measure less than x.
--
-- The result is a function f = rec_measure, satisfying
--
--   f x = rec_call f x

context gen_rec_params

parameters {dom : Type} {codom : dom → Type}
parameter  (default : ∀x, codom x)
parameter  (measure : dom → ℕ)
parameter  (rec_call : (∀x : dom, codom x) → (∀x : dom, codom x))
parameter  (rec_decreasing : ∀g1 g2 x, (∀z, measure z < measure x → g1 z = g2 z) →
             rec_call g1 x = rec_call g2 x)

definition restrict (f : ∀x : dom, codom x) (m : ℕ) (x : dom) :=
if measure x < m then f x else default x

theorem restrict_lt_eq (f : ∀x : dom, codom x) (m : ℕ) (x : dom) (H : measure x < m) :
  restrict f m x = f x := 
if_pos H

theorem restrict_not_lt_eq (f : ∀x : dom, codom x) (m : ℕ) (x : dom) (H : ¬ measure x < m) :
  restrict f m x = default x :=
if_neg H

definition rec_measure_aux : ℕ → (∀x : dom, codom x) :=
nat.rec (λx, default x) (λm g x, if measure x < succ m then rec_call g x else default x)

-- this is the desired function
definition rec_measure (x : dom) : codom x := rec_measure_aux (succ (measure x)) x

theorem rec_measure_aux_spec (m : ℕ) : ∀x, rec_measure_aux m x = restrict rec_measure m x :=
let f' := rec_measure_aux, f := rec_measure in
nat.case_strong_induction_on m
  (take x,
    have H1 : f' 0 x = default x, from rfl,
    have H2 : ¬ measure x < 0, from !not_lt_zero,
    have H3 : restrict f 0 x = default x, from if_neg H2,
    show f' 0 x = restrict f 0 x, from H1 ⬝ H3⁻¹)
  (take m,
    assume IH: ∀n, n ≤ m → ∀x, f' n x = restrict f n x,
    take x : dom,
    show f' (succ m) x = restrict f (succ m) x, from
      by_cases
        (assume H1 : measure x < succ m,
          have H2a : ∀z, measure z < measure x → f' m z = f z, from
            take z,
              assume Hzx : measure z < measure x,
              calc
                f' m z = restrict f m z : IH m !le_refl z
                  ... = f z : restrict_lt_eq _ _ _ (lt_le_trans Hzx (lt_succ_imp_le H1)),
          have H2 : f' (succ m) x = rec_call f x, from
            calc
              f' (succ m) x = if measure x < succ m then rec_call (f' m) x else default x : rfl
                ... = rec_call (f' m) x : if_pos H1
                ... = rec_call f x : rec_decreasing (f' m) f x H2a,
          let m' := measure x in
          have H3a : ∀z, measure z < m' → f' m' z = f z, from
            take z,
              assume Hzx : measure z < measure x,
              calc
                f' m' z = restrict f m' z : IH _ (lt_succ_imp_le H1) _
                  ... = f z : restrict_lt_eq _ _ _ Hzx,
          have H3 : restrict f (succ m) x = rec_call f x, from
            calc
              restrict f (succ m) x = f x : if_pos H1
                ... = f' (succ m') x : eq.refl _
                ... = if measure x < succ m' then rec_call (f' m') x else default x : rfl
                ... = rec_call (f' m') x : if_pos !self_lt_succ
                ... = rec_call f x : rec_decreasing _ _ _ H3a,
          show f' (succ m) x = restrict f (succ m) x,
            from H2 ⬝ H3⁻¹)
        (assume H1 : ¬ measure x < succ m,
          have H2 : f' (succ m) x = default x, from
            calc
              f' (succ m) x = if measure x < succ m then rec_call (f' m) x else default x : rfl
                ... = default x : if_neg H1,
          have H3 : restrict f (succ m) x = default x,
            from if_neg H1,
          show f' (succ m) x = restrict f (succ m) x,
            from H2 ⬝ H3⁻¹))

theorem rec_measure_spec (x : dom): rec_measure x = rec_call rec_measure x :=
let f' := rec_measure_aux, f := rec_measure, m  := measure x in
have H : ∀z, measure z < measure x → f' m z = f z, from
  take z,
    assume H1 : measure z < measure x,
    calc
      f' m z = restrict f m z : rec_measure_aux_spec m z
        ... = f z : restrict_lt_eq _ _ _ H1,
calc
  f x = f' (succ m) x : rfl
    ... = if measure x < succ m then rec_call (f' m) x else default x : rfl
    ... = rec_call (f' m) x : if_pos !self_lt_succ
    ... = rec_call f x : rec_decreasing _ _ _ H

end gen_rec_params

end gen_rec


-- Try it out.
-- ===========

-- vec
-- ---

-- TODO: is there any way to make the second argument to append implicit?
inductive vec (A : Type) : ℕ → Type :=
  empty {} : vec A 0,
  append : A → ∀n, (vec A n → vec A (succ n))

namespace vec
  context
  parameters {A : Type} (a : A) {n : ℕ}
  definition last (v : vec A n) : A := vec.rec a (λa' n v' x, a') v
  definition drop_last (v : vec A n) : vec A (pred n) := vec.rec empty (λa' n v' x, v') v
  definition default (n : nat) : vec A n := nat.rec empty (λn v, append a n v) n 
  end
end vec


-- vec_add
-- -------

definition vec_add_aux_dom : Type.{1} := Σ(n: ℕ) (v1 : vec nat n), vec nat n
definition vec_add_aux_cod (x : vec_add_aux_dom) : Type.{1} := vec nat (dpr1 x)
definition vec_add_aux_default (x : vec_add_aux_dom) : vec_add_aux_cod x := vec.default 0 (dpr1 x)
definition vec_add_aux_measure (x : vec_add_aux_dom) : ℕ := dpr1 x

definition vec_add_aux_rec_call (f : ∀x, vec_add_aux_cod x) (x : vec_add_aux_dom) : 
  vec_add_aux_cod x :=
let n := dpr1 x, v1 := dpr1 (dpr2 x), v2 := dpr2 (dpr2 x) in
by_cases
  (assume H : n = 0, eq.rec_on (eq.symm H) vec.empty)
  (assume H : n ≠ 0,
    have H1 : succ (pred n) = n, from ne_zero_succ_pred H,
    let x1' := vec.last 0 v1, x2' := vec.last 0 v2,
      v1' := vec.drop_last v1, v2' := vec.drop_last v2,
      rec_arg := dpair (pred n) (dpair v1' v2') in
      eq.rec_on H1 (vec.append (x1' + x2') _ (f rec_arg)))

theorem vec_add_aux_decreasing (g1 g2 : ∀x, vec_add_aux_cod x) (x : vec_add_aux_dom)
   (H : ∀z, vec_add_aux_measure z < vec_add_aux_measure x → g1 z = g2 z) :
  vec_add_aux_rec_call g1 x = vec_add_aux_rec_call g2 x :=
let n := dpr1 x, v1 := dpr1 (dpr2 x), v2 := dpr2 (dpr2 x) in
by_cases
  (assume Hz : n = 0, 
    calc
      vec_add_aux_rec_call g1 x = eq.rec_on (eq.symm Hz) vec.empty : by_cases_pos _ _ Hz
        ... = vec_add_aux_rec_call g2 x : eq.symm (by_cases_pos _ _ Hz))
  (assume Hnz : n ≠ 0,
    have H1 [visible] : succ (pred n) = n, from ne_zero_succ_pred Hnz,
    let x1' := vec.last 0 v1, x2' := vec.last 0 v2,
      v1' := vec.drop_last v1, v2' := vec.drop_last v2,
      rec_arg := dpair (pred n) (dpair v1' v2') in
    have H2 : vec_add_aux_measure rec_arg < vec_add_aux_measure x, from ne_zero_pred_lt Hnz,
     calc
      vec_add_aux_rec_call g1 x = eq.rec_on H1 (vec.append (x1' + x2') _ (g1 rec_arg)) :
          by_cases_neg _ _ Hnz
         ... = eq.rec_on H1 (vec.append (x1' + x2') _ (g2 rec_arg)) : {H _ H2}
         ... = vec_add_aux_rec_call g2 x : eq.symm (by_cases_neg _ _ Hnz))

definition vec_add_aux := gen_rec.rec_measure vec_add_aux_default vec_add_aux_measure
    vec_add_aux_rec_call

theorem vec_add_aux_spec_zero (x : vec_add_aux_dom) (H : dpr1 x = 0) : 
  vec_add_aux x = eq.rec_on (eq.symm H) vec.empty :=
eq.trans 
  (gen_rec.rec_measure_spec vec_add_aux_default vec_add_aux_measure 
      vec_add_aux_rec_call vec_add_aux_decreasing x)
  (by_cases_pos _ _ H)

theorem vec_add_aux_spec_not_zero (x : vec_add_aux_dom) (H : dpr1 x ≠ 0) : 
  vec_add_aux x = 
    let n := dpr1 x, 
      v1 := dpr1 (dpr2 x), v2 := dpr2 (dpr2 x),
      H1 := ne_zero_succ_pred H,
      x1' := vec.last 0 v1, x2' := vec.last 0 v2,
      v1' := vec.drop_last v1, v2' := vec.drop_last v2,
      rec_arg := dpair (pred n) (dpair v1' v2') in
      eq.rec_on H1 (vec.append (x1' + x2') _ (vec_add_aux rec_arg)) :=
eq.trans 
  (gen_rec.rec_measure_spec vec_add_aux_default vec_add_aux_measure 
      vec_add_aux_rec_call vec_add_aux_decreasing x)
  (by_cases_neg _ _ H)

definition vec_add {n : ℕ} (v1 v2 : vec nat n) : vec nat n :=
  vec_add_aux (dpair n (dpair v1 v2))

theorem vec_add_zero (v1 v2 : vec nat 0) : vec_add v1 v2 = vec.empty :=
eq.trans (vec_add_aux_spec_zero _ rfl) (eq.rec_on_id _ _)

theorem vec_add_succ {n : ℕ} (v1 v2 : vec nat (succ n)) : 
  vec_add v1 v2 = 
    vec.append (vec.last 0 v1 + vec.last 0 v2) _ (vec_add (vec.drop_last v1) (vec.drop_last v2)) :=
eq.trans (vec_add_aux_spec_not_zero _ !nat.succ_ne_zero) (eq.rec_on_id _ _)


-- easier definition of vec_add
-- ----------------------------

definition vec_add' {n : ℕ} : ∀v1 v2 : vec nat n, vec nat n :=
nat.rec_on n 
  (λv1 v2, vec.empty)
  (take n,
    take f : ∀v1 v2 : vec nat n, vec nat n,
    take v1 v2 : vec nat (succ n),
      vec.append (vec.last 0 v1 + vec.last 0 v2) _ (f (vec.drop_last v1) (vec.drop_last v2)))

theorem vec_add_zero' (v1 v2 : vec nat 0) : vec_add' v1 v2 = vec.empty := rfl

theorem vec_add_succ' {n : nat} (v1 v2 : vec nat (succ n)) : 
  vec_add' v1 v2 = 
    vec.append (vec.last 0 v1 + vec.last 0 v2) _ (vec_add' (vec.drop_last v1) (vec.drop_last v2)) :=
rfl

