-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

-- experimenting with the definition of semisimplicial types

import logic algebra.category.constructions data.nat

-- TODO: do we need this?
-- import logic.axioms.funext

open nat sigma function category functor
open category.opposite

-- For now, axiomatize increasing maps from i to j. Later we can construct them using lists,
-- or even ordinal types.

constant inc_map_op (i j  : nat) : Type
constant inc_id_op {i : nat} : inc_map_op i i
constant inc_comp_op ⦃i j k : nat⦄ (α : inc_map_op j k) (β : inc_map_op i j) : inc_map_op i k
axiom inc_comp_assoc_op ⦃i j k l : nat⦄ (α : inc_map_op k l) (β : inc_map_op j k) (γ : inc_map_op i j) :
  inc_comp_op α (inc_comp_op β γ) = inc_comp_op (inc_comp_op α β) γ
axiom inc_comp_idr_op ⦃i j : nat⦄ (α : inc_map_op i j) : inc_comp_op α inc_id_op = α
axiom inc_comp_idl_op ⦃i j : nat⦄ (α : inc_map_op i j) : inc_comp_op inc_id_op α = α

definition Delta_op [instance] := category.mk inc_map_op inc_comp_op @inc_id_op inc_comp_assoc_op
    inc_comp_idl_op inc_comp_idr_op
instance type_category

definition semisimplicial_strict : category (functor Delta_op type_category) :=
functor_category Delta_op type_category


-- at level 0: the connected components

definition SS0 := Type

context BD0

parameter X : SS0

set_option pp.implicit true

definition BD0_object (m : nat) := X
definition BD0_morphism {i j : nat} (α : inc_map_op i j) (x : BD0_object i) : BD0_object j := x
theorem BD0_respect_id (i : nat) : BD0_morphism (@inc_id_op i) = λx, x := rfl
theorem BD0_respect_comp (i j k : nat) (α : inc_map_op j k) (β : inc_map_op i j) :
  BD0_morphism (inc_comp_op α β) = BD0_morphism β ∘ BD0_morphism α := rfl

definition BD0 : functor Delta_op type_category :=
functor.mk BD0_object (@BD0_morphism) BD0_respect_id BD0_respect_comp

end BD0


context SSn' -- successor case

parameter n : nat

-- assume n case is done
parameter SSn : Type
parameter BDn (X : SSn) : functor Delta_op type_category

definition SSn' := ΣX : SSn, (BDn X (succ n) → Type)

context BDn'

parameter X : SSn'

definition dpr1_X : SSn := dpr1 X
definition dpr2_X : BDn (dpr1 X) (succ n) → Type := dpr2 X

definition BDn'_object  (m : nat) :=
  Σb : BDn (dpr1 X) m, Πα : inc_map_op m (succ n), dpr2 X (BDn (dpr1 X) α b)

definition BDn'_dpr1 {m : nat} (b : BDn'_object m) : BDn (dpr1 X) m := dpr1 b
definition BDn'_dpr2 {m : nat} (b : BDn'_object m) :
    Πα : inc_map_op m (succ n), dpr2 X (BDn (dpr1 X) α (BDn'_dpr1 b)) := dpr2 b

-- set_option unifier.max_steps 100000
-- set_option pp.implicit true
-- set_option pp.coercions true
definition BDn'_morphism {i j : nat} (α : inc_map_op i j) (b : BDn'_object i) : BDn'_object j :=
  dpair (BDn (dpr1_X) α (dpr1 b))
    (take α' : inc_map_op j (succ n),
      let t1 := BDn (dpr1_X) (inc_comp_op α' α),
	t2 := (BDn (dpr1_X) α') ∘ (BDn (dpr1_X) α) in
      have H : t1 = t2, from !respect_comp,
      let t3 := BDn'_dpr2 b, t4 := inc_comp_op α' α in
      let t5 := t3 t4 in
      have H1 : (t1 (BDn'_dpr1 b)) = (t2 (BDn'_dpr1 b)), from congr_fun H _,
      have H2 : dpr2_X (t1 (BDn'_dpr1 b)) = dpr2_X (t2 (BDn'_dpr1 b)), from congr_arg _ H1,
      show dpr2 X (BDn (dpr1_X) α' (BDn (dpr1_X) α (BDn'_dpr1 b))), from cast H2 t5)

end BDn'

end SSn'
