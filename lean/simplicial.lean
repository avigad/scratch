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

constant inc_map (i j  : nat) : Type
constant inc_id {i : nat} : inc_map i i
constant inc_comp ⦃i j k : nat⦄ (α : inc_map j k) (β : inc_map i j) : inc_map i k
axiom inc_comp_assoc ⦃i j k l : nat⦄ (α : inc_map k l) (β : inc_map j k) (γ : inc_map i j) :
  inc_comp α (inc_comp β γ) = inc_comp (inc_comp α β) γ
axiom inc_comp_idr ⦃i j : nat⦄ (α : inc_map i j) : inc_comp α inc_id = α
axiom inc_comp_idl ⦃i j : nat⦄ (α : inc_map i j) : inc_comp inc_id α = α

definition Delta := category.mk (λi j, inc_map i j) inc_comp @inc_id inc_comp_assoc
    inc_comp_idl inc_comp_idr

definition Delta_op [instance] := opposite Delta

definition semisimplicial_strict : category (functor (opposite Delta) type_category) :=
functor_category (opposite Delta) type_category


-- at level 0: the connected components

definition SS0 := Type

context BD0

parameter X : SS0

definition BD0_object (m : nat) := X
definition BD0_morphism {i j : nat} (α : inc_map j i) (x : BD0_object i) : BD0_object j := x
definition BD0_respect_id (i : nat) : BD0_morphism (@inc_id i) = λx, x := rfl
definition BD0_respect_comp (i j k : nat) (β : inc_map k j) (α : inc_map j i) :
  BD0_morphism (inc_comp α β) = BD0_morphism β ∘ BD0_morphism α := rfl

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

definition BDn'_object (m : nat) :=
  Σb : BDn (dpr1 X) m, Πα : inc_map (succ n) m, dpr2 X (BDn (dpr1 X) α b)

theorem test (i j : nat) (α : inc_map j i) (α' : inc_map (succ n) j) :
  BDn (dpr1 X) (inc_comp α α') = (BDn (dpr1 X) α') ∘ (BDn (dpr1 X) α) :=
@respect_comp nat Type Delta_op type_category (BDn (dpr1 X)) _ _ _ α' α

-- set_option pp.implicit true
-- set_option pp.coercions true
definition BDn'_morphism {i j : nat} (α : inc_map j i) (b : BDn'_object i) : BDn'_object j :=
  dpair (BDn (dpr1 X) α (dpr1 b))
    (take α' : inc_map (succ n) j,
      let t1 := (BDn (dpr1 X) (inc_comp α α')),
	t2 := ((BDn (dpr1 X) α') ∘ (BDn (dpr1 X) α)) in
      have H : t1 = t2, from !respect_comp,
-- fails
--      let t3 := dpr2 b, t4 := inc_comp α α' in
      let t3 := (typeof dpr2 b : _), t4 := inc_comp α α' in
      let t5 := t3 t4 in
      show dpr2 X (BDn (dpr1 X) α' (BDn (dpr1 X) α (dpr1 b))), from sorry)

end BDn'

end SSn'
