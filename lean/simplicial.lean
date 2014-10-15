-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

-- experimenting with the definition of semisimplicial types

import logic algebra.category.constructions data.nat

-- TODO: do we need this?
-- import logic.axioms.funext

open nat sigma function category functor
open category.opposite

-- For now, axiomatize increasing maps from i to j.
-- Later we can construct them using lists or ordinal types.

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
instance type_category


-- level 0: the connected components
-- ---------------------------------

definition SS0 := Type

context BD0

  parameter X : SS0

  definition BD0_object (m : nat) := X
  definition BD0_morphism {i j : nat} (α : inc_map j i) (x : BD0_object i) : BD0_object j := x
  theorem BD0_respect_id (i : nat) : BD0_morphism (@inc_id i) = λx, x := rfl
  theorem BD0_respect_comp (i j k : nat) (β : inc_map k j) (α : inc_map j i) :
    BD0_morphism (inc_comp α β) = BD0_morphism β ∘ BD0_morphism α := rfl

  definition BD0 : functor Delta_op type_category :=
  functor.mk BD0_object (@BD0_morphism) BD0_respect_id BD0_respect_comp

end BD0


-- successor step
-- --------------

context SSn'

  parameter n : nat

  -- assume n case is done
  parameter SSn : Type
  parameter BDn (X : SSn) : functor Delta_op type_category

  definition SSn' := ΣX : SSn, (BDn X (succ n) → Type)

  context BDn'

    parameter X : SSn'
    definition dpr1_X := dpr1 X
    definition dpr2_X := dpr2 X

    definition BDnX_mor := @morphism _ _ _ _ (BDn (dpr1_X))

    definition BDn'_object  (m : nat) :=
      Σb : BDn (dpr1 X) m, Πα : inc_map (succ n) m, dpr2 X (BDn (dpr1 X) α b)
    definition BDn'_dpair {m : nat} (b : BDn (dpr1 X) m)
	(f : Πα : inc_map (succ n) m, dpr2 X (BDn (dpr1 X) α b)) : BDn'_object m := dpair b f
    definition BDn'_dpr1 {m : nat} (b : BDn'_object m) := dpr1 b
    definition BDn'_dpr2 {m : nat} (b : BDn'_object m) := dpr2 b

    definition BDn'_morphism {i j : nat} (α : inc_map j i) (b : BDn'_object i) : BDn'_object j :=
    BDn'_dpair (BDnX_mor α (BDn'_dpr1 b))
      (take α' : inc_map (succ n) j,
	let t1 := BDnX_mor (inc_comp α α'),
	  t2 := (BDnX_mor α') ∘ (BDnX_mor α) in
	have H1 : t1 = t2, from !respect_comp,
	have H : dpr2_X (t1 (BDn'_dpr1 b)) = dpr2_X (t2 (BDn'_dpr1 b)),
	  from congr_arg _ (congr_fun H1 _),
	cast H (BDn'_dpr2 b (inc_comp α α')))

end BDn'

end SSn'