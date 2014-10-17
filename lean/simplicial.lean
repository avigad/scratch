-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

-- semisimplicial types
-- ====================

import logic algebra.category.constructions data.nat
import logic.axioms.funext

open nat sigma function category functor
open category.opposite


-- some cast calculus -- clean up and move

theorem eq_rec_on_heq {A : Type} {a a' : A} {B : Πa' : A, a = a' → Type} (H1 : a = a')
    (H2 : B a (eq.refl a)) : eq.rec_on H1 H2 == H2 :=
eq.rec_on H1 (heq.from_eq rfl)

theorem eq_cast_to_heq {A B : Type} {a : A} {b : B} {H : A = B} (H1 : b = cast H a) : b == a :=
heq.symm (cast_eq_to_heq (eq.symm H1))


-- For now, axiomatize increasing maps from i to j.
-- Later we can construct them using lists or ordinal types.

universe u
constant inc_map (i j  : nat) : Type.{u}
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

    definition BDnX_obj := @(object (BDn (dpr1_X)))
    definition BDnX_mor := @(morphism (BDn (dpr1_X)))

    definition BDn'_object  (m : nat) :=
      Σb : BDnX_obj m, Πα : inc_map (succ n) m, dpr2_X (BDnX_mor α b)

    definition BDn'_dpair {m : nat} (b : BDnX_obj m)
	(f : Πα : inc_map (succ n) m, dpr2_X (BDnX_mor α b)) : BDn'_object m := dpair b f
    definition BDn'_dpr1 {m : nat} (b : BDn'_object m) := dpr1 b
    definition BDn'_dpr2 {m : nat} (b : BDn'_object m) := dpr2 b

    theorem BDn'_object_equal {m : nat} {b1 b2 : BDn'_object m} (H1 : BDn'_dpr1 b1 = BDn'_dpr1 b2)
      (H2 : eq.rec_on H1 (BDn'_dpr2 b1) = BDn'_dpr2 b2) : b1 = b2 :=
    sigma.equal H1 H2

    theorem temp {m : nat} {b1 b2 : BDn'_object m} (H1 : BDn'_dpr1 b1 = BDn'_dpr1 b2) :
      eq.rec_on H1 (BDn'_dpr2 b1) = λα : inc_map (succ n) m, eq.rec_on H1 (BDn'_dpr2 b1 α) :=
    eq.rec_on H1 rfl

    -- set_option pp.implicit true
    theorem BDn'_object_equal' {m : nat} {b1 b2 : BDn'_object m} (H1 : BDn'_dpr1 b1 = BDn'_dpr1 b2)
      (H2 : ∀α : inc_map (succ n) m, eq.rec_on H1 (BDn'_dpr2 b1 α) = BDn'_dpr2 b2 α) : b1 = b2 :=
    have H3 : (λα : inc_map (succ n) m, eq.rec_on H1 (BDn'_dpr2 b1 α)) = BDn'_dpr2 b2,
      from funext H2,
    BDn'_object_equal H1 (eq.trans (temp H1) H3)

    theorem BDn'_fun_eq {i j : nat} {f1 f2 : BDn'_object i → BDn'_object j}
      (H : ∀b : BDnX_obj i, ∀f : Πα : inc_map (succ n) i, dpr2 X (BDn (dpr1 X) α b),
	f1 (BDn'_dpair b f) = f2 (BDn'_dpair b f)) : f1 = f2 :=
    funext (take b : BDn'_object i, sigma.destruct b H)

    theorem comp_eq_aux {i j : nat} (α : inc_map j i) (α' : inc_map (succ n) j)
	(b : BDn'_object i) :
      dpr2_X (BDnX_mor (inc_comp α α') (BDn'_dpr1 b)) =
	dpr2_X (((BDnX_mor α') ∘ (BDnX_mor α)) (BDn'_dpr1 b)) :=
    have H1 : BDnX_mor (inc_comp α α') = (BDnX_mor α') ∘ (BDnX_mor α), from !respect_comp,
    congr_arg _ (congr_fun H1 _)

    definition BDn'_morphism {i j : nat} (α : inc_map j i) (b : BDn'_object i) : BDn'_object j :=
    BDn'_dpair (BDnX_mor α (BDn'_dpr1 b))
      (take α' : inc_map (succ n) j,
	cast (comp_eq_aux α α' b) (BDn'_dpr2 b (inc_comp α α')))

    -- TODO: why do I have to supply the predicate for eq.rec_on?
    theorem aux (i : nat) (b : BDnX_obj i) (f : Πα : inc_map (succ n) i, dpr2_X (BDnX_mor α b))
	(H1 : BDn'_dpr1 (BDn'_morphism  (@inc_id i) (BDn'_dpair b f)) =
	    BDn'_dpr1 (BDn'_dpair b f)) (α : inc_map (succ n) i) :
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BDnX_mor α b)) H1
	  (BDn'_dpr2 (BDn'_morphism (@inc_id i) (BDn'_dpair b f)) α) =
		BDn'_dpr2 (BDn'_dpair b f) α :=
    let H' := comp_eq_aux (@inc_id i) α (BDn'_dpair b f) in
    have H2 : BDn'_dpr2 (BDn'_morphism (@inc_id i) (BDn'_dpair b f)) α =
      cast H' (f (inc_comp (@inc_id i) α)), from rfl,
    have H3 : @eq.rec_on _ _ _ (fun b e, dpr2_X (BDnX_mor α b)) H1
	(BDn'_dpr2 (BDn'_morphism (@inc_id i) (BDn'_dpair b f)) α) ==
	BDn'_dpr2 (BDn'_dpair b f) α, from
      calc
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BDnX_mor α b)) H1
	  (BDn'_dpr2 (BDn'_morphism (@inc_id i) (BDn'_dpair b f)) α) ==
	  BDn'_dpr2 (BDn'_morphism (@inc_id i) (BDn'_dpair b f)) α : !eq_rec_on_heq
	    ... == f (inc_comp (@inc_id i) α) : eq_cast_to_heq H2
	    ... == f α : dcongr_arg _ (inc_comp_idl _)
	    ... == BDn'_dpr2 (BDn'_dpair b f) α : heq.refl _,
    heq.to_eq H3

    theorem BDn'_respect_id (i : nat) : BDn'_morphism (@inc_id i) = λx, x :=
    have H : ∀b : BDnX_obj i, ∀f : Πα : inc_map (succ n) i, dpr2 X (BDn (dpr1 X) α b),
	BDn'_morphism (@inc_id i) (BDn'_dpair b f) = (BDn'_dpair b f),
      proof
	take b f,
	have H1 : BDn'_dpr1 (BDn'_morphism  (@inc_id i) (BDn'_dpair b f)) = b, from
	  calc
	    BDn'_dpr1 (BDn'_morphism (@inc_id i) (BDn'_dpair b f)) = (BDnX_mor (@inc_id i) b) : rfl
	       ... = id b : congr_fun (@respect_id _ _ _ type_category (BDn (dpr1_X)) i) b
	       ... = b : rfl,  -- TODO: why do we need to supply type_category?
	show BDn'_morphism (@inc_id i) (BDn'_dpair b f) = (BDn'_dpair b f), from
	  BDn'_object_equal' H1 (aux i b f H1)
      qed,
    BDn'_fun_eq H

    theorem aux2a {i j k : nat} (β : inc_map k j) (α : inc_map j i)
      (b : BDnX_obj i) (f : Πα : inc_map (succ n) i, dpr2_X (BDnX_mor α b))
	(α' : inc_map (succ n) k) :
      BDn'_dpr2 ((BDn'_morphism β) ((BDn'_morphism α) (BDn'_dpair b f))) α' ==
	f (inc_comp α (inc_comp β α')) :=
    let b_aux := (BDnX_mor α b), f_aux := (take α' : inc_map (succ n) j,
      cast (comp_eq_aux α α' (BDn'_dpair b f)) (f (inc_comp α α'))) in
    show BDn'_dpr2 ((BDn'_morphism β) ((BDn'_morphism α) (BDn'_dpair b f))) α' ==
	f (inc_comp α (inc_comp β α')), from
      calc
	BDn'_dpr2 ((BDn'_morphism β) ((BDn'_morphism α) (BDn'_dpair b f))) α' ==
	    cast (comp_eq_aux β α' (BDn'_dpair b_aux f_aux)) (f_aux (inc_comp β α')) : !heq.refl
	  ... == f_aux (inc_comp β α') : !cast_heq
	  ... == f (inc_comp α (inc_comp β α')) : !cast_heq

    theorem aux2 (i j k : nat) (β : inc_map k j) (α : inc_map j i)
      (b : BDnX_obj i) (f : Πα : inc_map (succ n) i, dpr2_X (BDnX_mor α b))
	(H1 : BDn'_dpr1 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) =
	    BDn'_dpr1 ((BDn'_morphism β ∘ BDn'_morphism α) (BDn'_dpair b f)))
	(α' : inc_map (succ n) k) :
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BDnX_mor α' b)) H1
	  (BDn'_dpr2 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) α') =
	  BDn'_dpr2 ((BDn'_morphism β ∘ BDn'_morphism α) (BDn'_dpair b f)) α' :=
    let H' := comp_eq_aux (inc_comp α β) α' (BDn'_dpair b f) in
    have H2 : BDn'_dpr2 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) α' =
      cast H' (f (inc_comp (inc_comp α β) α')), from rfl,
    have H3 : @eq.rec_on _ _ _ (fun b e, dpr2_X (BDnX_mor α' b)) H1
	(BDn'_dpr2 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) α') ==
	BDn'_dpr2 ((BDn'_morphism β ∘ BDn'_morphism α) (BDn'_dpair b f)) α', from
      calc
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BDnX_mor α' b)) H1
	    (BDn'_dpr2 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) α') ==
	    BDn'_dpr2 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) α' : !eq_rec_on_heq
	  ... == f (inc_comp (inc_comp α β) α') : eq_cast_to_heq H2
	  ... == f (inc_comp α (inc_comp β α')) : dcongr_arg _ (eq.symm (inc_comp_assoc _ _ _))
	  ... == BDn'_dpr2 ((BDn'_morphism β) ((BDn'_morphism α) (BDn'_dpair b f))) α' :
		   heq.symm (aux2a β α b f α')
	  ... == BDn'_dpr2 ((BDn'_morphism β ∘ BDn'_morphism α) (BDn'_dpair b f)) α' : !heq.refl,
    heq.to_eq H3

    theorem BDn'_respect_comp (i j k : nat) (β : inc_map k j) (α : inc_map j i) :
	BDn'_morphism (inc_comp α β) = BDn'_morphism β ∘ BDn'_morphism α :=
    have H0 : BDnX_mor (inc_comp α β) = (BDnX_mor β) ∘ (BDnX_mor α), from !respect_comp,
    have H : ∀b : BDnX_obj i, ∀f : Πα : inc_map (succ n) i, dpr2 X (BDn (dpr1 X) α b),
	BDn'_morphism (inc_comp α β) (BDn'_dpair b f) =
	  (BDn'_morphism β ∘ BDn'_morphism α) (BDn'_dpair b f),
      proof
	take b f,
	have H1 : BDn'_dpr1 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) =
	    BDn'_dpr1 ((BDn'_morphism β ∘ BDn'_morphism α) (BDn'_dpair b f)), from
	  calc
	    BDn'_dpr1 (BDn'_morphism (inc_comp α β) (BDn'_dpair b f)) =
		(BDnX_mor (inc_comp α β) b) : rfl
	       ... = ((BDnX_mor β) ∘ (BDnX_mor α)) b : congr_fun H0 b
	       ... = BDn'_dpr1 ((BDn'_morphism β ∘ BDn'_morphism α) (BDn'_dpair b f)) : rfl,
	BDn'_object_equal' H1 (aux2 i j k β α b f H1)
      qed,
    BDn'_fun_eq H

  end BDn'

end SSn'
