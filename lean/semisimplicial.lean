-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

-- semisimplicial types
-- ====================

-- This construction was explained to me by Richard Garner. I believe it is essentially the
-- same as one presented by Vladimir Voevodsky.
--
-- The intuition: (SS n) and (Bd n) are defined recursively. For each n:
--
--   SS n represents the (n-1)-dimensional simplicial types.
--   For each X : SS n, Bd n X m represents the maps from sk_n (Delta_m) into X.

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

context Bd0

  parameter X : SS0

  definition Bd0_object (m : nat) := X
  definition Bd0_morphism {i j : nat} (α : inc_map j i) (x : Bd0_object i) : Bd0_object j := x
  theorem Bd0_respect_id (i : nat) : Bd0_morphism (@inc_id i) = λx, x := rfl
  theorem Bd0_respect_comp (i j k : nat) (β : inc_map k j) (α : inc_map j i) :
    Bd0_morphism (inc_comp α β) = Bd0_morphism β ∘ Bd0_morphism α := rfl

  definition Bd0 : functor Delta_op type_category :=
  functor.mk Bd0_object (@Bd0_morphism) Bd0_respect_id Bd0_respect_comp

end Bd0


-- successor step
-- --------------

context SSn'

  parameter n : nat

  -- assume n case is done
  parameter SSn : Type
  parameter Bdn (X : SSn) : functor Delta_op type_category

  definition SSn' := ΣX : SSn, (Bdn X (succ n) → Type)

  context Bdn'

    parameter X : SSn'
    definition dpr1_X := dpr1 X
    definition dpr2_X := dpr2 X

    definition BdnX_obj := @(object (Bdn (dpr1_X)))
    definition BdnX_mor := @(morphism (Bdn (dpr1_X)))

    definition Bdn'_object  (m : nat) :=
      Σb : BdnX_obj m, Πα : inc_map (succ n) m, dpr2_X (BdnX_mor α b)

    definition Bdn'_dpair {m : nat} (b : BdnX_obj m)
	(f : Πα : inc_map (succ n) m, dpr2_X (BdnX_mor α b)) : Bdn'_object m := dpair b f
    definition Bdn'_dpr1 {m : nat} (b : Bdn'_object m) := dpr1 b
    definition Bdn'_dpr2 {m : nat} (b : Bdn'_object m) := dpr2 b

    theorem Bdn'_object_equal {m : nat} {b1 b2 : Bdn'_object m} (H1 : Bdn'_dpr1 b1 = Bdn'_dpr1 b2)
      (H2 : eq.rec_on H1 (Bdn'_dpr2 b1) = Bdn'_dpr2 b2) : b1 = b2 :=
    sigma.equal H1 H2

    theorem Bdn'_object_equal' {m : nat} {b1 b2 : Bdn'_object m} (H1 : Bdn'_dpr1 b1 = Bdn'_dpr1 b2)
      (H2 : ∀α : inc_map (succ n) m, eq.rec_on H1 (Bdn'_dpr2 b1 α) = Bdn'_dpr2 b2 α) : b1 = b2 :=
    have H3 : eq.rec_on H1 (Bdn'_dpr2 b1) = λα : inc_map (succ n) m, eq.rec_on H1 (Bdn'_dpr2 b1 α),
      from eq.rec_on H1 rfl,
    have H4 : (λα : inc_map (succ n) m, eq.rec_on H1 (Bdn'_dpr2 b1 α)) = Bdn'_dpr2 b2,
      from funext H2,
    Bdn'_object_equal H1 (eq.trans H3 H4)

    theorem Bdn'_fun_eq {i j : nat} {f1 f2 : Bdn'_object i → Bdn'_object j}
      (H : ∀b : BdnX_obj i, ∀f : Πα : inc_map (succ n) i, dpr2 X (Bdn (dpr1 X) α b),
	f1 (Bdn'_dpair b f) = f2 (Bdn'_dpair b f)) : f1 = f2 :=
    funext (take b : Bdn'_object i, sigma.destruct b H)

    theorem comp_eq_aux {i j : nat} (α : inc_map j i) (α' : inc_map (succ n) j)
	(b : Bdn'_object i) :
      dpr2_X (BdnX_mor (inc_comp α α') (Bdn'_dpr1 b)) =
	dpr2_X (((BdnX_mor α') ∘ (BdnX_mor α)) (Bdn'_dpr1 b)) :=
    have H1 : BdnX_mor (inc_comp α α') = (BdnX_mor α') ∘ (BdnX_mor α), from !respect_comp,
    congr_arg _ (congr_fun H1 _)

    definition Bdn'_morphism {i j : nat} (α : inc_map j i) (b : Bdn'_object i) : Bdn'_object j :=
    Bdn'_dpair (BdnX_mor α (Bdn'_dpr1 b))
      (take α' : inc_map (succ n) j,
	cast (comp_eq_aux α α' b) (Bdn'_dpr2 b (inc_comp α α')))

    -- TODO: why do I have to supply the predicate for eq.rec_on?
    theorem aux (i : nat) (b : BdnX_obj i) (f : Πα : inc_map (succ n) i, dpr2_X (BdnX_mor α b))
	(H1 : Bdn'_dpr1 (Bdn'_morphism  (@inc_id i) (Bdn'_dpair b f)) =
	    Bdn'_dpr1 (Bdn'_dpair b f)) (α : inc_map (succ n) i) :
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BdnX_mor α b)) H1
	  (Bdn'_dpr2 (Bdn'_morphism (@inc_id i) (Bdn'_dpair b f)) α) =
		Bdn'_dpr2 (Bdn'_dpair b f) α :=
    let H' := comp_eq_aux (@inc_id i) α (Bdn'_dpair b f) in
    have H2 : Bdn'_dpr2 (Bdn'_morphism (@inc_id i) (Bdn'_dpair b f)) α =
      cast H' (f (inc_comp (@inc_id i) α)), from rfl,
    have H3 : @eq.rec_on _ _ _ (fun b e, dpr2_X (BdnX_mor α b)) H1
	(Bdn'_dpr2 (Bdn'_morphism (@inc_id i) (Bdn'_dpair b f)) α) ==
	Bdn'_dpr2 (Bdn'_dpair b f) α, from
      calc
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BdnX_mor α b)) H1
	  (Bdn'_dpr2 (Bdn'_morphism (@inc_id i) (Bdn'_dpair b f)) α) ==
	  Bdn'_dpr2 (Bdn'_morphism (@inc_id i) (Bdn'_dpair b f)) α : !eq_rec_on_heq
	    ... == f (inc_comp (@inc_id i) α) : eq_cast_to_heq H2
	    ... == f α : dcongr_arg _ (inc_comp_idl _)
	    ... == Bdn'_dpr2 (Bdn'_dpair b f) α : heq.refl _,
    heq.to_eq H3

    theorem Bdn'_respect_id (i : nat) : Bdn'_morphism (@inc_id i) = λx, x :=
    have H : ∀b : BdnX_obj i, ∀f : Πα : inc_map (succ n) i, dpr2 X (Bdn (dpr1 X) α b),
	Bdn'_morphism (@inc_id i) (Bdn'_dpair b f) = (Bdn'_dpair b f),
      proof
	take b f,
	have H1 : Bdn'_dpr1 (Bdn'_morphism  (@inc_id i) (Bdn'_dpair b f)) = b, from
	  calc
	    Bdn'_dpr1 (Bdn'_morphism (@inc_id i) (Bdn'_dpair b f)) = (BdnX_mor (@inc_id i) b) : rfl
	       ... = id b : congr_fun (@respect_id _ _ _ type_category (Bdn (dpr1_X)) i) b
	       ... = b : rfl,  -- TODO: why do we need to supply type_category?
	show Bdn'_morphism (@inc_id i) (Bdn'_dpair b f) = (Bdn'_dpair b f), from
	  Bdn'_object_equal' H1 (aux i b f H1)
      qed,
    Bdn'_fun_eq H

    theorem aux2a {i j k : nat} (β : inc_map k j) (α : inc_map j i)
      (b : BdnX_obj i) (f : Πα : inc_map (succ n) i, dpr2_X (BdnX_mor α b))
	(α' : inc_map (succ n) k) :
      Bdn'_dpr2 ((Bdn'_morphism β) ((Bdn'_morphism α) (Bdn'_dpair b f))) α' ==
	f (inc_comp α (inc_comp β α')) :=
    let b_aux := (BdnX_mor α b), f_aux := (take α' : inc_map (succ n) j,
      cast (comp_eq_aux α α' (Bdn'_dpair b f)) (f (inc_comp α α'))) in
    show Bdn'_dpr2 ((Bdn'_morphism β) ((Bdn'_morphism α) (Bdn'_dpair b f))) α' ==
	f (inc_comp α (inc_comp β α')), from
      calc
	Bdn'_dpr2 ((Bdn'_morphism β) ((Bdn'_morphism α) (Bdn'_dpair b f))) α' ==
	    cast (comp_eq_aux β α' (Bdn'_dpair b_aux f_aux)) (f_aux (inc_comp β α')) : !heq.refl
	  ... == f_aux (inc_comp β α') : !cast_heq
	  ... == f (inc_comp α (inc_comp β α')) : !cast_heq

    theorem aux2 (i j k : nat) (β : inc_map k j) (α : inc_map j i)
      (b : BdnX_obj i) (f : Πα : inc_map (succ n) i, dpr2_X (BdnX_mor α b))
	(H1 : Bdn'_dpr1 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) =
	    Bdn'_dpr1 ((Bdn'_morphism β ∘ Bdn'_morphism α) (Bdn'_dpair b f)))
	(α' : inc_map (succ n) k) :
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BdnX_mor α' b)) H1
	  (Bdn'_dpr2 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) α') =
	  Bdn'_dpr2 ((Bdn'_morphism β ∘ Bdn'_morphism α) (Bdn'_dpair b f)) α' :=
    let H' := comp_eq_aux (inc_comp α β) α' (Bdn'_dpair b f) in
    have H2 : Bdn'_dpr2 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) α' =
      cast H' (f (inc_comp (inc_comp α β) α')), from rfl,
    have H3 : @eq.rec_on _ _ _ (fun b e, dpr2_X (BdnX_mor α' b)) H1
	(Bdn'_dpr2 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) α') ==
	Bdn'_dpr2 ((Bdn'_morphism β ∘ Bdn'_morphism α) (Bdn'_dpair b f)) α', from
      calc
	@eq.rec_on _ _ _ (fun b e, dpr2_X (BdnX_mor α' b)) H1
	    (Bdn'_dpr2 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) α') ==
	    Bdn'_dpr2 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) α' : !eq_rec_on_heq
	  ... == f (inc_comp (inc_comp α β) α') : eq_cast_to_heq H2
	  ... == f (inc_comp α (inc_comp β α')) : dcongr_arg _ (eq.symm (inc_comp_assoc _ _ _))
	  ... == Bdn'_dpr2 ((Bdn'_morphism β) ((Bdn'_morphism α) (Bdn'_dpair b f))) α' :
		   heq.symm (aux2a β α b f α')
	  ... == Bdn'_dpr2 ((Bdn'_morphism β ∘ Bdn'_morphism α) (Bdn'_dpair b f)) α' : !heq.refl,
    heq.to_eq H3

    theorem Bdn'_respect_comp (i j k : nat) (β : inc_map k j) (α : inc_map j i) :
	Bdn'_morphism (inc_comp α β) = Bdn'_morphism β ∘ Bdn'_morphism α :=
    have H0 : BdnX_mor (inc_comp α β) = (BdnX_mor β) ∘ (BdnX_mor α), from !respect_comp,
    have H : ∀b : BdnX_obj i, ∀f : Πα : inc_map (succ n) i, dpr2 X (Bdn (dpr1 X) α b),
	Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f) =
	  (Bdn'_morphism β ∘ Bdn'_morphism α) (Bdn'_dpair b f),
      proof
	take b f,
	have H1 : Bdn'_dpr1 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) =
	    Bdn'_dpr1 ((Bdn'_morphism β ∘ Bdn'_morphism α) (Bdn'_dpair b f)), from
	  calc
	    Bdn'_dpr1 (Bdn'_morphism (inc_comp α β) (Bdn'_dpair b f)) =
		(BdnX_mor (inc_comp α β) b) : rfl
	       ... = ((BdnX_mor β) ∘ (BdnX_mor α)) b : congr_fun H0 b
	       ... = Bdn'_dpr1 ((Bdn'_morphism β ∘ Bdn'_morphism α) (Bdn'_dpair b f)) : rfl,
	Bdn'_object_equal' H1 (aux2 i j k β α b f H1)
      qed,
    Bdn'_fun_eq H

    definition Bdn' : functor Delta_op type_category :=
    functor.mk Bdn'_object (@Bdn'_morphism) Bdn'_respect_id Bdn'_respect_comp

  end Bdn'

end SSn'
