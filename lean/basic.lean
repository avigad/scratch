-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import logic.axioms.funext path_new

open eq eq.ops path fibrant

inductive category [class] (ob : Type) [fob : fibrant ob] : Type :=
mk : Π (hom : ob → ob → Type) [fhom : Πa b : ob, fibrant (hom a b)]
       (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
       (id : Π {a : ob}, hom a a),
       (Π ⦃a b c d : ob⦄ {h : hom c d} {g : hom b c} {f : hom a b},
           comp h (comp g f) ≈ comp (comp h g) f) →
       (Π ⦃a b : ob⦄ {f : hom a b}, comp id f ≈ f) →
       (Π ⦃a b : ob⦄ {f : hom a b}, comp f id ≈ f) →
         category ob

axiom category_fibrant (ob : Type) [fob : fibrant ob] : fibrant (category ob)
instance [persistent] category_fibrant

namespace category
  variables {ob : Type} [fob : fibrant ob] [C : category ob]
  variables {a b c d : ob}
  include C

  definition hom [reducible] : ob → ob → Type := rec (λ hom fhom compose id assoc idr idl, hom) C
  -- note: needs to be reducible to typecheck composition in opposite category

  definition fhom [instance] [reducible] : Πa b : ob, fibrant (hom a b) := 
  rec (λ hom fhom compose id assoc idr idl, fhom) C

  definition compose [reducible] : Π {a b c : ob}, hom b c → hom a b → hom a c :=
  rec (λ hom fhom compose id assoc idr idl, compose) C

  definition id [reducible] : Π {a : ob}, hom a a := rec (λ hom fhom compose id assoc idr idl, id) C
  definition ID [reducible] (a : ob) : hom a a := id

  infixr `∘`:60 := compose
  infixl `⟶`:25 := hom -- input ⟶ using \--> (this is a different arrow than \-> (→))

  variables {h : hom c d} {g : hom b c} {f : hom a b} {i : hom a a}

  theorem assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
      (h ∘ (g ∘ f)) ≈ ((h ∘ g) ∘ f) :=
  rec (λ hom fhom comp id assoc idr idl, assoc) C

  theorem id_left  : Π ⦃a b : ob⦄ (f : hom a b), id ∘ f ≈ f :=
  rec (λ hom fhom comp id assoc idl idr, idl) C
  theorem id_right : Π ⦃a b : ob⦄ (f : hom a b), f ∘ id ≈ f :=
  rec (λ hom fhom comp id assoc idl idr, idr) C

  --the following is the only theorem for which "include C" is necessary if C is a variable (why?)
  theorem id_compose (a : ob) : (ID a) ∘ id ≈ id := !id_left

  theorem left_id_unique (H : Π{b} {f : hom b a}, i ∘ f ≈ f) : i ≈ id :=
  calc i ≈ i ∘ id : id_right
     ... ≈ id     : H

  theorem right_id_unique (H : Π{b} {f : hom a b}, f ∘ i ≈ f) : i ≈ id :=
  calc i ≈ id ∘ i : id_left
     ... ≈ id     : H
end category

inductive Category : Type := mk : Π (ob : Type) [fob : fibrant ob], category ob → Category

namespace category
  definition Mk {ob} [fob] (C) : Category := @Category.mk ob fob C
  definition MK a [fa] b [fb] (c d e f g) : Category := 
    @Category.mk a fa (@category.mk a fa b fb c d e f g)

  definition objects [coercion] [reducible] (C : Category) : Type := 
  Category.rec (fun c fc s, c) C

  definition objects_fibrant [instance] [reducible] (C : Category) : fibrant (objects C) := 
  Category.rec (fun c fc s, fc) C

  -- TODO: Floris made this a coercion as well. I removed that to eliminate one possible
  -- source of problems
  definition category_instance [instance] [reducible] (C : Category) : 
    category (objects C) :=
  Category.rec (fun c fc s, s) C

end category

axiom Category_fibrant : fibrant Category
instance [persistent] Category_fibrant

open category

-- TODO: causes looping - Lean freezes for 30 seconds 
-- theorem Category.equal (C : Category) : 
--    (@Category.mk C (objects_fibrant C) C) ≈ C := sorry

-- freezes too
-- theorem Category.equal (C : Category) : 
--    (Category.mk C C) ≈ C := sorry

-- also freezes
-- theorem Category.equal (C : Category) : 
--     @path Category Category_fibrant (@Category.mk C (objects_fibrant C) C) C :=
-- Category.rec (λ ob fob s, idp) C

-- TODO: why do both fibrancy judgments have to be inserted manually?
theorem Category.equal (C : Category) : 
    @path Category Category_fibrant (@Category.mk C (objects_fibrant C) (category_instance C)) C :=
Category.rec (λ ob fob s, @idpath Category Category_fibrant _) C

-- this loops, even without the axiom and instance Category_fibrant
-- theorem test.{u} (A : Type.{u}) [h : fibrant Category] : Type.{u} := A
-- 
-- section
--   variable (A : Type)
-- 
--   definition test2 := test A
-- end

-- strange -- this loops -- 
-- theorem test.{u v} (C : Category.{u v}) [hC : fibrant C] : Category.{u v} := C
--
-- section
--   variable (C : Category)
--
--   definition test2 := test C
-- end

