import path_new

open path

inductive category [class] (ob : Type) [fob : fibrant ob] : Type :=
mk : Π (hom : ob → ob → Type) [fhom : Πa b : ob, fibrant (hom a b)]
       (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
       (id : Π {a : ob}, hom a a),
       (Π ⦃a b c d : ob⦄ {h : hom c d} {g : hom b c} {f : hom a b},
	   comp h (comp g f) ≈ comp (comp h g) f) →
       (Π ⦃a b : ob⦄ {f : hom a b}, comp id f ≈ f) →
       (Π ⦃a b : ob⦄ {f : hom a b}, comp f id ≈ f) →
	 category ob

namespace category
  variables {ob : Type} [fob : fibrant ob] [C : category ob]
  variables {a b c d : ob}
  include C

  definition hom [reducible] : ob → ob → Type := rec (λ hom fhom compose id assoc idr idl, hom) C
  -- note: needs to be reducible to typecheck composition in opposite category

  definition fhom [instance] [reducible] : Πa b : ob, fibrant (hom a b) :=
  rec (λ hom fhom compose id assoc idr idl, fhom) C

end category

inductive Category : Type := mk : Π (ob : Type) [fob : fibrant ob], category ob → Category

namespace category

  definition objects [coercion] [reducible] (C : Category) : Type :=
  Category.rec (fun c fc s, c) C

  definition objects_fibrant [instance] [reducible] (C : Category) : fibrant (objects C) :=
  Category.rec (fun c fc s, fc) C

  definition category_instance [instance] [reducible] (C : Category) :
    category (objects C) :=
  Category.rec (fun c fc s, s) C

end category

open category

-- this loops

theorem test.{u} (A : Type.{u}) [h : fibrant Category] : Type.{u} := A

section
  variable (A : Type)

  definition test2 := test A
end
