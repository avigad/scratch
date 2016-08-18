inductive fibrant [class] (T : Type) : Type :=
fibrant_mk : fibrant T


inductive category [class] (ob : Type) [fob : fibrant ob] : Type :=
mk : Π (hom : ob → ob → Type) [fhom : Πa b : ob, fibrant (hom a b)],
	 category ob

definition hom {ob : Type} [fob : fibrant ob] [C : category ob] :
  ob → ob → Type := category.rec (λ hom fhom, hom) C

definition fhom [instance] {ob : Type} [fob : fibrant ob] [C : category ob] :
  Πa b : ob, fibrant (hom a b) := category.rec (λ hom fhom, fhom) C


inductive Category : Type := mk : Π (ob : Type) (fob : fibrant ob), category ob → Category

definition objects (C : Category) : Type := Category.rec (fun c fc s, c) C

definition objects_fibrant [instance] (C : Category) : fibrant (objects C) :=
Category.rec (fun c fc s, fc) C

definition category_instance [instance] (C : Category) : category (objects C) :=
Category.rec (fun c fc s, s) C


-- this loops

theorem test.{u} (A : Type.{u}) [h : fibrant Category] : Type.{u} := A

section
  variable (A : Type)

  definition test2 := test A
end
