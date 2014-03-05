----------------------------------------------------------------------------------------------------
--
-- test_algebra2.lean
-- Jeremy Avigad
--
-- Trying to handle the algebraic hierarchy, with explicit casts.
--
----------------------------------------------------------------------------------------------------

import macros

-- universe U ≥ 2

-- simulate the "real" version of cast
-- note that this will ensure that we are only using casts on small types
definition cast' {A B : Type} (e : A = B) := cast (to_heq e)

-- variable Sigma (A : Type) (B : A → Type) : Type
-- variable Pair {A : Type} {B : A → Type} (a : A) (b : B a) : Sigma A B
-- variable Fst {A : Type} {B : A → Type} (p : Sigma A B) : A
-- variable Snd {A : Type} {B : A → Type} (p : Sigma A B) : B (Fst p)
-- axiom FstAx {A : Type} {B : A → Type} (a : A) (b : B a) : @Fst A B (Pair a b) = a
-- axiom SndAx {A : Type} {B : A → Type} (a : A) (b : B a) : @Snd A B (Pair a b) == b

-- variable A : Type 
-- variable B : A → Type 
-- variable a : A 
-- variable b : B a

-- check @Snd A B (Pair a b)

--
-- Classes of structures, and axiomatic classes of structures
--

-- A "structure" consists of a carrier, and some data (whose type depends on the carrier)

definition StructType : (Type 1) := Type → Type   -- the type of the data

-- record type
variable Structure (S : StructType) : (Type 1)

-- constructor
variable mk_Structure {S : StructType} {T : Type} (d : S T) : Structure S 

-- first projection
variable carrier {S : StructType} (M : Structure S) : Type

-- second projection
variable data {S : StructType} (M : Structure S) : S (carrier M)

axiom carrier_structure_eq {S : StructType} {T : Type} (d : S T) : carrier (mk_Structure d) = T

axiom data_structure_eq {S : StructType} {T : Type} (d : S T) : data (mk_Structure d) == d


-- An "axiomatic class" is a class of structures satisfying some predicate (the "axioms")

-- record type
variable AxClass : (Type 1)

-- constructor
variable mk_AxClass {S : StructType} (P : Structure S → Bool) : AxClass

-- first projection
variable struct_type (C : AxClass) : StructType

-- second projection
variable axioms {C : AxClass} (M : Structure (struct_type C)) : Bool

axiom struct_type_axclass_eq {S : StructType} (P : Structure S → Bool) : 
  struct_type (mk_AxClass P) = S

axiom axioms_axclass_eq {S : StructType} (P : Structure S → Bool) : 
  @axioms (mk_AxClass P) == P


-- An instance of the class is a structure satisfying the axioms

-- record type
variable Instance (C : AxClass) : (Type 1)

-- constructor
variable mk_Instance {C : AxClass} {M : Structure (struct_type C)} (H : axioms M) : Instance C
-- := pair M H

-- first projection
variable struct {C : AxClass} (M : Instance C) : Structure (struct_type C)

-- second projection
variable hyps {C : AxClass} (M : Instance C) : axioms (struct M)

axiom struct_instance_eq {C : AxClass} {M : Structure (struct_type C)} (H : axioms M) : 
  struct (mk_Instance H) = M

axiom hyps_instance_eq {C : AxClass} {M : Structure (struct_type C)} (H : axioms M) : 
  hyps (mk_Instance H) == H



--
-- Some axiomatic classes
--

--
-- Structure MulStruct (for overloading *)
--

definition MulStruct : StructType
:= λ T, T → T → T

definition MulClass : AxClass := mk_AxClass (λ M : Structure MulStruct, true)

-- ultimately, the cast e should be inserted automatically
definition mul {C : AxClass} {M : Instance C} {M' : Instance MulClass} 
   (e : @eq Type (carrier (struct M)) (carrier (struct M'))) 
   (x : carrier (struct M)) (y : carrier (struct M)) : carrier (struct M)
:= 
  have e' : struct_type MulClass = MulStruct, from struct_type_axclass_eq _,
  let m' := data (cast' e' (struct M')) in
  let x' := cast' e x in
  let y' := cast' e y in
  cast' (symm e) (m' x' y')


--
-- AxClass Semigroup : associative MulStruct
--

definition Semigroup := mk_AxClass (λ M : Structure MulStruct, 
  let m := data M in ∀ x y z : carrier M, m (m x y) z = m x (m y z))

theorem mul_assoc {C : AxClass} {M : Instance C} {M' : Instance Semigroup} (e : carrier (struct M) = carrier (struct M'))
  : ∀ x y z : carrier (struct M), mul e (mul e x y) z = mul e x (mul e y z)
:= 
  _

-- The cast e signals that we are viewing M as the MulStruct M'.
-- definition mul_is_assoc {S : StructType} {M : Structure S} {M' : Structure MulStruct} 
--   (e : carrier M = carrier M') : Bool
-- :=  ∀ x y z : carrier M, mul e (mul e x y) z = mul e x (mul e y z)

-- -- once again, in practice, the fact that a multiplication is associative is a "hole"
-- -- that should be inferred automatically
-- theorem mul_assoc {S : StructType} {M : Structure S} {M' : Structure MulStruct} 
--   (e : carrier M = carrier M') (H : mul_is_assoc e) : 
--   ∀ x y z : carrier M, mul e (mul e x y) z = mul e x (mul e y z)
-- := H

-- definition mul_is_comm {S : StructClass} {M : structure S} {M' : structure MulStruct} 
--   (e : carrier M = carrier M') : Bool
-- := 
--   ∀ x y z : carrier M, mul e x y = mul e y x

-- -- this is how you view a mulstruct as a mulstruct
-- theorem mulstruct_as_mulstruct (M : structure MulStruct) : carrier M = carrier M
-- := refl _

-- set_opaque MulStruct true
-- set_opaque mul true
-- set_opaque mul_is_assoc true
-- set_opaque mul_is_comm true


-- -- semigroups

-- -- note: mk_AxClass doesn't work here, even though it is defined to be pair
-- definition Semigroup : AxClass
-- := pair MulStruct (λ M, (mul_is_assoc (mulstruct_as_mulstruct M)))

-- -- this is how you view a semigroup as a mulstruct
-- theorem semigroup_as_mulstruct (M : instance Semigroup) : carrier (struct M) = carrier (struct M)
-- := refl _

-- -- to fill the hole in mul_assoc

-- -- question: why do we have to make mul_is_assoc transparent here?
-- variable M : instance Semigroup
-- check hyps M -- axioms (struct M)
-- -- eval axioms M -- fails
-- eval @axioms Semigroup (struct M)
-- -- if I make struct opaque, I need to write
-- -- eval @axioms Semigroup (@struct Semigroup M)

-- set_opaque mul_is_assoc false

-- theorem semigroup_mul_is_assoc (M : instance Semigroup) : 
--   mul_is_assoc (mulstruct_as_mulstruct (struct M))
-- := hyps M

-- set_opaque mul_is_assoc true



-- definition OneStruct : StructClass
-- := λ T, T

-- definition one {M : structure OneStruct} : carrier M
-- := data M

-- -- structures with mult and one

-- definition MonoidStruct : StructClass
-- := λ T, OneStruct T # MulStruct T

-- definition MonoidStruct_to_OneStruct (M : structure MonoidStruct) : (structure OneStruct)
-- := pair (carrier M) (proj1 (data M))

-- definition MonoidStruct_to_MulStruct (M : structure MonoidStruct) : (structure MulStruct)
-- := pair (carrier M) (proj2 (data M))

-- variable M : structure MonoidStruct
-- check carrier M = carrier (MonoidStruct_to_OneStruct M)

-- theorem test1 (M : structure MonoidStruct) : carrier M = carrier (MonoidStruct_to_OneStruct M)
-- := refl (carrier M)

-- definition is_mul_right_id (M : structure MonoidStruct) : Bool
-- := let m : carrier M → carrier M → carrier M := @mul (MonoidStruct_to_MulStruct M),
--        o : carrier M                            := @one (MonoidStruct_to_OneStruct M)
--    in ∀ x : carrier M, m x o = x

-- definition is_monoid (M : structure MonoidStruct) : Bool
-- := mul_is_assoc (MonoidStruct_to_MulStruct M) ∧ is_mul_right_id M

-- definition Monoid : AxClass
-- := pair MonoidStruct is_monoid

-- theorem monoid_is_mul_right_id (M : instance Monoid) : is_mul_right_id (struct M)
-- := and_elimr (proj2 M)

-- theorem monoid_mul_is_assoc (M : instance Monoid) : mul_is_assoc (MonoidStruct_to_MulStruct (struct M))
-- := and_eliml (proj2 M)
