----------------------------------------------------------------------------------------------------
--
-- test_algebra2.lean
-- Jeremy Avigad
--
-- Trying to handle the algebraic hierarchy, with explicit casts.
--
----------------------------------------------------------------------------------------------------

import macros

-- simulate the "real" version of cast
-- note that this will ensure that we are only using casts on small types
definition cast' {A B : Type} (e : A = B) := cast (to_heq e)

--
-- Classes of structures, and axiomatic classes of structures
--

-- A "structure" consists of a carrier, and some data (whose type depends on the carrier)

definition StructClass : (Type 1) := Type → Type   -- the type of the data

definition structure (S : StructClass) : (Type 1)
:= sig T : Type, S T

definition mk_structure {S : StructClass} {T : Type} (d : S T) : structure S 
:= pair T d

definition carrier {S : StructClass} (M : structure S) : Type
:= proj1 M

definition data {S : StructClass} (M : structure S) : S (carrier M)
:= proj2 M

set_opaque structure true
set_opaque mk_structure true
set_opaque carrier true
set_opaque data true

-- An "axiomatic class" is a class of structures satisfying some predicate (the "axioms")

definition AxClass : (Type 1)
:= sig S : StructClass, structure S → Bool

definition mk_AxClass (S : StructClass) (P : structure S → Bool)
:= pair S P

-- Coercion from AxClass to StructClass
definition struct_class (C : AxClass) : StructClass
:= proj1 C

definition axioms {C : AxClass} (M : structure (struct_class C))
:= proj2 C M

definition instance (C : AxClass) : (Type 1)
:= sig M : structure (struct_class C), axioms M

definition mk_instance (C : AxClass) (M : structure (struct_class C)) (H : axioms M)
:= pair M H

definition struct {C : AxClass} (M : instance C)
:= proj1 M

definition hyps {C : AxClass} (M : instance C) : axioms (struct M)
:= proj2 M

-- set_opaque AxClass true
set_opaque mk_AxClass true
-- set_opaque axioms true
-- set_opaque struct true
-- set_opaque hyps true
set_opaque instance true

--
-- Examples
--

-- multiplication (for overloading *)

definition MulStruct : StructClass
:= λ T, T → T → T

-- ultimately, the cast e should be inserted automatically
definition mul {S : StructClass} {M : structure S} {M' : structure MulStruct} 
  (e : carrier M = carrier M') (x : carrier M) (y : carrier M) : carrier M
:= 
  let m' := data M' in
  let x' := cast' e x in
  let y' := cast' e y in
    cast' (symm e) (m' x' y')

-- infixl 70 * : mul

-- The cast e signals that we are viewing M as the MulStruct M'.
definition mul_is_assoc {S : StructClass} {M : structure S} {M' : structure MulStruct} 
  (e : carrier M = carrier M') : Bool
:=  ∀ x y z : carrier M, mul e (mul e x y) z = mul e x (mul e y z)

-- once again, in practice, the fact that a multiplication is associative is a "hole"
-- that should be inferred automatically
theorem mul_assoc {S : StructClass} {M : structure S} {M' : structure MulStruct} 
    (e : carrier M = carrier M') (H : mul_is_assoc e) : 
  ∀ x y z : carrier M, mul e (mul e x y) z = mul e x (mul e y z)
:= H

definition mul_is_comm {S : StructClass} {M : structure S} {M' : structure MulStruct} 
  (e : carrier M = carrier M') : Bool
:= 
  ∀ x y z : carrier M, mul e x y = mul e y x

-- this is how you view a mulstruct as a mulstruct
theorem mulstruct_as_mulstruct (M : structure MulStruct) : carrier M = carrier M
:= refl _

set_opaque MulStruct true
set_opaque mul true
set_opaque mul_is_assoc true
set_opaque mul_is_comm true


-- semigroups

-- note: mk_AxClass doesn't work here, even though it is defined to be pair
definition Semigroup : AxClass
:= pair MulStruct (λ M, (mul_is_assoc (mulstruct_as_mulstruct M)))

-- this is how you view a semigroup as a mulstruct
theorem semigroup_as_mulstruct (M : instance Semigroup) : carrier (struct M) = carrier (struct M)
:= refl _

-- to fill the hole in mul_assoc

-- question: why do we have to make mul_is_assoc transparent here?
variable M : instance Semigroup
check hyps M -- axioms (struct M)
-- eval axioms M -- fails
eval @axioms Semigroup (struct M)
-- if I make struct opaque, I need to write
-- eval @axioms Semigroup (@struct Semigroup M)

set_opaque mul_is_assoc false

theorem semigroup_mul_is_assoc (M : instance Semigroup) : 
  mul_is_assoc (mulstruct_as_mulstruct (struct M))
:= hyps M

set_opaque mul_is_assoc true



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
