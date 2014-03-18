----------------------------------------------------------------------------------------------------
--
-- algebra.lean
-- Jeremy Avigad
--
-- Handling the algebraic hierarchy. Uses:
-- 
-- o unbundled type class encodings to overload constants and theorem names
-- o bundled records for structures
-- o instance declarations (unification hints) to relate the two
--
----------------------------------------------------------------------------------------------------

import macros
import tactic

-- simulate the "right" equality axioms

axiom subst' {A : (Type U)} {a b : A} {P : A → (Type 1)} (H1 : P a) (H2 : a = b) : P b
axiom subst'_heq {A : (Type U)} {a a' : A} {B : A → (Type 1)} (b : B a) (e : a = a') :
  subst' b e == b

theorem eq_subst'_to_heq {A : (Type U)} {a a' : A} {B : A → (Type 1)} {b : B a} {e : a = a'} 
  {b' : B a'} (e2: b' = subst' b e) : b' == b 
:= htrans (to_heq e2) (subst'_heq b e)


-- useful abbreviations

definition is_assoc {T : Type} (op : T → T → T) := ∀ x y z, op (op x y) z = op x (op y z)
definition is_comm {T : Type} (op : T → T → T) := ∀ x y, op x y = op y x
definition is_right_id {T : Type} (op : T → T → T) (e : T) := ∀ x, op x e = x
definition is_left_id {T : Type} (op : T → T → T) (e : T) := ∀ x, op e x = x
definition is_right_inv {T : Type} (op : T → T → T) (i : T → T) (e : T) := ∀ x, op x (i x) = e
definition is_left_inv {T : Type} (op : T → T → T) (i : T → T) (e : T) := ∀ x, op (i x) x = e


--
-- Type classes: overloaded constants
-- 

-- mul

definition has_mul (T : Type) (m : T → T → T) := true
definition mk_mul_instance (T : Type) (m : T → T → T) : has_mul T m := trivial
definition mul {T : Type} {m : T → T → T} {instance : has_mul T m} : T → T → T
:= m
theorem mul_def {T : Type} {m : T → T → T} (instance : has_mul T m) : @mul T m instance = m 
:= refl _

set_opaque has_mul true
set_opaque mk_mul_instance true
set_opaque mul true

-- an abbreviation with the third argument explicit
definition mul_of {T : Type} {m : T → T → T} (instance : has_mul T m) : T → T → T
:= @mul T m instance

-- one

definition has_one (T : Type) (o : T) := true
definition mk_one_instance (T : Type) (o : T) : has_one T o := trivial
definition one {T : Type} {o : T} {instance : has_one T o} : T
:= o
theorem one_def {T : Type} {o : T} (instance : has_one T o) : @one T o instance = o 
:= refl _

set_opaque has_one true
set_opaque mk_one_instance true
set_opaque one true

definition one_of {T : Type} {o : T} (instance : has_one T o) : T
:= @one T o instance

-- inv

definition has_inv (T : Type) (i : T → T) := true
definition mk_inv_instance (T : Type) (i : T → T) : has_inv T i := trivial
definition inv {T : Type} {i : T → T} {instance : has_inv T i} : T → T
:= i
theorem inv_def {T : Type} {i : T → T} (instance : has_inv T i) : @inv T i instance = i 
:= refl _

set_opaque has_inv true
set_opaque mk_inv_instance true
set_opaque inv true

definition inv_of {T : Type} {i : T → T} (instance : has_inv T i) : T → T
:= @inv T i instance


--
-- Type classes: overloaded theorem names
-- 

-- mul_assoc

definition is_mul_assoc {T : Type} (m : T → T → T) := is_assoc m
definition mk_mul_assoc_instance {T : Type} {m : T → T → T} (H : is_assoc m) : is_mul_assoc m
:= H
theorem assoc_of_mul_assoc {T : Type} {m : T → T → T} (H : is_mul_assoc m) : is_assoc m
:= H
theorem mul_assoc {T : Type} {m : T → T → T} {mul_inst : has_mul T m} 
  {assoc_inst : is_mul_assoc m} : is_assoc (mul_of mul_inst) 
:= subst assoc_inst (symm (mul_def mul_inst))

set_opaque is_mul_assoc true
set_opaque mk_mul_assoc_instance true


-- mul_comm

definition is_mul_comm {T : Type} (m : T → T → T) := is_comm m
definition mk_mul_comm_instance {T : Type} {m : T → T → T} (H : is_comm m) : is_mul_comm m
:= H
theorem comm_of_mul_comm {T : Type} {m : T → T → T} (H : is_mul_comm m) : is_comm m
:= H
theorem mul_comm {T : Type} {m : T → T → T} {mul_inst : has_mul T m} 
  {comm_inst : is_mul_comm m} : is_comm (mul_of mul_inst) 
:= subst comm_inst (symm (mul_def mul_inst))

set_opaque is_mul_comm true
set_opaque mk_mul_comm_instance true

-- mul_right_id

definition is_mul_right_id {T : Type} (m : T → T → T) (o : T) := is_right_id m o
definition mk_mul_right_id_instance {T : Type} {m : T → T → T} {o : T} (H : is_right_id m o)
  : is_mul_right_id m o 
:= H
theorem right_id_of_mul_right_id {T : Type} {m : T → T → T} {o : T} (H : is_mul_right_id m o)
  : is_right_id m o 
:= H
theorem mul_right_id {T : Type} {m : T → T → T} {o : T} {mul_inst : has_mul T m} 
  {one_inst : has_one T o} {right_id_inst : is_mul_right_id m o} : 
  is_right_id (mul_of mul_inst) (one_of one_inst)
:= subst (subst right_id_inst (symm (mul_def mul_inst))) (symm (one_def one_inst))

set_opaque is_mul_right_id true
set_opaque mk_mul_right_id_instance true

-- mul_left_id

definition is_mul_left_id {T : Type} (m : T → T → T) (o : T) := is_left_id m o
definition mk_mul_left_id_instance {T : Type} {m : T → T → T} {o : T} (H : is_left_id m o) 
  : is_mul_left_id m o
:= H
theorem left_id_of_mul_left_id {T : Type} {m : T → T → T} {o : T} (H : is_mul_left_id m o)
  : is_left_id m o 
:= H
theorem mul_left_id {T : Type} {m : T → T → T} {o : T} {mul_inst : has_mul T m} 
  {one_inst : has_one T o} {left_id_inst : is_mul_left_id m o} : 
  is_left_id (mul_of mul_inst) (one_of one_inst)
:= subst (subst left_id_inst (symm (mul_def mul_inst))) (symm (one_def one_inst))

set_opaque is_mul_left_id true
set_opaque mk_mul_left_id_instance true

-- mul_right_inv

definition is_mul_right_inv {T : Type} (m : T → T → T) (i : T → T) (o : T) := is_right_inv m i o
definition mk_mul_right_inv_instance {T : Type} {m : T → T → T} {i : T → T} {o : T} 
    (H : is_right_inv m i o) 
  : is_mul_right_inv m i o
:= H
theorem right_inv_of_mul_right_inv {T : Type} {m : T → T → T} {i : T → T} {o : T} 
   (H : is_mul_right_inv m i o)
  : is_right_inv m i o
:= H
theorem mul_right_inv {T : Type} {m : T → T → T} {i : T → T} {o : T} {mul_inst : has_mul T m} 
  {inv_inst : has_inv T i} {one_inst : has_one T o} {right_inv_inst : is_mul_right_inv m i o} : 
  is_right_inv (mul_of mul_inst) (inv_of inv_inst) (one_of one_inst)
:= subst (subst (subst right_inv_inst (symm (mul_def mul_inst))) (symm (inv_def inv_inst))) 
     (symm (one_def one_inst))

set_opaque is_mul_right_inv true
set_opaque mk_mul_right_inv_instance true

-- mul_left_inv

definition is_mul_left_inv {T : Type} (m : T → T → T) (i : T → T) (o : T) := is_left_inv m i o
definition mk_mul_left_inv_instance {T : Type} {m : T → T → T} {i : T → T} {o : T} 
    (H : is_left_inv m i o)
  : is_mul_left_inv m i o 
:= H
theorem left_inv_of_mul_left_inv {T : Type} {m : T → T → T} {i : T → T} {o : T} 
   (H : is_mul_left_inv m i o)
  : is_left_inv m i o
:= H
theorem mul_left_inv {T : Type} {m : T → T → T} {i : T → T} {o : T} {mul_inst : has_mul T m} 
  {inv_inst : has_inv T i} {one_inst : has_one T o} {left_inv_inst : is_mul_left_inv m i o} : 
  is_left_inv (mul_of mul_inst) (inv_of inv_inst) (one_of one_inst)
:= subst (subst (subst left_inv_inst (symm (mul_def mul_inst))) (symm (inv_def inv_inst))) 
     (symm (one_def one_inst))

set_opaque is_mul_left_inv true
set_opaque mk_mul_left_inv_instance true


--
-- Semigroup Structure
--

-- semigroup record

variable Semigroup : (Type 1)
variable mk_Semigroup (T : Type) (m : T → T → T) (H : is_assoc m) : Semigroup
variable Semigroup_rec (P : Semigroup → (Type 1)) : 
  (∀ T : Type, ∀ m : T → T → T, ∀ H : is_assoc m, P (mk_Semigroup T m H)) →
    ∀ S : Semigroup, P S
axiom Semigroup_comp (P : Semigroup → (Type 1)) 
  (f : ∀ T : Type, ∀ m : T → T → T, ∀ H : is_assoc m, P (mk_Semigroup T m H))
    (T : Type) (m : T → T → T) (H : is_assoc m) :
  Semigroup_rec P f (mk_Semigroup T m H) = f T m H

definition Semigroup_carrier : Semigroup → Type
:= Semigroup_rec (λ S, Type) (λ T : Type, λ m : T → T → T, λ H : is_assoc m, T)
theorem Semigroup_carrier_eq : ∀ T : Type, ∀ m H, Semigroup_carrier (mk_Semigroup T m H) = T
:= Semigroup_comp (λ S, Type) (λ T : Type, λ m : T → T → T, λ H : is_assoc m, T)

definition Semigroup_mul : ∀ S : Semigroup, Semigroup_carrier S → Semigroup_carrier S → 
  Semigroup_carrier S
:= 
  let P := λ S, Semigroup_carrier S → Semigroup_carrier S → Semigroup_carrier S in
  let f := λ T : Type,  λ m : T → T → T, λ H : is_assoc m, 
      (subst' m (symm (Semigroup_carrier_eq T m H))) in
    Semigroup_rec P f   -- without specifying P, elaborator freezes 
theorem Semigroup_mul_eq' : ∀ T m H, Semigroup_mul (mk_Semigroup T m H) =
  subst' m (symm (Semigroup_carrier_eq T m H))
:= Semigroup_comp _ _
theorem Semigroup_mul_eq : ∀ T m H, Semigroup_mul (mk_Semigroup T m H) == m
:= λ T : Type, λ m H, eq_subst'_to_heq (Semigroup_mul_eq' T m H)

-- This can be defined by the recursor as above, but now we need two casts.
-- For now, I am lazy.
axiom Semigroup_mul_assoc :  ∀ S : Semigroup, is_assoc (Semigroup_mul S)

-- We can replace "Bool" by "(Type 1)" here and in the next lemma, for new recursion
-- principles. But is that useful?
theorem Semigroup_bundle' (P : ∀ T : Type, ∀ m : T → T → T, Bool) :
  (∀ T m, is_assoc m → P T m) → (∀ S : Semigroup, P (Semigroup_carrier S) (Semigroup_mul S))
:= take f S, f (Semigroup_carrier S) (Semigroup_mul S) (Semigroup_mul_assoc S) 

theorem Semigroup_unbundle' (P : ∀ T : Type, ∀ m : T → T → T, Bool) :
  (∀ S : Semigroup, P (Semigroup_carrier S) (Semigroup_mul S)) → (∀ T m, is_assoc m → P T m)
:= 
  take f T m, assume H : is_assoc m,
  let S := mk_Semigroup T m H in
  have e1 : Semigroup_carrier S == T, from to_heq (Semigroup_carrier_eq _ _ _),
  have e2 : Semigroup_mul S == m, from Semigroup_mul_eq _ _ _,
  have e3 : P (Semigroup_carrier S) == P T, from hcongr (hrefl _) e1,
  -- note: simp doesn't work here, nor does plugging in the definition of e3
  have e4 : P (Semigroup_carrier S) (Semigroup_mul S) == P T m, from hcongr e3 e2,
  cast e4 (f S)

set_opaque Semigroup_carrier true
set_opaque Semigroup_mul true


-- type class instantiations

definition mul_of_Semigroup (S : Semigroup)
:= mk_mul_instance (Semigroup_carrier S) (Semigroup_mul S)
definition Semigroup_is_mul_assoc (S : Semigroup)
:= mk_mul_assoc_instance (Semigroup_mul_assoc S)
theorem mul_of_Semigroup_eq (S : Semigroup) : mul_of (mul_of_Semigroup S) = Semigroup_mul S
:= mul_def _

-- now bundle and unbundle with type class version of "mul"
theorem Semigroup_bundle (P : ∀ T : Type, ∀ m : T → T → T, Bool) :
  (∀ T m, is_assoc m → P T m) → 
    (∀ S : Semigroup, P (Semigroup_carrier S) (mul_of (mul_of_Semigroup S)))
:= take f S, subst' (Semigroup_bundle' P f S) (symm (mul_of_Semigroup_eq S))

theorem Semigroup_unbundle (P : ∀ T : Type, ∀ m : T → T → T, Bool) :
  (∀ S : Semigroup, P (Semigroup_carrier S) (mul_of (mul_of_Semigroup S))) →
    (∀ T m, is_assoc m → P T m)
:= take f, let f' := λ S, subst' (f S) (mul_of_Semigroup_eq S) in Semigroup_unbundle' P f'

-- converts theorems to type class versions
theorem Semigroup_unbundled_to_type_class 
  (P : ∀ T : Type, ∀ m : T → T → T, Bool) (f : ∀ T m, is_assoc m → P T m) 
  {T : Type} {m : T → T → T} {mul_inst : has_mul T m} {assoc_inst : is_mul_assoc m} : P T m
:= f T m (assoc_of_mul_assoc assoc_inst)

-- after synthesizing this term from P and f, the last four arguments should be made implicit
theorem Semigroup_bundled_to_type_class 
  (P : ∀ T : Type, ∀ m : T → T → T, Bool) 
    (f : ∀ S : Semigroup, P (Semigroup_carrier S) (mul_of (mul_of_Semigroup S)))
  (T : Type) (m : T → T → T) (mul_inst : has_mul T m) (assoc_inst : is_mul_assoc m) : P T m
:= Semigroup_unbundle P f T m (assoc_of_mul_assoc assoc_inst)


set_opaque mul_of_Semigroup true
set_opaque Semigroup_is_mul_assoc true

print "Unification hints:"
check mul_of_Semigroup
check Semigroup_is_mul_assoc

-- In this example, the implicit arguments given explicitly in the definitions of  mul' and 
-- mul_assoc' would be inferred using the unification hints mul_of_Semigroup and 
-- Semigroup_is_mul_assoc, using the fact that the arguments have type Semigroup_carrier S.

theorem example1: ∀ S : Semigroup, ∀ x y z w : Semigroup_carrier S,
  let mul' := @mul _ _ (mul_of_Semigroup S) in
  mul' (mul' (mul' x y) z) w = mul' x (mul' y (mul' z w))
:=
  take S : Semigroup,
  take x y z w  : Semigroup_carrier S,
  let mul' := @mul _ _ (mul_of_Semigroup S) in
  let mul_assoc' := @mul_assoc _ _ (mul_of_Semigroup S) (Semigroup_is_mul_assoc S) in
  calc
    mul' (mul' (mul' x y) z) w = mul' (mul' x y) (mul' z w) : { mul_assoc' _ _ _}
                           ... = mul' x (mul' y (mul' z w)) : { mul_assoc' _ _ _}

definition example1_body (T : Type) (m : T → T → T) := ∀ x y z w : T, 
  m (m (m x y) z) w = m x (m y (m z w))

definition type_of {T : Type} (t : T) := T

print ""
print "*** Example 1: ***"
print ""

check example1
print ""
eval type_of example1
print ""

definition example1_unbundled := Semigroup_unbundle example1_body example1
check example1_unbundled
print ""
eval type_of example1_unbundled
print ""

definition example1_as_type_class := Semigroup_bundled_to_type_class example1_body example1
check example1_as_type_class
print ""
eval type_of example1_as_type_class
print ""

definition example1_rebundled := Semigroup_bundle example1_body example1_unbundled
check example1_rebundled
print ""
eval type_of example1_rebundled
print ""

definition example1_rebundled_as_record := Semigroup_bundle' example1_body example1_unbundled
check example1_rebundled_as_record
print ""
eval type_of example1_rebundled_as_record
print ""

--
-- Monoid Structure
--

-- monoid record

definition is_monoid {T : Type} (m : T → T → T) (o : T) := 
  is_assoc m ∧ is_right_id m o ∧ is_left_id m o

variable Monoid : (Type 1)
variable mk_Monoid (T : Type) (m : T → T → T) (o : T) (H : is_monoid m o) : Monoid
variable Monoid_carrier : Monoid → Type
variable Monoid_mul : ∀ S : Monoid, Monoid_carrier S → Monoid_carrier S → Monoid_carrier S
variable Monoid_one : ∀ S : Monoid, Monoid_carrier S
variable Monoid_is_monoid :  ∀ S : Monoid, is_monoid (Monoid_mul S) (Monoid_one S)

axiom Monoid_carrier_eq : ∀ T m o H, Monoid_carrier (mk_Monoid T m o H) = T
axiom Monoid_mul_eq : ∀ T m o H, Monoid_mul (mk_Monoid T m o H) == m
axiom Monoid_one_eq : ∀ T m o H, Monoid_one (mk_Monoid T m o H) == o


-- type class instantiations

definition mul_of_Monoid (S : Monoid)
:= mk_mul_instance (Monoid_carrier S) (Monoid_mul S)
definition one_of_Monoid (S : Monoid)
:= mk_one_instance (Monoid_carrier S) (Monoid_one S)
definition Monoid_is_mul_assoc (S : Monoid)
:= mk_mul_assoc_instance (and_eliml (Monoid_is_monoid S))
definition Monoid_is_right_id (S : Monoid)
:= mk_mul_right_id_instance (and_eliml (and_elimr (Monoid_is_monoid S)))
definition Monoid_is_left_id (S : Monoid)
:= mk_mul_left_id_instance (and_elimr (and_elimr (Monoid_is_monoid S)))

set_opaque mul_of_Monoid true
set_opaque one_of_Monoid true
set_opaque Monoid_is_mul_assoc true
set_opaque Monoid_is_right_id true
set_opaque Monoid_is_left_id true

print "Unification hints:"
check mul_of_Monoid
check one_of_Monoid
check Monoid_is_mul_assoc
check Monoid_is_right_id
check Monoid_is_left_id

-- This is the same example as before, except that a different mul and mul_assoc are inferred

theorem example2: ∀ S : Monoid, ∀ x y z w : Monoid_carrier S,
  let mul' := @mul _ _ (mul_of_Monoid S) in
  mul' (mul' (mul' x y) z) w = mul' x (mul' y (mul' z w))
:=
  take S : Monoid,
  take x y z w  : Monoid_carrier S,
  let mul' := @mul _ _ (mul_of_Monoid S) in
  let mul_assoc' := @mul_assoc _ _ (mul_of_Monoid S) (Monoid_is_mul_assoc S) in
  calc
    mul' (mul' (mul' x y) z) w = mul' (mul' x y) (mul' z w) : { mul_assoc' _ _ _}
                           ... = mul' x (mul' y (mul' z w)) : { mul_assoc' _ _ _}

-- here is another example

theorem example3: ∀ S : Monoid, ∀ x y : Monoid_carrier S,
  let mul' := @mul _ _ (mul_of_Monoid S) in
  let one' := @one _ _ (one_of_Monoid S) in
  mul' (mul' x y) one' = mul' x y
:= take S x y, @mul_right_id _ _ _ (mul_of_Monoid S) (one_of_Monoid S) (Monoid_is_right_id S) _

