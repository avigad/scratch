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


--
-- Type classes: overloaded theorem names
-- 

-- mul_assoc

definition is_mul_assoc {T : Type} (m : T → T → T) := is_assoc m
definition mk_mul_assoc_instance {T : Type} {m : T → T → T} (H : is_assoc m) : is_mul_assoc m
:= H
theorem mul_assoc {T : Type} {m : T → T → T} {mul_inst : has_mul T m} 
  {assoc_inst : is_mul_assoc m} : is_assoc (@mul _ _ mul_inst) 
:= subst assoc_inst (symm (mul_def mul_inst))

set_opaque is_mul_assoc true
set_opaque mk_mul_assoc_instance true

-- mul_comm

definition is_mul_comm {T : Type} (m : T → T → T) := is_comm m
definition mk_mul_comm_instance {T : Type} {m : T → T → T} (H : is_comm m) : is_mul_comm m
:= H
theorem mul_comm {T : Type} {m : T → T → T} {mul_inst : has_mul T m} 
  {comm_inst : is_mul_comm m} : is_comm (@mul _ _ mul_inst) 
:= subst comm_inst (symm (mul_def mul_inst))

set_opaque is_mul_comm true
set_opaque mk_mul_comm_instance true

-- mul_right_id

definition is_mul_right_id {T : Type} (m : T → T → T) (o : T) := is_right_id m o
definition mk_mul_right_id_instance {T : Type} {m : T → T → T} {o : T} (H : is_right_id m o)
  : is_mul_right_id m o 
:= H
theorem mul_right_id {T : Type} {m : T → T → T} {o : T} {mul_inst : has_mul T m} 
  {one_inst : has_one T o} {right_id_inst : is_mul_right_id m o} : 
  is_right_id (@mul _ _ mul_inst) (@one _ _ one_inst)
:= subst (subst right_id_inst (symm (mul_def mul_inst))) (symm (one_def one_inst))

set_opaque is_mul_right_id true
set_opaque mk_mul_right_id_instance true

-- mul_left_id

definition is_mul_left_id {T : Type} (m : T → T → T) (o : T) := is_left_id m o
definition mk_mul_left_id_instance {T : Type} {m : T → T → T} {o : T} (H : is_left_id m o) 
  : is_mul_left_id m o
:= H
theorem mul_left_id {T : Type} {m : T → T → T} {o : T} {mul_inst : has_mul T m} 
  {one_inst : has_one T o} {left_id_inst : is_mul_left_id m o} : 
  is_left_id (@mul _ _ mul_inst) (@one _ _ one_inst)
:= subst (subst left_id_inst (symm (mul_def mul_inst))) (symm (one_def one_inst))

set_opaque is_mul_left_id true
set_opaque mk_mul_left_id_instance true

-- mul_right_inv

definition is_mul_right_inv {T : Type} (m : T → T → T) (i : T → T) (o : T) := is_right_inv m i o
definition mk_mul_right_inv_instance {T : Type} {m : T → T → T} {i : T → T} {o : T} 
  (H : is_right_inv m i o) 
:= H
theorem mul_right_inv {T : Type} {m : T → T → T} {i : T → T} {o : T} {mul_inst : has_mul T m} 
  {inv_inst : has_inv T i} {one_inst : has_one T o} {right_inv_inst : is_mul_right_inv m i o} : 
  is_right_inv (@mul _ _ mul_inst) (@inv _ _ inv_inst) (@one _ _ one_inst)
:= subst (subst (subst right_inv_inst (symm (mul_def mul_inst))) (symm (inv_def inv_inst))) 
     (symm (one_def one_inst))

set_opaque is_mul_right_inv true
set_opaque mk_mul_right_inv_instance true

-- mul_left_inv

definition is_mul_left_inv {T : Type} (m : T → T → T) (i : T → T) (o : T) := is_left_inv m i o
definition mk_mul_left_inv_instance {T : Type} {m : T → T → T} {i : T → T} {o : T} 
  (H : is_left_inv m i o) 
:= H
theorem mul_left_inv {T : Type} {m : T → T → T} {i : T → T} {o : T} {mul_inst : has_mul T m} 
  {inv_inst : has_inv T i} {one_inst : has_one T o} {left_inv_inst : is_mul_left_inv m i o} : 
  is_left_inv (@mul _ _ mul_inst) (@inv _ _ inv_inst) (@one _ _ one_inst)
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
variable Semigroup_carrier : Semigroup → Type
variable Semigroup_mul : ∀ S : Semigroup, Semigroup_carrier S → Semigroup_carrier S → 
  Semigroup_carrier S
variable Semigroup_mul_assoc :  ∀ S : Semigroup, is_assoc (Semigroup_mul S)

axiom Semigroup_carrier_eq : ∀ T m H, Semigroup_carrier (mk_Semigroup T m H) = T
axiom Semigroup_mul_eq : ∀ T m H, Semigroup_mul (mk_Semigroup T m H) == m

-- type class instantiations

definition mul_of_Semigroup (S : Semigroup)
:= mk_mul_instance (Semigroup_carrier S) (Semigroup_mul S)
definition Semigroup_is_mul_assoc (S : Semigroup)
:= mk_mul_assoc_instance (Semigroup_mul_assoc S)

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

