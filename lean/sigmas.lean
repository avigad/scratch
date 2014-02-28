----------------------------------------------------------------------------------------------------
--
-- test_pairs.lean
-- Jeremy Avigad
--
-- experimenting with axiomatized pairs
--
----------------------------------------------------------------------------------------------------

import macros

universe U ≥ 2

-- the "right" equality axioms

axiom subst' {A : (Type U)} {a b : A} {P : A → (Type 1)} (H1 : P a) (H2 : a = b) : P b
axiom subst_id {A : (Type U)} {a : A} {P : A → (Type 1)} (H1 : P a) (e : a = a) : subst' H1 e = H1

-- theorem congr1' {A B : (Type U)} {f g : A → B} (H : f = g) (a : A) : f a = g a
-- := @subst' _ f g (fun h, f a = h a) (refl (f a)) H

-- theorem congr2' {A B : (Type U)} {a b : A} (f : A → B) (H : a = b) : f a = f b
-- := @subst' _ _ _ (fun x : A, f a = f x) (refl (f a)) H

-- casting
-- definition cast' {A B : Type} (e : A = B) (a : A) : B
-- := subst' a e

-- should be provable, using subst'
-- axiom cast_congr2 {A : Type} {B : A → Type} {a a' : A} (e : a = a') (b : B a)
--   : cast' (congr2' B e) b = subst' b e

-- also provable
-- axiom subst'_congr2 {A : Type} {B : A → Type} (f : ∀ x : A, B x) {a a' : A} (e : a = a')
--   : subst' (f a) e = f a'

-- pairs

variable Sigma {A : (Type 1)} (B : A → (Type 1)) : (Type 1)
variable Pair {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) : Sigma B
variable Fst {A : (Type 1)} {B : A → (Type 1)} (p : Sigma B) : A
variable Snd {A : (Type 1)} {B : A → (Type 1)} (p : Sigma B) : B (Fst p)
axiom FstAx {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) : @Fst A B (Pair a b) = a

axiom SndAx {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) : 
  (@Snd A B (Pair a b)) = @subst' A _ _ B b (symm (@FstAx A B a b))


theorem subst_pair {A : (Type 1)} {B : A → (Type 1)} {a a' : A} (e : a = a') (b : B a)
  : subst' (Pair a b) e = Pair a' (subst' b e)
:= 
  let P := fun x, ∀ e' : a = x, ∀ b : B a, subst' (Pair a b) e' = Pair x (subst' b e') in
  have H : P a, from
    take e' : a = a,
    take b : B a,
    have H1 : subst' b e' = b, from subst_id b e', 
    calc
      subst' (Pair a b) e' = Pair a b             : subst_id _ _
                       ... = Pair a (subst' b e') : { symm H1 },
  have H2 : P a', from subst' H e,
  H2 e b  

 
scope
-- Remark: A1 a1 A2 a2 A3 a3 A3 a4 are parameters for the definitions and theorems in this scope.
variable A1 : (Type 1)
variable a1 : A1
variable A2 : A1 → (Type 1)
variable a2 : A2 a1
variable A3 : ∀ a1 : A1, A2 a1 → (Type 1)
variable a3 : A3 a1 a2
variable A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1)
variable a4 : A4 a1 a2 a3

-- Pair type parameterized by a1 and a2
definition A1A2_tuple_ty (a1 : A1) (a2 : A2 a1) : (Type 1)
:= @Sigma (A3 a1 a2) (A4 a1 a2)
-- Pair a3 a4
definition tuple_34 : A1A2_tuple_ty a1 a2
:= @Pair (A3 a1 a2) (A4 a1 a2) a3 a4
-- Triple type parameterized by a1
definition A1_tuple_ty (a1 : A1) : (Type 1)
:= @Sigma (A2 a1) (A1A2_tuple_ty a1)
-- Triple a2 a3 a4
definition tuple_234 : A1_tuple_ty a1
:= @Pair (A2 a1) (A1A2_tuple_ty a1) a2 tuple_34
-- Quadruple type
definition tuple_ty : (Type 1)
:= @Sigma A1 A1_tuple_ty
-- Quadruple a1 a2 a3 a4
definition tuple_1234 : tuple_ty
:= @Pair A1 A1_tuple_ty a1 tuple_234

-- First element of the quadruple
definition f_1234 : A1
:= @Fst A1 A1_tuple_ty tuple_1234
-- Rest of the quadruple (i.e., a triple)
definition s_1234 : A1_tuple_ty f_1234
:= @Snd A1 A1_tuple_ty tuple_1234
-- theorem H_eq_a1 : f_1234 = a1
-- := @FstAx A1 A1_tuple_ty a1 tuple_234
definition H_eq_a1 : f_1234 = a1
:= @FstAx A1 A1_tuple_ty a1 tuple_234
-- theorem H_eq_triple : s_1234 == tuple_234
-- := @SndAx A1 A1_tuple_ty a1 tuple_234
definition H_eq_triple : s_1234 = @subst' A1 a1 f_1234 A1_tuple_ty tuple_234 (symm H_eq_a1)
:= @SndAx A1 A1_tuple_ty a1 tuple_234


--- left off here...

-- Second element of the quadruple
definition fs_1234 : A2 f_1234
:= @Fst (A2 f_1234) (A1A2_tuple_ty f_1234) s_1234
-- Rest of the triple (i.e., a pair)
definition ss_1234 : A1A2_tuple_ty f_1234 fs_1234
:= @Snd (A2 f_1234) (A1A2_tuple_ty f_1234) s_1234
theorem H_eq_a2 : fs_1234 == a2
:= have H1 : @Fst (A2 f_1234) (A1A2_tuple_ty f_1234) s_1234 == @Fst (A2 a1) (A1A2_tuple_ty a1) tuple_234,
     from hcongr (hcongr (hrefl (λ x, @Fst (A2 x) (A1A2_tuple_ty x))) (to_heq H_eq_a1)) H_eq_triple,
   have H2 : @Fst (A2 a1) (A1A2_tuple_ty a1) tuple_234 = a2,
     from FstAx _ _,
   htrans H1 (to_heq H2)
theorem H_eq_pair : ss_1234 == tuple_34
:= have H1 : @Snd (A2 f_1234) (A1A2_tuple_ty f_1234) s_1234 == @Snd (A2 a1) (A1A2_tuple_ty a1) tuple_234,
     from hcongr (hcongr (hrefl (λ x, @Snd (A2 x) (A1A2_tuple_ty x))) (to_heq H_eq_a1)) H_eq_triple,
   have H2 : @Snd (A2 a1) (A1A2_tuple_ty a1) tuple_234 == tuple_34,
     from SndAx _ _,
   htrans H1 H2
-- Third element of the quadruple
definition fss_1234 : A3 f_1234 fs_1234
:= @Fst (A3 f_1234 fs_1234) (A4 f_1234 fs_1234) ss_1234
-- Fourth element of the quadruple
definition sss_1234 : A4 f_1234 fs_1234 fss_1234
:= @Snd (A3 f_1234 fs_1234) (A4 f_1234 fs_1234) ss_1234
theorem H_eq_a3 : fss_1234 == a3
:= have H1 : @Fst (A3 f_1234 fs_1234) (A4 f_1234 fs_1234) ss_1234 == @Fst (A3 a1 a2) (A4 a1 a2) tuple_34,
     from hcongr (hcongr (hcongr (hrefl (λ x y z, @Fst (A3 x y) (A4 x y) z)) (to_heq H_eq_a1)) H_eq_a2) H_eq_pair,
   have H2 : @Fst (A3 a1 a2) (A4 a1 a2) tuple_34 = a3,
     from FstAx _ _,
   htrans H1 (to_heq H2)
theorem H_eq_a4 : sss_1234 == a4
:= have H1 : @Snd (A3 f_1234 fs_1234) (A4 f_1234 fs_1234) ss_1234 == @Snd (A3 a1 a2) (A4 a1 a2) tuple_34,
     from hcongr (hcongr (hcongr (hrefl (λ x y z, @Snd (A3 x y) (A4 x y) z)) (to_heq H_eq_a1)) H_eq_a2) H_eq_pair,
   have H2 : @Snd (A3 a1 a2) (A4 a1 a2) tuple_34 == a4,
     from SndAx _ _,
   htrans H1 H2

