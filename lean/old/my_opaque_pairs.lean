import macros tactic

universe U ≥ 2 -- needed to state Sigma_inj below

-- the "right" equality axioms

axiom subst' {A : (Type U)} {a b : A} {P : A → (Type 1)} (H1 : P a) (H2 : a = b) : P b
-- not needed here
-- axiom subst_id {A : (Type U)} {a : A} {P : A → (Type 1)} (H1 : P a) (e : a = a) : subst' H1 e = H1
-- definition cast' {A B : Type} (e : A = B) (a : A) : B
-- := subst' a e
-- the current definition
-- definition cast' {A B : Type} (e : A = B) : A → B
-- := cast (to_heq e)

-- this will easily be provable with the right definition of ==
axiom subst'_heq {A : (Type U)} {a b : A} {P : A → (Type 1)} (H1 : P a) (H2 : a = b) :
  subst' H1 H2 == H1


--
-- Sigma types
--

variable Sigma {A : (Type 1)} (B : A → (Type 1)) : (Type 1)

variable Pair {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) : Sigma B

axiom sigma_rec {A : (Type 1)} {B : A → (Type 1)} {P : Sigma B → (Type 1)} :
  (∀ a : A, ∀ b : B a, P (@Pair A B a b)) → ∀ p : Sigma B, P p

axiom sigma_comp {A : (Type 1)} {B : A → (Type 1)} {P : Sigma B → (Type 1)}
    (f : (∀ a : A, ∀ b : B a, P (@Pair A B a b))) (a : A) (b : B a) :
  @sigma_rec A B P f (Pair a b) = f a b


definition Fst {A : (Type 1)} {B : A → (Type 1)} : ∀ p : Sigma B, A :=
  @sigma_rec A B (λ p, A) (λ a : A, λ b : B a, a)

theorem FstAx {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) : @Fst A B (Pair a b) = a
:= sigma_comp _ _ _

definition Snd {A : (Type 1)} {B : A → (Type 1)} : ∀ p : Sigma B, B (Fst p)
:=
  let P := λ p, B (Fst p) in
  let f := λ a : A, λ b : B a, subst' b (symm (@FstAx A B a b)) in
  @sigma_rec A B P f

theorem SndAx_subst {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) : 
    @Snd A B (Pair a b) = subst' b (symm (@FstAx A B a b))
:= sigma_comp _ _ _

theorem SndAx {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) : @Snd A B (Pair a b) == b
:= htrans (to_heq (@SndAx_subst A B a b)) (subst'_heq _ _)

set_opaque Fst true
set_opaque Snd true

axiom Sigma_inj {A : (Type 1)} {B : A → (Type 1)} {B' : A → (Type 1)} : Sigma B = Sigma B' → B = B'


--
-- Properties of Sigma types
-- 

theorem Fst_heq {A : (Type 1)} {B : A → (Type 1)} {B' : A → (Type 1)} {p : Sigma B} {p' : Sigma B'} :
  p == p' → Fst p == Fst p'
:=
  assume e : p == p',
  have H : B = B', from Sigma_inj (to_eq (type_eq e)),
  let P := λ T : A → (Type 1), ∀ q : Sigma T, p == q → Fst p == Fst q in
  have H1 : P B, from
    take q : Sigma B, assume e : p == q, (subst (hrefl (Fst p)) (to_eq e)), 
  substp P H1 H p' e

theorem Fst_heq' {A : (Type 1)} {A' : (Type 1)} (e : A = A') {B : A → (Type 1)} 
  {B' : A' → (Type 1)} {p : Sigma B} {p' : Sigma B'} :
    p == p' → Fst p == Fst p'
:= 
  take he,
  let H1 := substp (λ	X, ∀ B : A → (Type 1), ∀ B' : X → (Type 1), 
    ∀ p : Sigma B, ∀ p' : Sigma B', p == p' → Fst p == Fst p') (@Fst_heq A) e in
  H1 B B' p p' he

theorem Snd_heq {A : (Type 1)} {B : A → (Type 1)} {B' : A → (Type 1)} {p : Sigma B} {p' : Sigma B'} :
  p == p' → Snd p == Snd p'
:=
  assume e : p == p',
  have H : B = B', from Sigma_inj (to_eq (type_eq e)),
  let P := λ T : A → (Type 1), ∀ q : Sigma T, p == q → Snd p == Snd q in
  have H1 : P B, from
    take q : Sigma B, assume e : p == q, (subst (hrefl (Snd p)) (to_eq e)), 
  substp P H1 H p' e

theorem Snd_heq' {A : (Type 1)} {A' : (Type 1)} (e : A = A') {B : A → (Type 1)} 
  {B' : A' → (Type 1)} {p : Sigma B} {p' : Sigma B'} :
  p == p' → Snd p == Snd p'
:=
  take he,
  let H1 := substp (λ	X, ∀ B : A → (Type 1), ∀ B' : X → (Type 1), 
    ∀ p : Sigma B, ∀ p' : Sigma B', p == p' → Snd p == Snd p') (@Snd_heq A) e in
  H1 B B' p p' he


-- interesting: after the proof was done, I found I could remove most of the implicit arguments
theorem pair_eta {A : (Type 1)} (B : A → (Type 1)) (p : Sigma B) : p = Pair (Fst p) (Snd p)
:= 
  let P := λ p, p = Pair (Fst p) (Snd p) in
  have H : ∀ a : A, ∀ b : B a, P (Pair a b), from
    take a : A, 
    take b : B a,
    have H1 : Pair a == Pair (Fst (Pair a b)), 
      from hcongr (hrefl _) (to_heq (symm (@FstAx A B a b))),
    have H2 : Pair a b == Pair (Fst (Pair a b)) (@Snd A B (Pair a b)),
      from hcongr H1 (hsymm (SndAx a b)),
    show Pair a b = Pair (Fst (Pair a b)) (Snd (Pair a b)), from to_eq H2,
  sigma_rec H p

check @pair_eta

-- Conjectures
-- At least they all type check...
--

-- theorem eq_pair {A : (Type 1)} {B : A → (Type 1)} (p : Sigma B) (a : A) (b : B a)
--     (e1 : Fst p = a) (e2 : Snd p == b) : p = Pair a b
-- := 
--   _

-- theorem pair_inj2 {A : (Type 1)} {B : A → (Type 1)} (a : A) (b : B a) (b' : B a)
--   (H : Pair a b = Pair a b') : b == b'
-- := 
--   _ 

-- theorem eq_pair_iff {A : (Type 1)} {B : A → (Type 1)} {A' : (Type 1)} {B' : A' → (Type 1)} (p : Sigma B)
--   (p' : Sigma B') : (p == p') ↔ (Fst p == Fst p' ∧ Snd p == Snd p')
-- := 
--   _


--
-- Triples
-- 

definition Sigma2 {A1 : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) : (Type 1)
  := @Sigma A1 (λ a1 : A1, @Sigma (A2 a1) (A3 a1))

definition Triple {A1 : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) 
  (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) : @Sigma2 A1 A2 A3 
:= @Pair A1 (λ x, @Sigma (A2 x) (A3 x)) a1 (@Pair (A2 a1) (A3 a1) a2 a3)

definition pr31 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
  (p : @Sigma2 A1 A2 A3) : A1 
:= Fst p 

definition pr32 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
  (p : @Sigma2 A1 A2 A3) : A2 (pr31 p)
:= Fst (Snd p)

definition pr33 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
  (p : @Sigma2 A1 A2 A3) : A3 (pr31 p) (pr32 p)
:= Snd (Snd p)

theorem pr31_Triple_eq {A1 : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) 
    (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) :
  pr31 (@Triple A1 A2 A3 a1 a2 a3) = a1
:= FstAx _ _

theorem pr32_Triple_eq {A1 : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) 
    (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) :
  pr32 (@Triple A1 A2 A3 a1 a2 a3) == a2
:=
  have H : Snd (Triple A3 a1 a2 a3) == Pair a2 a3, from SndAx _ _,
  have H1 : A2 (Fst (Triple A3 a1 a2 a3)) = A2 a1, from congr2 _ (pr31_Triple_eq _ _ _ _),
  have H2 : pr32 (Triple A3 a1 a2 a3) == Fst (Pair a2 a3), from Fst_heq' H1 H,
  have H3 : Fst (Pair a2 a3) == a2, from to_heq (FstAx _ _),
  htrans H2 H3

theorem pr33_Triple_eq {A1 : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) 
    (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) :
  pr33 (@Triple A1 A2 A3 a1 a2 a3) == a3
:=
  have H : Snd (Triple A3 a1 a2 a3) == Pair a2 a3, from SndAx _ _,
  have H1 : A2 (Fst (Triple A3 a1 a2 a3)) = A2 a1, from congr2 _ (pr31_Triple_eq _ _ _ _),
  have H2 : pr33 (Triple A3 a1 a2 a3) == Snd (Pair a2 a3), from Snd_heq' H1 H,
  have H3 : Snd (Pair a2 a3) == a3, from SndAx _ _,
  htrans H2 H3

theorem pr31_heq {A1 A1' : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) 
    {A2' : A1' → (Type 1)} (A3' : ∀ a1 : A1', A2' a1 → (Type 1)) 
    {p : @Sigma2 A1 A2 A3} {p' : @Sigma2 A1' A2' A3'} (e : A1 = A1')
  : p == p' → pr31 p == pr31 p'
:= Fst_heq' e

theorem pr32_heq {A1 A1' : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) 
    {A2' : A1' → (Type 1)} (A3' : ∀ a1 : A1', A2' a1 → (Type 1)) 
    {p : @Sigma2 A1 A2 A3} {p' : @Sigma2 A1' A2' A3'} (e1 : A1 = A1') (e2 : A2 == A2')
  : p == p' → pr32 p == pr32 p'
:= 
  assume e : p == p',
  have H1 : Fst p == Fst p', from Fst_heq' e1 e,
  have H2 : Snd p == Snd p', from Snd_heq' e1 e,
  have H3 : A2 (Fst p) == A2' (Fst p'), from hcongr e2 H1,
  let e3 := to_eq H3 in
  show pr32 p == pr32 p', from Fst_heq' e3 H2

theorem pr33_heq {A1 A1' : (Type 1)} {A2 : A1 → (Type 1)} (A3 : ∀ a1 : A1, A2 a1 → (Type 1)) 
    {A2' : A1' → (Type 1)} (A3' : ∀ a1 : A1', A2' a1 → (Type 1)) 
    {p : @Sigma2 A1 A2 A3} {p' : @Sigma2 A1' A2' A3'} (e1 : A1 = A1') (e2 : A2 == A2')
  : p == p' → pr33 p == pr33 p'
:= 
  assume e : p == p',
  have H1 : Fst p == Fst p', from Fst_heq' e1 e,
  have H2 : Snd p == Snd p', from Snd_heq' e1 e,
  have H3 : A2 (Fst p) == A2' (Fst p'), from hcongr e2 H1,
  let e3 := to_eq H3 in
  show pr33 p == pr33 p', from Snd_heq' e3 H2

set_opaque Sigma2 true
set_opaque Triple true
set_opaque pr31 true
set_opaque pr32 true
set_opaque pr33 true

--
-- Quadruples
-- 

definition Sigma3 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
    (A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1)) : (Type 1)
  := @Sigma A1 (λ a1 : A1, @Sigma2 (A2 a1) (A3 a1) (A4 a1))

definition Quadruple {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)} 
    (A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1)) (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2)
    (a4 : A4 a1 a2 a3)
:= @Pair A1 (λ x : A1, @Sigma2 (A2 x) (A3 x) (A4 x)) a1 (@Triple (A2 a1) (A3 a1) (A4 a1) a2 a3 a4)

definition pr41 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
    {A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1)}   
  (p : @Sigma3 A1 A2 A3 A4) := Fst p 

definition pr42 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
    {A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1)}   
  (p : @Sigma3 A1 A2 A3 A4) 
:= @pr31 (A2 (Fst p)) (A3 (Fst p)) (A4 (Fst p)) (Snd p) 

definition pr43 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
    {A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1)}   
  (p : @Sigma3 A1 A2 A3 A4) 
:= @pr32 (A2 (Fst p)) (A3 (Fst p)) (A4 (Fst p)) (Snd p) 

definition pr44 {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
    {A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1)}   
  (p : @Sigma3 A1 A2 A3 A4) 
:= @pr33 (A2 (Fst p)) (A3 (Fst p)) (A4 (Fst p)) (Snd p)

theorem pr41_Quadruple_eq {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
   (A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1))
    (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3) :
  pr41 (@Quadruple A1 A2 A3 A4 a1 a2 a3 a4) = a1
:= FstAx _ _

theorem pr42_Quadruple_eq {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
   (A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1))
    (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3) :
  pr42 (@Quadruple A1 A2 A3 A4 a1 a2 a3 a4) == a2
:=
  let q1234 := @Quadruple A1 A2 A3 A4 a1 a2 a3 a4 in
  let t234 := @Triple (A2 a1) (A3 a1) (A4 a1) a2 a3 a4 in
  have H1 : Fst q1234 = a1, from FstAx _ _,
  have H2 : Snd q1234 == t234, from SndAx _ _,
  have H3 : A2 (Fst q1234) = A2 a1, from congr2 A2 H1,
  have H4 : pr42 q1234 == pr31 t234,
    from pr31_heq (A4 (Fst q1234)) (A4 a1) H3 H2,
  have H5 : pr31 t234 == a2, from to_heq (pr31_Triple_eq _ _ _ _),
  htrans H4 H5

theorem pr43_Quadruple_eq {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
   (A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1))
    (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3) :
  pr43 (@Quadruple A1 A2 A3 A4 a1 a2 a3 a4) == a3
:=
  let q1234 := @Quadruple A1 A2 A3 A4 a1 a2 a3 a4 in
  let t234 := @Triple (A2 a1) (A3 a1) (A4 a1) a2 a3 a4 in
  have H1 : Fst q1234 = a1, from FstAx _ _,
  have H2 : Snd q1234 == t234, from SndAx _ _,
  have H3 : A2 (Fst q1234) = A2 a1, from congr2 A2 H1,
  have H3' : A3 (Fst q1234) == A3 a1, from hcongr (hrefl A3) (to_heq H1),
  have H4 : pr43 q1234 == pr32 t234,
    from pr32_heq (A4 (Fst q1234)) (A4 a1) H3 H3' H2,
  have H5 : pr32 t234 == a3, from pr32_Triple_eq _ _ _ _,
  htrans H4 H5

theorem pr44_Quadruple_eq {A1 : (Type 1)} {A2 : A1 → (Type 1)} {A3 : ∀ a1 : A1, A2 a1 → (Type 1)}
   (A4 : ∀ (a1 : A1) (a2 : A2 a1), A3 a1 a2 → (Type 1))
    (a1 : A1) (a2 : A2 a1) (a3 : A3 a1 a2) (a4 : A4 a1 a2 a3) :
  pr44 (@Quadruple A1 A2 A3 A4 a1 a2 a3 a4) == a4
:=
  let q1234 := @Quadruple A1 A2 A3 A4 a1 a2 a3 a4 in
  let t234 := @Triple (A2 a1) (A3 a1) (A4 a1) a2 a3 a4 in
  have H1 : Fst q1234 = a1, from FstAx _ _,
  have H2 : Snd q1234 == t234, from SndAx _ _,
  have H3 : A2 (Fst q1234) = A2 a1, from congr2 A2 H1,
  have H3' : A3 (Fst q1234) == A3 a1, from hcongr (hrefl A3) (to_heq H1),
  have H4 : pr44 q1234 == pr33 t234,
    from pr33_heq (A4 (Fst q1234)) (A4 a1) H3 H3' H2,
  have H5 : @pr33 (A2 a1) (A3 a1) (A4 a1) t234 == a4, 
    from @pr33_Triple_eq (A2 a1) (A3 a1) (A4 a1) a2 a3 a4,
  htrans H4 H5

set_opaque Sigma3 true
set_opaque Quadruple true
set_opaque pr41 true
set_opaque pr42 true
set_opaque pr43 true
set_opaque pr44 true

 

--
-- Experiment with Pair a1 (Pair a2 (Pair a3 a4))
-- 

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
-- Triple type parameterized by a1 a2 a3
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
theorem H_eq_a1 : f_1234 = a1
:= @FstAx A1 A1_tuple_ty a1 tuple_234
theorem H_eq_triple : s_1234 == tuple_234
:= @SndAx A1 A1_tuple_ty a1 tuple_234
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
eval tuple_1234
eval f_1234
eval fs_1234
eval fss_1234
eval sss_1234
check H_eq_a1
check H_eq_a2
check H_eq_a3
check H_eq_a4
theorem f_quadruple : Fst (Pair a1 (Pair a2 (Pair a3 a4))) = a1
:= H_eq_a1
theorem fs_quadruple : Fst (Snd (Pair a1 (Pair a2 (Pair a3 a4)))) == a2
:= H_eq_a2
theorem fss_quadruple : Fst (Snd (Snd (Pair a1 (Pair a2 (Pair a3 a4))))) == a3
:= H_eq_a3
theorem sss_quadruple : Snd (Snd (Snd (Pair a1 (Pair a2 (Pair a3 a4))))) == a4
:= H_eq_a4
end
-- Show the theorems with their parameters
check f_quadruple
check fs_quadruple
check fss_quadruple
check sss_quadruple
exit
