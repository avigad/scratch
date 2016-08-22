/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Automated tableaux reasoners, inspired by the ones in Isabelle.

  clarify : applies safe rules only, doesn't split goals
  safe : applies safe rules only, though it may split goals
  auto : applies safe rules, and then does a bactracking search with unsafe rules.

All can be called in classical or intuitionistic mode, and all can use the simplifier as well
to simplify the goal and hypotheses.

To do:

- use attribute manager to keep track of rules
- need tactics to build introduction and elimination rules automatically
    (in particular, elim rules from dest rules)
- need version of apply that doesn't instantiate metavariables
- bound split depth in safe, backtracking depth in force, and iterations in clarify
- rules should match goal w/ or w/out reduction to whnf (reducible)
- improve tracing output by keeping track of backtracking depth
- provide better error messages when the name of a theorem doesn't exist; for example,
    replace mk_const with mk_const_with_warning (when installing the rule?)
- write a splitter, to help simp
- use a backtracking version of reflexivity
- do more instantiations of quantifiers
- with bintro and belim rules, "num_subgoals" is "really num_branches"
- for intuitionistic logic, add a safe elimination rule for A → B, A, and also for A ∨ B → C,
  and similarly for (∃ x, A x → C)
- add safe rules for quantifiers, e.g. ∀ x, P x |- P a

Questions:

- In backtracking search, use better selection of rules, e.g. to chose those with fewest subgoals?
- Should calls to simplifier use clarify as the prover?
- Use more sophisticated handling of quantifiers?
- Should we ever call cases, or induction? Maybe with user hints?
- Better handling of equality? E.g. use symmetry as an elim rule?
- When backtracking, can we intelligently detect that some subgoals can be thrown away?
    For example, in the intuitionistic elim rule for A → B, we may end up not using B.
    The tactic that handles that can detect this.

Note: the rules are not complete for intuitionistic propositional logic, which may require
using an elim rule on A → B multiple times.
-/
open expr tactic list nat

declare_trace auto
set_option trace.auto false

-- TODO: this is useful here; add it to list library?
private definition for {A B : Type} (l : list A) (f : A → B) : list B := map f l


/- logic rules for the tableau prover -/

theorem not_or_of_imp {A B : Prop} (H : A → B) : ¬ A ∨ B :=
or.elim (classical.em A) (λ H', or.inr (H H')) (λ H', or.inl H')

lemma classical_swap {A : Prop} (B : Prop) (H₁ : ¬ A) (H₂ : ¬ B → A) : B :=
classical.by_contradiction (λ H, H₁ (H₂ H))

theorem imp_classical_elim {A B C : Prop} (H : A → B) (H₁ : ¬ A → C) (H₂ : B → C) : C :=
or.elim (not_or_of_imp H) (λ H', H₁ H') (λ H', H₂ H')

theorem imp_intuit_elim {A B C : Prop} (H : A → B) (H₁ : A) (H₂ : B → C) : C :=
H₂ (H H₁)

theorem or_classical_intro {A B : Prop} (H : ¬ A → B) : A ∨ B :=
or.elim (classical.em A) (λ H', or.inl H') (λ H', or.inr (H H'))

theorem iff_elim {A B C : Prop} (H : A ↔ B) (H' : (A → B) → (B → A) → C) : C :=
iff.elim H' H

theorem exists.intro2 {A : Type} {P : A → Prop} (a₁ a₂ : A) (H : P a₁ ∨ P a₂) : ∃ x, P x :=
or.elim H (λ H', exists.intro _ H') (λ H', exists.intro _ H')

theorem forall_elim {A : Type} {P : A → Prop} {C : Prop} (H : ∀ x, P x)
  {y : A} (H' : P y → C) : C :=
H' (H y)

theorem forall_elim2 {A : Type} {P : A → Prop} {C : Prop} (H : ∀ x, P x)
  {y₁ y₂ : A} (H' : P y₁ ∧ P y₂ → C) : C :=
H' (and.intro (H y₁) (H y₂))

-- for the intuitionistic prover

theorem not_or_elim {A B C : Prop} (H : ¬ (A ∨ B)) (H₁ : ¬ A → ¬ B → C) : C :=
H₁ (λ HA, H (or.inl HA)) (λ HB, H (or.inr HB))

theorem not_not_not_elim {A C : Prop} (H : ¬ ¬ ¬ A) (H₁ : ¬ A → C) : C :=
H₁ (λ H', H (not_not_intro H'))

namespace tactic

/- utils -/

meta_definition collect_props : list expr → tactic (list expr)
| []        := return []
| (h :: hs) := do
  props   ← collect_props hs,
  ht      ← infer_type h,
  htt     ← infer_type ht,
  (unify htt prop >> return (h :: props)) <|> return props

meta_definition unfold_all (ns : list name) : tactic unit :=
do unfold ns, local_context >>= collect_props >>= monad.mapM' (unfold_at ns)

meta_definition head_symbol : expr → name
| (const n a)      := n
| (app e a)        := match (get_app_fn e) with
                      | (const n l) := n
                      | a           := `none
                      end
| (pi a₁ a₂ a₃ a₄) := `pi
| a                := `none

private meta_definition whnf_red : expr → tactic expr := whnf_core reducible

meta_definition is_negation (e : expr) : tactic bool :=
do e' ← whnf_red e,
   if head_symbol e' = `not then return tt
   else if is_pi e' = tt then
    (do b' ← whnf_red (binding_body e'),
        bool.cond (is_false b')
          (return tt)
          (return ff))
   else return ff


/- versions of the simplifier that call themselves recursively -/

-- simp_add_prove_max_depth l d uses the simplifier as its own prover, recursing up to depth d
meta_definition simp_add_prove_max_depth (lemmas : list expr) : ℕ → tactic unit
| 0        := failed
| (succ d) := do l ← local_context >>= collect_props,
                 simplify_goal (simp_add_prove_max_depth lemmas d) (l ++ lemmas),
                 triv

meta_definition strong_simp_add (lemmas : list expr) : tactic unit :=
do l ← local_context >>= collect_props,
   simplify_goal (simp_add_prove_max_depth lemmas 10) (l ++ lemmas),
   try triv

meta_definition strong_simp : tactic unit :=
strong_simp_add []

meta_definition strong_simp_at_add (h : expr) (lemmas : list expr) : tactic unit :=
do simp_core_at (simp_add_prove_max_depth lemmas 10) lemmas h

meta_definition strong_simp_at (h : expr) : tactic unit :=
do strong_simp_at_add h []

meta_definition strong_simp_hyps_add (lemmas : list expr) : tactic unit :=
have aux : list expr → tactic unit
     | []        := skip
     | (h :: hs) := try (strong_simp_at_add h lemmas) >> aux hs,
do l ← local_context,
   aux l

meta_definition strong_simp_hyps : tactic unit :=
strong_simp_hyps_add []


/-
  These are for tracing. We use a thunk to avoid computing a string when it is not needed.

  auto_trace_step is meant to trace a single step, e.g. application of a rule, showing the state
    before and after.

  auto_trace_with_fail_message can be used to print a message after the tactic, e.g. after
    calling a continuation.
-/

meta_definition auto_trace_step (tac : tactic unit) (s : unit → string) : tactic unit :=
bool.cond (is_trace_enabled_for `auto)
  (let s' := s () in
    do trace s',
       trace_state,
       (tac >> trace ("succeeded " ++ s') >> trace_state >> trace "-----") <|>
         (trace ("failed " ++ s') >> trace "-----" >> failed))
  tac

meta_definition auto_trace_with_fail_message (tac : tactic unit) (s : unit → string) :
  tactic unit :=
bool.cond (is_trace_enabled_for `auto)
  (tac <|> (trace (s ()) >> failed))
  tac


/-
  Safe versions of some tactics, i.e. tactics that do not instantiate metavariables and
  hence can be applied in safe mode.
-/

-- we really want: e₁ and e₂ can be unified without instantiating metavariables
meta_definition unify_safe_core (t : transparency) (e₁ e₂ : expr) : tactic unit :=
bool.cond (has_meta_var e₁ || has_meta_var e₂) failed (unify_core t e₁ e₂)

meta_definition unify_safe (e₁ e₂ : expr) : tactic unit :=
unify_safe_core semireducible e₁ e₂

-- we really want: try to apply e, without instantiation any metavariables in the goal
-- maybe we also want the same for fapply?
meta_definition apply_safe_core (t : transparency) (all : bool) (insts : bool) (e : expr) :
  tactic unit :=
apply_core t all insts e

meta_definition apply_safe : expr → tactic unit :=
apply_safe_core semireducible ff tt

/- a safe version of assumption -/

meta_definition find_same_type_safe (e : expr) (l : list expr) : tactic expr :=
first (map (λ H, do {t ← infer_type H, unify_safe e t >> return H}) l)

meta_definition assumption_safe_trace_message (H : expr) : unit → string :=
λ u, "applying assumption " ++ to_string H

meta_definition assumption_safe : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     H   ← find_same_type_safe t ctx,
     auto_trace_step (exact H) (assumption_safe_trace_message H) }

/- a safe version of contradiction -/

meta_definition contra_A_not_A_safe_trace_message (H2 H1 : expr) : unit → string :=
λ u, "using contradiction at " ++ to_string H2 ++ ", " ++ to_string H1

private meta_definition contra_A_not_A_safe : list expr → list expr → tactic unit
| []         Hs := failed
| (H1 :: Rs) Hs :=
  do t_0 ← infer_type H1,
     t   ← whnf t_0,
     (do a ← match_not t,
         H2 ← find_same_type_safe a Hs,
         tgt ← target,
         pr ← mk_app `absurd [tgt, H2, H1],
         auto_trace_step (exact pr) (contra_A_not_A_safe_trace_message H2 H1))
         <|> contra_A_not_A_safe Rs Hs

meta_definition contradiction_safe : tactic unit :=
do ctx ← local_context, contra_A_not_A_safe ctx ctx


/-
The structure storing a rule has the following data:

  key : name         := the head symbol that triggers the rule
  num_subgoals : nat := number of subgoals introduced
  classical : bool   := whether to use in classical mode
  intuit : bool      := whether to use in intuitionistic mode
  tac : ...          := the tactic used to execute the rule

Notice that all the work is done by tac, which is arbitrary. Helper functions build suitable
tactics in common situations, but users can write more complicated ones. All the other data
is used to find the rules quickly and decide when to apply them.

Currently, the only thing that varies is the type of the tactic, so this is given as a parameter:

  intro_rule_type == tactic unit
  elim_rule_type  == expr → tactic unit
  bintro_rule     == tactic unit → tactic unit
  belim_rule      == tactic unit → expr → tactic unit

The letter "b" is for "backtracking." The elimination rule takes the expression to which it is
applied, and the last two take continuations.
-/

structure rule_data (A : Type) : Type :=
(key : name) (num_subgoals : ℕ) (classical : bool) (intuit : bool) (tac : A)

meta_definition rule_key {A : Type} : rule_data A → name := rule_data.key

meta_definition intro_rule : Type₁  := rule_data (tactic unit)
meta_definition elim_rule : Type₁   := rule_data (expr → tactic unit)
meta_definition bintro_rule : Type₁ := rule_data (tactic unit → tactic unit)
meta_definition belim_rule : Type₁  := rule_data (expr → tactic unit → tactic unit)

meta_definition rule_database (A : Type) : Type := rb_lmap name (rule_data A)

meta_definition intro_rule_database : Type₁  := rb_lmap name intro_rule
meta_definition elim_rule_database : Type₁   := rb_lmap name elim_rule
meta_definition bintro_rule_database : Type₁ := rb_lmap name bintro_rule
meta_definition belim_rule_database : Type₁  := rb_lmap name belim_rule

meta_definition mk_rule_database (A : Type) : rule_database A := rb_lmap.mk _ _

meta_definition insert_rule {A : Type} (db : rule_database A) (r : rule_data A) :
  rule_database A :=
rb_lmap.insert db (rule_key r) r

meta_definition insert_rule_list {A : Type} (db : rule_database A) :
  list (rule_data A) → rule_database A
| []        := db
| (r :: rs) := insert_rule (insert_rule_list db rs) r

meta_definition initialize_rule_database {A : Type} (l : list (rule_data A)) : rule_database A :=
insert_rule_list (mk_rule_database A) l

meta_definition find_rules {A : Type} (db : rule_database A) (key : name) : list (rule_data A) :=
rb_lmap.find db key


/- intro rules -/

meta_definition apply_intro_rule_trace_message (r : intro_rule) : unit → string :=
λ u, "applying intro rule for " ++ to_string (rule_key r)

meta_definition apply_intro_rule (db : intro_rule_database) (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do goal ← target >>= whnf_red,
   first $ for (find_rules db (head_symbol goal))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                 bool.cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             auto_trace_step (rule_data.tac r) (apply_intro_rule_trace_message r)
           else failed)

/- procedures for building particular intro rules -/

meta_definition deploy_intro (op : name) : tactic unit :=
mk_const op >>= apply

meta_definition deploy_intro_then_intros (op : name) : tactic unit :=
mk_const op >>= apply >> intros >> return ()


/- backtracking intro rules -/

meta_definition apply_bintro_rule (db : bintro_rule_database) (max_subgoals : ℕ) (classical : bool)
    (cont : tactic unit) :
  tactic unit :=
do goal ← target >>= whnf_red,
   first $ for (find_rules db (head_symbol goal))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                bool.cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             rule_data.tac r cont
           else failed)

/- procedure for building particular intro rules -/

meta_definition deploy_bintro_choices (l : list (tactic unit)) : tactic unit → tactic unit :=
take cont, first $ for l (λ t, do
  auto_trace_step t (λ u, "applying backtracking intro rule"),
  auto_trace_with_fail_message cont (λ u, "failed applying backtracking intro rule"))


/- elim rules -/

-- convert (... h : ¬ A ... ==> B) to (... hn : ¬ B ... ==> A), where h' has a fresh name
meta_definition do_classical_swap (h : expr) : tactic expr :=
do goal ← target,
   mk_mapp `classical_swap [none, some goal, some h] >>= apply,
   clear h,
   mk_fresh_name >>= intro

meta_definition classical_apply_intro_rule_at (db : intro_rule_database) (h : expr)
    (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do n ← mk_fresh_name,
   negated_concl ← do_classical_swap h,
   apply_intro_rule db max_subgoals classical ;
     (intros >> do_classical_swap negated_concl >> skip)

meta_definition apply_elim_rule_at_trace_message (r : elim_rule) (h : expr) : unit → string :=
λ u, "trying to apply elim rule for " ++ to_string (rule_key r) ++ " at " ++ to_string h

meta_definition apply_elim_rule_at (idb : intro_rule_database) (edb : elim_rule_database)
    (h : expr) (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do ht ← infer_type h >>= whnf_red,
   (first $ for (find_rules edb (head_symbol ht))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                bool.cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             auto_trace_step (rule_data.tac r h) (apply_elim_rule_at_trace_message r h)
           else failed)) <|>
   bool.cond classical
     (monad.condM (is_negation ht)
       (classical_apply_intro_rule_at idb h max_subgoals classical)
       failed)
     failed

meta_definition apply_elim_rule (idb : intro_rule_database) (edb : elim_rule_database)
    (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do hs ← local_context >>= collect_props,
   first $ for hs (λ h, apply_elim_rule_at idb edb h max_subgoals classical)

/- procedures for building particular elim rules -/

private definition elim_instance_mapp_args (motive major : ℕ) (emotive emajor : expr) :
  list (option expr) :=
let diff := major - motive in
nat.rec_on major []
  (λ n l, if n = diff then some emotive :: l
          else if n = 0 then some emajor :: l else none :: l)

meta_definition deploy_elim_at (op : name) (motive : ℕ) (major : ℕ) : expr → tactic unit :=
λ h : expr,
do goal ← target,
   el ← mk_mapp op (elim_instance_mapp_args motive major goal h),
   clear h,
   apply el ; (intros >> skip),    -- is apply_safe really needed?
   return ()


/- backtracking elim rules -/

meta_definition classical_apply_bintro_rule_at (db : bintro_rule_database) (h : expr)
    (max_subgoals : ℕ) (classical : bool) (cont : tactic unit) :
  tactic unit :=
do n ← mk_fresh_name,
   negated_concl ← do_classical_swap h,
   apply_bintro_rule db max_subgoals classical (intros >> do_classical_swap negated_concl >> cont)

meta_definition apply_belim_rule_at (bidb : bintro_rule_database) (bedb : belim_rule_database)
    (h : expr) (max_subgoals : ℕ) (classical : bool) (cont : tactic unit) :
  tactic unit :=
do ht ← infer_type h >>= whnf_red,
   (first $ for (find_rules bedb (head_symbol ht))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                bool.cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             rule_data.tac r h cont
           else failed)) <|>
   bool.cond classical
     (monad.condM (is_negation ht)
       (classical_apply_bintro_rule_at bidb h max_subgoals classical cont)
       failed)
     failed

meta_definition apply_belim_rule (bidb : bintro_rule_database) (bedb : belim_rule_database)
    (max_subgoals : ℕ) (classical : bool) (cont : tactic unit) :
  tactic unit :=
do hs ← local_context >>= collect_props,
   first (for hs (λ h, apply_belim_rule_at bidb bedb h max_subgoals classical cont))


/- procedure for building particular belim rules -/

meta_definition belim_choices_trace_message (h : expr) : unit → string :=
λ u, "applying backtracking elim rule at " ++ to_string h

meta_definition belim_choices_trace_message₂ (h : expr) : unit → string :=
λ u, "failed applying backtracking elim rule at " ++ to_string h

meta_definition belim_choices_trace_message₃ (h : expr) : unit → string :=
λ u, "clearing hypothesis h" ++ to_string h

meta_definition deploy_belim_choices (l : list (expr → tactic unit)) :
  expr → tactic unit → tactic unit :=
take h cont,
  (first $ for l (λ t,
    auto_trace_step (t h) (belim_choices_trace_message h) >>
    auto_trace_with_fail_message cont (belim_choices_trace_message₂ h))) <|>
  (auto_trace_step (clear h) (belim_choices_trace_message₃ h) >> cont)


/- try to do a subst or injection on a hypothesis -/

meta_definition has_eq_type (h : expr) : tactic bool :=
do htype ← infer_type h >>= whnf_red,
   return (match (expr.is_eq htype) with (some _) := tt | none := ff end)

meta_definition try_subst_and_injection_on_hyps : tactic unit :=
do ctx ← local_context,
   first $ for ctx (λ h, do
     b ← has_eq_type h,
     bool.cond b
       ((subst h >> clear h) <|>  (injection h >> clear h))
       failed)

/-
    Standard rule sets
-/

/- standard introduction rules -/

meta_definition true_intro_rule : intro_rule :=
⦃ rule_data, key := ``true, num_subgoals := 0, classical := tt, intuit := tt,
    tac := deploy_intro ``true.intro ⦄

meta_definition and_intro_rule : intro_rule :=
⦃ rule_data, key := ``and, num_subgoals := 2, classical := tt, intuit := tt,
    tac := deploy_intro ``and.intro ⦄

meta_definition or_classical_intro_rule : intro_rule :=
⦃ rule_data, key := ``or, num_subgoals := 1, classical := tt, intuit := ff,
    tac := deploy_intro_then_intros ``or_classical_intro ⦄

meta_definition Pi_intro_rule : intro_rule :=
⦃ rule_data, key := `pi, num_subgoals := 1, classical := tt, intuit := tt,
    tac := intro1 >> return () ⦄

meta_definition not_intro_rule : intro_rule :=
⦃ rule_data, key := ``not, num_subgoals := 1, classical := tt, intuit := tt,
    tac := intro1 >> return () ⦄

meta_definition iff_intro_rule : intro_rule :=
⦃ rule_data, key := ``iff, num_subgoals := 2, classical := tt, intuit := tt,
    tac := deploy_intro ``iff.intro ⦄

meta_definition standard_intro_rules : list intro_rule :=
[true_intro_rule, and_intro_rule, or_classical_intro_rule, Pi_intro_rule, not_intro_rule,
  iff_intro_rule]

/- standard backtracking intro rules -/

meta_definition or_intuit_bintro_rule : bintro_rule :=
⦃ rule_data, key := ``or, num_subgoals := 2, classical := ff, intuit := tt,
    tac := deploy_bintro_choices [deploy_intro ``or.inl, deploy_intro ``or.inr] ⦄

meta_definition standard_bintro_rules : list bintro_rule :=
[or_intuit_bintro_rule]

/- standard elim rules -/

meta_definition and_elim_rule :=
⦃ rule_data, key := ``and, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_elim_at ``and.elim 3 4 ⦄

meta_definition or_elim_rule :=
⦃ rule_data, key := ``or, num_subgoals := 2, classical := tt, intuit := tt,
    tac := deploy_elim_at ``or.elim 3 4 ⦄

meta_definition false_elim_rule :=
⦃ rule_data, key := ``false, num_subgoals := 0, classical := tt, intuit := tt,
    tac := deploy_elim_at ``false.elim 1 2 ⦄

meta_definition exists_elim_rule :=
⦃ rule_data, key := ``Exists, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_elim_at ``exists.elim 3 4 ⦄

-- classical elim rule for A → B, should not be applied if B is false!
meta_definition deploy_imp_classical_elim_at (h : expr) : tactic unit :=
do ht ← infer_type h >>= whnf_red,
   b ← is_negation ht,
   bool.cond b failed (deploy_elim_at ``imp_classical_elim 3 4 h)

meta_definition imp_classical_elim_rule :=
⦃ rule_data, key := `pi, num_subgoals := 2, classical := tt, intuit := ff,
    tac := deploy_imp_classical_elim_at ⦄

meta_definition iff_elim_rule :=
⦃ rule_data, key := ``iff, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_elim_at ``iff_elim 3 4 ⦄

-- needed to speed up intuitionistic treatment of ¬ (A ∨ B) in a hypothesis
meta_definition not_or_intuit_elim_rule :=
⦃ rule_data, key := ``not, num_subgoals := 1, classical := ff, intuit := tt,
    tac := deploy_elim_at ``not_or_elim 3 4 ⦄

meta_definition not_not_not_intuit_elim_rule :=
⦃ rule_data, key := ``not, num_subgoals := 1, classical := ff, intuit := tt,
    tac := deploy_elim_at ``not_not_not_elim 2 3 ⦄

meta_definition standard_elim_rules : list elim_rule :=
[and_elim_rule, or_elim_rule, false_elim_rule, exists_elim_rule, imp_classical_elim_rule,
  iff_elim_rule, not_or_intuit_elim_rule, not_not_not_intuit_elim_rule]

/- standard backtracking elim rules -/

meta_definition imp_intuit_belim_rule :=
⦃ rule_data, key := `pi, num_subgoals := 2, classical := ff, intuit := tt,
    tac := deploy_belim_choices [deploy_elim_at ``imp_intuit_elim 3 4] ⦄

meta_definition standard_belim_rules : list belim_rule :=
[imp_intuit_belim_rule]


/- backtracking assumption tactic -/

meta_definition try_assumptions_trace_message₁ (h ht : expr) : unit → string :=
λ u, "applying assumption (" ++ to_string h ++ " : " ++ to_string ht ++ ") with bactracking"

meta_definition try_assumptions_trace_message₂ (h ht : expr) : unit → string :=
λ u, "backtracking assumption (" ++ to_string h ++ " : " ++ to_string ht ++ ")"

meta_definition try_assumptions (cont : tactic unit) :=
do ctx ← local_context,
   goal ← target,
   first $ for ctx
     (λ h, do ht ← infer_type h,
              unify ht goal,
              auto_trace_step (exact h) (try_assumptions_trace_message₁ h ht),
              auto_trace_with_fail_message cont (try_assumptions_trace_message₂ h ht))

meta_definition try_contradictions_trace_message₁ (h ht h' ht' : expr) : unit → string :=
λ u, "applying contradiction (" ++ to_string h ++ " : " ++ to_string ht ++ ") <-> (" ++
       to_string h' ++ " : " ++ to_string ht' ++ ") with backtracking"

meta_definition try_contradictions_trace_message₂ (h ht h' ht' : expr) : unit → string :=
λ u, "backtracking contradiction (" ++ to_string h ++ " : " ++ to_string ht ++ ") <-> (" ++
       to_string h' ++ " : " ++ to_string ht' ++ ")"

meta_definition try_contradictions (cont : tactic unit) :=
do ctx ← local_context,
   goal ← target,
   first $ for ctx (λ h, do
     ht ← infer_type h,
     unneg_ht ← match_not ht,
     first $ for ctx (λ h', do
       ht' ← infer_type h',
       unify ht' unneg_ht,
       auto_trace_step (mk_app ``absurd [goal, h', h] >>= exact)
         (try_contradictions_trace_message₁ h ht h' ht'),
       auto_trace_with_fail_message cont
         (try_contradictions_trace_message₂ h ht h' ht')))


/- instantiating quantifiers in the backtracking search -/

meta_definition has_forall_type (h : expr) : tactic bool :=
do ht ← infer_type h,
   if head_symbol ht ≠ `pi then return ff
   else do
     htt ← infer_type ht,
     if htt ≠ prop then return ff
     else do
       dt ← infer_type (binding_domain ht),
      if dt ≠ prop then return tt else return ff

meta_definition try_instantiate_quantifiers (cont : tactic unit) : tactic unit :=
do hs ← (local_context >>= monad.filterM has_forall_type),
   gt ← target,
   when (hs = [] ∧ head_symbol gt ≠ `Exists) failed,
   monad.forM' hs
     (λ h, do goal ← target,
           el ← mk_mapp ``forall_elim (elim_instance_mapp_args 3 4 goal h),
           apply el ; (intros >> skip)),
   when (head_symbol gt = `Exists) split,
   monad.forM' hs clear,
   cont


/-
  Safe automation. These operate on the first goal, and apply only safe rules (the new
  state is logically equivalent to the original one). They make whatever progress they
  can, and leave the user with zero or more goals.

  They take the following arguments:

  classical     : classical or intuitionistic
  use_simp      : whether to use the simplifier
  simp_lemmas   : in the latter case, extra lemmas to use
-/

-- perform safe rules that do not split the goal
meta_definition clarify_core (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database) (simp_lemmas : list expr) :
  tactic unit :=
do repeat (apply_intro_rule idb 1 classical),
   repeat (apply_elim_rule idb edb 1 classical),
   repeat try_subst_and_injection_on_hyps,
   (now <|> assumption_safe <|> contradiction_safe <|>
     when (use_simp = tt)
       (do when_tracing `auto (trace "calling simplifier..."),
          try (strong_simp_hyps_add simp_lemmas),
          try (strong_simp_add simp_lemmas),
          try (now <|> assumption_safe <|> contradiction_safe)))

-- perform safe rules
meta_definition safe_core (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database) (simp_lemmas : list expr) :
  tactic unit :=
do clarify_core classical use_simp idb edb simp_lemmas,
   now <|>
     try ((apply_intro_rule idb 10 classical <|> apply_elim_rule idb edb 10 classical) ;
        (safe_core classical use_simp idb edb simp_lemmas))

/-
  The backtracking tableau prover.

  The function force_all_core_aux is the heart of the tableau prover. It takes a list of goals,
  which are assumed to have been processed with the safe rules already and are not visible on the
  goal stack. It applies safe rules to the goals in the current goal list (if any),
  and then starts calling backtracking rules.

  This function is meant to be passed as a continuation to the backtracking tactics, which are
  called with a single goal. The tactics should operate on the goal, resulting in a new goal
  list. They should then call the continuation to finish the backtracking search.

  The function succeeds if all the goals are ultimately proved, and it fails otherwise.
-/

meta_definition force_all_core_aux (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database)
    (bidb : bintro_rule_database) (bedb : belim_rule_database) (simp_lemmas : list expr)
    (preprocessed_goals : list expr) :
  tactic unit :=
let force_core_rec := force_all_core_aux classical use_simp idb edb bidb bedb simp_lemmas in
have process_goals_with_bactracking : list expr → tactic unit
     | []        := skip   -- success!
     | (g :: gs) :=
       do {set_goals [g],   -- TODO: should I check to make sure g is still a goal?
           try_assumptions (force_core_rec gs) <|>
           try_contradictions (force_core_rec gs) <|>
           try_instantiate_quantifiers (force_core_rec gs) <|>
           apply_bintro_rule bidb 10 classical (force_core_rec gs) <|>
           apply_belim_rule bidb bedb 10 classical (force_core_rec gs)},
do n ← num_goals,
   if n ≠ 0 then do
     all_goals (safe_core classical use_simp idb edb simp_lemmas),
     gs ← get_goals,
     set_goals [],
     force_all_core_aux classical use_simp idb edb bidb bedb simp_lemmas (gs ++ preprocessed_goals)
   else do
     process_goals_with_bactracking preprocessed_goals

-- the main tableaux prover: succeeds if all goals are proved
meta_definition force_all_core (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database)
    (bidb : bintro_rule_database) (bedb : belim_rule_database) (simp_lemmas : list expr) :
  tactic unit :=
force_all_core_aux classical use_simp idb edb bidb bedb simp_lemmas []


/- front ends -/

-- applies to first goal, never splits it, applies only safe rules, always succeeds
meta_definition clarify (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (simp_lemmas : list expr) :
  tactic unit :=
let idb := initialize_rule_database (standard_intro_rules ++ irules),
    edb := initialize_rule_database (standard_elim_rules ++ erules) in
clarify_core classical use_simp idb edb simp_lemmas

-- applies to first goal, applies only safe rules, always succeeds
meta_definition safe (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (simp_lemmas : list expr) :
  tactic unit :=
let idb := initialize_rule_database (standard_intro_rules ++ irules),
    edb := initialize_rule_database (standard_elim_rules ++ erules) in
safe_core classical use_simp idb edb simp_lemmas

-- applies safe to all goals
meta_definition safe_all (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (simp_lemmas : list expr) :
  tactic unit :=
all_goals (safe classical use_simp irules erules simp_lemmas)

-- applies to all goals, proves them all or fails
meta_definition force_all (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule)
    (birules : list bintro_rule) (berules : list belim_rule) (simp_lemmas : list expr) :
  tactic unit :=
let idb := initialize_rule_database (standard_intro_rules ++ irules),
    bidb := initialize_rule_database (standard_bintro_rules ++ birules),
    edb := initialize_rule_database (standard_elim_rules ++ erules),
    bedb := initialize_rule_database (standard_belim_rules ++ berules) in
force_all_core classical use_simp idb edb bidb bedb simp_lemmas

-- applies to force_all to the first goal only
meta_definition force (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule)
    (birules : list bintro_rule) (berules : list belim_rule) (simp_lemmas : list expr) :
  tactic unit :=
focus [force_all classical use_simp irules erules birules berules simp_lemmas]

-- applies to all goals, always succeeds
meta_definition auto (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule)
    (birules : list bintro_rule) (berules : list belim_rule) (simp_lemmas : list expr) :
  tactic unit :=
safe_all classical use_simp irules erules simp_lemmas >>
all_goals (try (force classical use_simp irules erules birules berules simp_lemmas))


/- for testing -/

meta_definition clarify' : tactic unit := clarify tt ff [] [] []

meta_definition safe' : tactic unit := safe tt ff [] [] []

meta_definition ssafe' : tactic unit := safe tt tt [] [] []  -- with simplification

meta_definition auto' : tactic unit := auto tt ff [] [] [] [] []

meta_definition sauto' : tactic unit := auto tt tt [] [] [] [] []

meta_definition iauto' : tactic unit := auto ff ff [] [] [] [] []

meta_definition isauto' : tactic unit := auto ff tt [] [] [] [] []

end tactic
