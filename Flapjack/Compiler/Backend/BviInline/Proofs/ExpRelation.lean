module

public import Flapjack.Compiler.Backend.BviInline.Proofs.SourceCorrespondence
public import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateGrowth
public import Mathlib.Data.List.Forall2
public import Flapjack.Misc.Option.Rel

@[expose] public section

/-! Expression relation for BVI wrapper inlining. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

/-- Flapjack infrastructure: expression-level inlining relation. Its own
declaration remains untagged pending a separate declaration-level review. -/
inductive ExpRel (code : Spt (Nat × Bvi.Exp)) : Bvi.Exp → Bvi.Exp → Prop where
  | var (n : Nat) : ExpRel code (.var n) (.var n)
  | force (location index : Nat) : ExpRel code (.force location index) (.force location index)
  | ifThenElse {x y z x' y' z'} : ExpRel code x x' → ExpRel code y y' → ExpRel code z z' →
      ExpRel code (.ifThenElse x y z) (.ifThenElse x' y' z')
  | letExp {xs ys body body'} : List.Forall₂ (ExpRel code) xs ys → ExpRel code body body' →
      ExpRel code (.let xs body) (.let ys body')
  | raise {body body'} : ExpRel code body body' → ExpRel code (.raise body) (.raise body')
  | tick {body body'} : ExpRel code body body' → ExpRel code (.tick body) (.tick body')
  | op {op xs ys} : List.Forall₂ (ExpRel code) xs ys → ExpRel code (.op op xs) (.op op ys)
  | callNone {ticks target xs ys} : List.Forall₂ (ExpRel code) xs ys →
      ExpRel code (.call ticks target xs none) (.call ticks target ys none)
  | callSome {ticks target xs ys body body'} : List.Forall₂ (ExpRel code) xs ys → ExpRel code body body' →
      ExpRel code (.call ticks target xs (some body)) (.call ticks target ys (some body'))
  | letCall {rets ticks target xs ys body body'} : List.Forall₂ (ExpRel code) xs ys → ExpRel code body body' →
      ExpRel code (.letCall rets ticks target xs body) (.letCall rets ticks target ys body')
  | returnExp {xs ys} : List.Forall₂ (ExpRel code) xs ys → ExpRel code (.return xs) (.return ys)
  | inlineCall {ticks name xs ys arity body} : List.Forall₂ (ExpRel code) xs ys →
      sptLookup name code = some (arity, body) → ys.length = arity →
      ExpRel code (.call ticks (some name) xs none) (.let ys (mkTick (ticks + 1) body))


/-- Inversion of the expression relation for each source constructor. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "exp_rel_inv"]
theorem expRelInv (c : Spt (Nat × Bvi.Exp)) (n loc : Nat)
    (x1 x2 x3 x y : Bvi.Exp) (xs : List Bvi.Exp) (op : ClosLang.Op)
    (rets ticks target : Nat) (dest : Option Nat) (handler : Option Bvi.Exp) :
    (ExpRel c (.var n) y ↔ y = .var n) ∧
    (ExpRel c (.force loc n) y ↔ y = .force loc n) ∧
    (ExpRel c (.ifThenElse x1 x2 x3) y ↔
      ∃ y1 y2 y3, y = .ifThenElse y1 y2 y3 ∧ ExpRel c x1 y1 ∧
        ExpRel c x2 y2 ∧ ExpRel c x3 y3) ∧
    (ExpRel c (.let xs x) y ↔
      ∃ ys y1, y = .let ys y1 ∧ List.Forall₂ (ExpRel c) xs ys ∧ ExpRel c x y1) ∧
    (ExpRel c (.raise x) y ↔ ∃ y1, y = .raise y1 ∧ ExpRel c x y1) ∧
    (ExpRel c (.tick x) y ↔ ∃ y1, y = .tick y1 ∧ ExpRel c x y1) ∧
    (ExpRel c (.op op xs) y ↔ ∃ ys, y = .op op ys ∧ List.Forall₂ (ExpRel c) xs ys) ∧
    (ExpRel c (.return xs) y ↔ ∃ ys, y = .return ys ∧ List.Forall₂ (ExpRel c) xs ys) ∧
    (ExpRel c (.letCall rets ticks target xs x) y ↔
      ∃ ys y1, y = .letCall rets ticks target ys y1 ∧
        List.Forall₂ (ExpRel c) xs ys ∧ ExpRel c x y1) ∧
    (ExpRel c (.call ticks dest xs handler) y ↔
      (∃ ys handler1, y = .call ticks dest ys handler1 ∧
        List.Forall₂ (ExpRel c) xs ys ∧ optionRel (ExpRel c) handler handler1) ∨
      (∃ name ys arity body, dest = some name ∧ handler = none ∧
        y = .let ys (mkTick (ticks + 1) body) ∧
        List.Forall₂ (ExpRel c) xs ys ∧ sptLookup name c = some (arity, body) ∧
        ys.length = arity)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h; cases h; rfl
    · intro h; subst y; exact .var n
  · constructor
    · intro h; cases h; rfl
    · intro h; subst y; exact .force loc n
  · constructor
    · intro h; cases h with | ifThenElse a b c => exact ⟨_, _, _, rfl, a, b, c⟩
    · rintro ⟨_, _, _, rfl, a, b, c⟩; exact .ifThenElse a b c
  · constructor
    · intro h; cases h with | letExp a b => exact ⟨_, _, rfl, a, b⟩
    · rintro ⟨_, _, rfl, a, b⟩; exact .letExp a b
  · constructor
    · intro h; cases h with | raise a => exact ⟨_, rfl, a⟩
    · rintro ⟨_, rfl, a⟩; exact .raise a
  · constructor
    · intro h; cases h with | tick a => exact ⟨_, rfl, a⟩
    · rintro ⟨_, rfl, a⟩; exact .tick a
  · constructor
    · intro h; cases h with | op a => exact ⟨_, rfl, a⟩
    · rintro ⟨_, rfl, a⟩; exact .op a
  · constructor
    · intro h; cases h with | returnExp a => exact ⟨_, rfl, a⟩
    · rintro ⟨_, rfl, a⟩; exact .returnExp a
  · constructor
    · intro h; cases h with | letCall a b => exact ⟨_, _, rfl, a, b⟩
    · rintro ⟨_, _, rfl, a, b⟩; exact .letCall a b
  · constructor
    · intro h
      cases h with
      | callNone a => exact Or.inl ⟨_, none, rfl, a, trivial⟩
      | callSome a b => exact Or.inl ⟨_, some _, rfl, a, b⟩
      | inlineCall a b d => exact Or.inr ⟨_, _, _, _, rfl, rfl, rfl, a, b, d⟩
    · rintro (⟨ys, h, rfl, a, b⟩ | ⟨name, ys, arity, body, rfl, rfl, rfl, a, b, d⟩)
      · cases handler <;> cases h <;> simp_all [optionRel, ExpRel.callNone, ExpRel.callSome]
      · exact .inlineCall a b d

mutual
/-- Flapjack infrastructure: extending a code tree preserves the
expression-level inlining relation. -/
theorem expRel_mono (source target : Spt (Nat × Bvi.Exp)) (expression result : Bvi.Exp)
    (related : ExpRel source expression result) (subset : sptSubspt source target) :
    ExpRel target expression result := by
  cases related with
  | var n => exact .var n
  | force location index => exact .force location index
  | ifThenElse hx hy hz =>
    exact .ifThenElse (expRel_mono source target _ _ hx subset)
      (expRel_mono source target _ _ hy subset) (expRel_mono source target _ _ hz subset)
  | letExp hxs hb =>
    exact .letExp (expsRel_mono source target _ _ hxs subset) (expRel_mono source target _ _ hb subset)
  | raise hb => exact .raise (expRel_mono source target _ _ hb subset)
  | tick hb => exact .tick (expRel_mono source target _ _ hb subset)
  | op hxs => exact .op (expsRel_mono source target _ _ hxs subset)
  | callNone hxs => exact .callNone (expsRel_mono source target _ _ hxs subset)
  | callSome hxs hb =>
    exact .callSome (expsRel_mono source target _ _ hxs subset) (expRel_mono source target _ _ hb subset)
  | letCall hxs hb =>
    exact .letCall (expsRel_mono source target _ _ hxs subset) (expRel_mono source target _ _ hb subset)
  | returnExp hxs => exact .returnExp (expsRel_mono source target _ _ hxs subset)
  | inlineCall hxs lookup length =>
    have present := (sptMem_iff_lookup _ source).2 ⟨_, lookup⟩
    exact .inlineCall (expsRel_mono source target _ _ hxs subset) ((subset _ present).2.trans lookup) length
termination_by sizeOf expression
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack infrastructure: code extension also preserves the pointwise
relation on expression lists. -/
theorem expsRel_mono (source target : Spt (Nat × Bvi.Exp)) (expressions results : List Bvi.Exp)
    (related : List.Forall₂ (ExpRel source) expressions results) (subset : sptSubspt source target) :
    List.Forall₂ (ExpRel target) expressions results := by
  cases related with
  | nil => exact .nil
  | cons head tail => exact .cons (expRel_mono source target _ _ head subset) (expsRel_mono source target _ _ tail subset)
termination_by sizeOf expressions
decreasing_by all_goals (simp_wf; omega)
end

/-- Flapjack infrastructure: BVI evaluation preserves expression and list
relations because it only extends the code table. -/
theorem evaluate_expRel_mono {C F : Type} (executed : List Bvi.Exp) (env : List BvlSem.Value)
    (source target : BviSem.BviState C F) (result : BviSem.BviResult)
    (run : BviSem.evaluate executed env source = (result, target)) :
    (∀ x y, ExpRel source.code x y → ExpRel target.code x y) ∧
    (∀ xs ys, List.Forall₂ (ExpRel source.code) xs ys → List.Forall₂ (ExpRel target.code) xs ys) := by
  have subset := BviProps.evaluate_code_mono executed env source target result run
  exact ⟨fun x y related => expRel_mono source.code target.code x y related subset,
    fun xs ys related => expsRel_mono source.code target.code xs ys related subset⟩


namespace EvaluationRelationCarrier
/-- The canonical BVI reference-map representation has a roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end EvaluationRelationCarrier

/-- BVI evaluation preserves both individual expression relations and
pointwise expression-list relations. The evaluator inherits the real-model
assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "exp_rel_evaluate_mono"
  (fmap_as_finite_support := [refs])]
theorem expRelEvaluateMono {C F : Type} (executed : List Bvi.Exp) (env : List BvlSem.Value)
    (source target : BviSem.BviState C F) (result : BviSem.BviResult)
    (x y : Bvi.Exp) (xs ys : List Bvi.Exp) :
    ((BviSem.evaluate executed env source = (result, target) ∧ ExpRel source.code x y) →
      ExpRel target.code x y) ∧
    ((BviSem.evaluate executed env source = (result, target) ∧
      List.Forall₂ (ExpRel source.code) xs ys) → List.Forall₂ (ExpRel target.code) xs ys) := by
  constructor
  · rintro ⟨run, related⟩
    exact (evaluate_expRel_mono executed env source target result run).1 x y related
  · rintro ⟨run, related⟩
    exact (evaluate_expRel_mono executed env source target result run).2 xs ys related

mutual
/-- Every expression is related to itself by the inlining relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "exp_rel_refl"]
theorem expRel_refl (code : Spt (Nat × Bvi.Exp)) (expression : Bvi.Exp) : ExpRel code expression expression := by
  cases expression with
  | var n => exact .var n
  | force location index => exact .force location index
  | ifThenElse x y z => exact .ifThenElse (expRel_refl code x) (expRel_refl code y) (expRel_refl code z)
  | «let» xs body => exact .letExp (expsRel_refl code xs) (expRel_refl code body)
  | raise body => exact .raise (expRel_refl code body)
  | tick body => exact .tick (expRel_refl code body)
  | op op xs => exact .op (expsRel_refl code xs)
  | «return» xs => exact .returnExp (expsRel_refl code xs)
  | letCall rets ticks target xs body => exact .letCall (expsRel_refl code xs) (expRel_refl code body)
  | call ticks target xs handler =>
    cases handler with
    | none => exact .callNone (expsRel_refl code xs)
    | some body => exact .callSome (expsRel_refl code xs) (expRel_refl code body)
termination_by sizeOf expression
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack infrastructure: reflexivity extends pointwise to lists. -/
private theorem expsRel_refl (code : Spt (Nat × Bvi.Exp)) (expressions : List Bvi.Exp) :
    List.Forall₂ (ExpRel code) expressions expressions := by
  cases expressions with
  | nil => exact .nil
  | cons e rest => exact .cons (expRel_refl code e) (expsRel_refl code rest)
termination_by sizeOf expressions
decreasing_by all_goals (simp_wf; omega)
end

/-- Inlining a call without a handler preserves the expression relation when
the cache is contained in the target code and its arguments are related. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_call_none_exp_rel"]
theorem inlineCallNoneExpRel (cache code : Spt (Nat × Bvi.Exp))
    (expressions : List Bvi.Exp) (ticks : Nat) (destination : Option Nat)
    (premises : sptSubspt cache code ∧
      List.Forall₂ (ExpRel code) expressions (inlineExpsSource cache expressions)) :
    ExpRel code (.call ticks destination expressions none)
      (inlineExpSource cache (.call ticks destination expressions none)) := by
  obtain ⟨subset, related⟩ := premises
  cases destination with
  | none =>
    simpa [inlineExpSource] using ExpRel.callNone (ticks := ticks) (target := none) related
  | some name =>
    cases lookup : sptLookup name cache with
    | none =>
      simpa [inlineExpSource, lookup] using ExpRel.callNone (ticks := ticks) (target := some name) related
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      by_cases length : (inlineExpsSource cache expressions).length = arity
      · have present : sptMem name cache := (sptMem_iff_lookup name cache).2 ⟨_, lookup⟩
        have targetLookup : sptLookup name code = some (arity, body) := (subset name present).2.trans lookup
        simpa [inlineExpSource, lookup, length] using ExpRel.inlineCall (ticks := ticks) related targetLookup length
      · simpa [inlineExpSource, lookup, length] using ExpRel.callNone (ticks := ticks) (target := some name) related

mutual
/-- Flapjack infrastructure: inlining an expression produces an expression
related under any code tree containing the cache. -/
private theorem inlineExpSource_rel (cache code : Spt (Nat × Bvi.Exp)) (expression : Bvi.Exp)
    (subset : sptSubspt cache code) : ExpRel code expression (inlineExpSource cache expression) := by
  cases expression with
  | var n => simpa [inlineExpSource] using ExpRel.var (code := code) n
  | force location index => simpa [inlineExpSource] using ExpRel.force (code := code) location index
  | ifThenElse x y z =>
    simpa [inlineExpSource] using ExpRel.ifThenElse (inlineExpSource_rel cache code x subset)
      (inlineExpSource_rel cache code y subset) (inlineExpSource_rel cache code z subset)
  | «let» xs body =>
    simpa [inlineExpSource] using ExpRel.letExp (inlineExpsSource_rel cache code xs subset)
      (inlineExpSource_rel cache code body subset)
  | raise body => simpa [inlineExpSource] using ExpRel.raise (inlineExpSource_rel cache code body subset)
  | tick body => simpa [inlineExpSource] using ExpRel.tick (inlineExpSource_rel cache code body subset)
  | op op xs => simpa [inlineExpSource] using ExpRel.op (op := op) (inlineExpsSource_rel cache code xs subset)
  | «return» xs => simpa [inlineExpSource] using ExpRel.returnExp (inlineExpsSource_rel cache code xs subset)
  | letCall rets ticks target xs body =>
    simpa [inlineExpSource] using ExpRel.letCall (rets := rets) (ticks := ticks) (target := target)
      (inlineExpsSource_rel cache code xs subset) (inlineExpSource_rel cache code body subset)
  | call ticks target xs handler =>
    cases handler with
    | some body =>
      simpa [inlineExpSource] using ExpRel.callSome (ticks := ticks) (target := target)
        (inlineExpsSource_rel cache code xs subset) (inlineExpSource_rel cache code body subset)
    | none =>
      exact inlineCallNoneExpRel cache code xs ticks target
        ⟨subset, inlineExpsSource_rel cache code xs subset⟩
termination_by sizeOf expression
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack infrastructure: inlining a list preserves the pointwise
expression relation under the same cache inclusion. -/
private theorem inlineExpsSource_rel (cache code : Spt (Nat × Bvi.Exp)) (expressions : List Bvi.Exp)
    (subset : sptSubspt cache code) : List.Forall₂ (ExpRel code) expressions (inlineExpsSource cache expressions) := by
  cases expressions with
  | nil => simp [inlineExpsSource]
  | cons e rest =>
    simpa [inlineExpsSource] using List.Forall₂.cons (inlineExpSource_rel cache code e subset)
      (inlineExpsSource_rel cache code rest subset)
termination_by sizeOf expressions
decreasing_by all_goals (simp_wf; omega)
end


/-- Inlining an expression or expression list preserves the expression
relation when the target code contains the inlining cache. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exp_rel"]
theorem inlineExpRel (cache code : Spt (Nat × Bvi.Exp)) (subset : sptSubspt cache code) :
    (∀ expression, ExpRel code expression (inlineExpSource cache expression)) ∧
    (∀ expressions, List.Forall₂ (ExpRel code) expressions (inlineExpsSource cache expressions)) := by
  exact ⟨fun expression => inlineExpSource_rel cache code expression subset,
    fun expressions => inlineExpsSource_rel cache code expressions subset⟩

end Flapjack.Compiler.Backend.BviInline
