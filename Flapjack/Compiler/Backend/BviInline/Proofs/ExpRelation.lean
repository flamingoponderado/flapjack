import Flapjack.Compiler.Backend.BviInline.Proofs.SourceCorrespondence
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateGrowth
import Mathlib.Data.List.Forall2

/-! Expression relation for BVI wrapper inlining. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

/-- Flapjack infrastructure: expression-level inlining relation. This is
untagged until its nested list and optional-handler carriers are reviewed
against the original inductive relation. -/
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

mutual
/-- Flapjack infrastructure: every expression is related to itself. -/
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
theorem expsRel_refl (code : Spt (Nat × Bvi.Exp)) (expressions : List Bvi.Exp) :
    List.Forall₂ (ExpRel code) expressions expressions := by
  cases expressions with
  | nil => exact .nil
  | cons e rest => exact .cons (expRel_refl code e) (expsRel_refl code rest)
termination_by sizeOf expressions
decreasing_by all_goals (simp_wf; omega)
end

mutual
/-- Flapjack infrastructure: inlining an expression produces an expression
related under any code tree containing the cache. -/
theorem inlineExpSource_rel (cache code : Spt (Nat × Bvi.Exp)) (expression : Bvi.Exp)
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
      cases target with
      | none =>
        simpa [inlineExpSource] using ExpRel.callNone (ticks := ticks) (target := none)
          (inlineExpsSource_rel cache code xs subset)
      | some name =>
        cases lookup : sptLookup name cache with
        | none =>
          simpa [inlineExpSource, lookup] using ExpRel.callNone (ticks := ticks) (target := some name)
            (inlineExpsSource_rel cache code xs subset)
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          by_cases length : (inlineExpsSource cache xs).length = arity
          · have present : sptMem name cache := (sptMem_iff_lookup name cache).2 ⟨_, lookup⟩
            have targetLookup : sptLookup name code = some (arity, body) := (subset name present).2.trans lookup
            simpa [inlineExpSource, lookup, length] using ExpRel.inlineCall (ticks := ticks)
              (inlineExpsSource_rel cache code xs subset) targetLookup length
          · simpa [inlineExpSource, lookup, length] using ExpRel.callNone (ticks := ticks) (target := some name)
              (inlineExpsSource_rel cache code xs subset)
termination_by sizeOf expression
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack infrastructure: inlining a list preserves the pointwise
expression relation under the same cache inclusion. -/
theorem inlineExpsSource_rel (cache code : Spt (Nat × Bvi.Exp)) (expressions : List Bvi.Exp)
    (subset : sptSubspt cache code) : List.Forall₂ (ExpRel code) expressions (inlineExpsSource cache expressions) := by
  cases expressions with
  | nil => simp [inlineExpsSource]
  | cons e rest =>
    simpa [inlineExpsSource] using List.Forall₂.cons (inlineExpSource_rel cache code e subset)
      (inlineExpsSource_rel cache code rest subset)
termination_by sizeOf expressions
decreasing_by all_goals (simp_wf; omega)
end

/-- Flapjack infrastructure: a production inlining result satisfies the
expression relation when the code tree contains its wrapper cache. -/
theorem inlineExpBounded_rel (fuel : Nat) (cache code : Spt (Nat × Bvi.Exp)) (expression result : Bvi.Exp)
    (subset : sptSubspt cache code) (run : inlineExpBounded fuel cache expression = some result) :
    ExpRel code expression result := by
  rw [inlineExpBounded_eq_source] at run
  have same : inlineExpSource cache expression = result := Option.some.inj run
  rw [← same]
  exact inlineExpSource_rel cache code expression subset

end Flapjack.Compiler.Backend.BviInline
