import Flapjack.Compiler.Backend.BviInline.Proofs.SourceCorrespondence
import Mathlib.Data.List.Forall2

/-! Expression relation for BVI wrapper inlining. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

/-- Flapjack infrastructure: expression-level inlining relation. This is
untagged until its nested list and optional-handler carriers are reviewed
against the original inductive relation. -/
inductive ExpRel (code : Spt (Nat × Exp)) : Exp → Exp → Prop where
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
/-- Flapjack infrastructure: inlining an expression produces an expression
related under any code tree containing the cache. -/
theorem inlineExpSource_rel (cache code : Spt (Nat × Exp)) (expression : Exp)
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
theorem inlineExpsSource_rel (cache code : Spt (Nat × Exp)) (expressions : List Exp)
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
theorem inlineExpBounded_rel (fuel : Nat) (cache code : Spt (Nat × Exp)) (expression result : Exp)
    (subset : sptSubspt cache code) (run : inlineExpBounded fuel cache expression = some result) :
    ExpRel code expression result := by
  rw [inlineExpBounded_eq_source] at run
  have same : inlineExpSource cache expression = result := Option.some.inj run
  rw [← same]
  exact inlineExpSource_rel cache code expression subset

end Flapjack.Compiler.Backend.BviInline
