import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineStateRel
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call

/-! Call-lookup and clock prerequisites for the BVL inlining simulation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open BvlSem

/-- A shared clock decrement preserves the inlining relation. This is a
Flapjack helper extracted from the original evaluator proof, not a separate
HOL declaration. -/
theorem inStateRel_decClock {C F : Type} (limit n : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) :
    inStateRel limit (decClock n source) (decClock n target) := by
  simpa [inStateRel, decClock, related.2.2.1] using related

/-- Successful direct or indirect lookup in the source has the same argument
selection and a related body in the inlined target. This helper is extracted
from the original evaluator proof and has no standalone HOL declaration. -/
theorem inStateRel_findCode {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) (dest : Option Nat)
    (args output : List Value) (body : Bvl.Exp)
    (run : findCode dest args source.code = some (output, body)) :
    ∃ body', findCode dest args target.code = some (output, body') ∧
      ExpRel source.code [body] [body'] := by
  have codeRel := related.2.2.2.2.2.2.2.2
  cases dest with
  | some name =>
    cases lookup : sptLookup name source.code with
    | none => simp [findCode, lookup] at run
    | some entry =>
      obtain ⟨arity, original⟩ := entry
      by_cases arityEq : args.length = arity
      · simp [findCode, lookup, arityEq] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨body', found, bodyRel⟩ := codeRel name arity original lookup
        exact ⟨body', by simp [findCode, found, arityEq], bodyRel⟩
      · simp [findCode, lookup, arityEq] at run
  | none =>
    cases args with
    | nil => simp [findCode] at run
    | cons first rest =>
      cases last : Flapjack.holLast (first :: rest) with
      | codePtr name =>
        cases lookup : sptLookup name source.code with
        | none => simp [findCode, last, lookup] at run
        | some entry =>
          obtain ⟨arity, original⟩ := entry
          by_cases arityEq : rest.length = arity
          · simp [findCode, last, lookup, arityEq] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨body', found, bodyRel⟩ := codeRel name arity original lookup
            exact ⟨body', by simp [findCode, last, found, arityEq], bodyRel⟩
          · simp [findCode, last, lookup, arityEq] at run
      | number n => simp [findCode, last] at run
      | word64 w => simp [findCode, last] at run
      | block tag fields => simp [findCode, last] at run
      | refPtr thunk index => simp [findCode, last] at run

end Flapjack.Compiler.Backend.BvlInline.Proofs
