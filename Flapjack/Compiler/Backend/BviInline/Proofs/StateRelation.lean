import Flapjack.Compiler.Backend.BviInline.Proofs.InlineCall
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! State relation for the BVI inlining pass. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem BackendProps

/-- Flapjack infrastructure: the inliner's source-shaped compiler adapter. -/
def inCc {C : Type} (compiler : BviSem.Compiler C) : BviSem.Compiler (Spt (Nat × Bvi.Exp) × C) :=
  stateCc inlineAllSource compiler

/-- Flapjack infrastructure: transform each future code segment with its
cached wrappers. -/
def inCo {C : Type} (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C)) : BviSem.CompileOracle C :=
  stateCo inlineAllSource oracle

/-- Flapjack infrastructure: source and target states for BVI inlining. This
source-shaped relation remains untagged pending HOL carrier review. -/
def InStateRel {C F : Type} (source : BviState (Spt (Nat × Bvi.Exp) × C) F) (target : BviState C F) : Prop :=
  target.refs = source.refs ∧ target.clock = source.clock ∧ target.global = source.global ∧
  target.ffi = source.ffi ∧ target.compileOracle = inCo source.compileOracle ∧
  sptSubspt (source.compileOracle 0).1.1 target.code ∧ source.compile = inCc target.compile ∧
  sptDomain target.code = sptDomain source.code ∧
  ∀ key arity body, sptLookup key source.code = some (arity, body) →
    ∃ transformed, sptLookup key target.code = some (arity, transformed) ∧ ExpRel target.code body transformed

/-- Flapjack infrastructure: equal clock replacement preserves the inliner
state relation. -/
theorem inStateRel_with_clock {C F : Type} (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (target : BviState C F) (states : InStateRel source target) (clock : Nat) :
    InStateRel { source with clock := clock } { target with clock := clock } := by
  exact ⟨states.1, rfl, states.2.2⟩

/-- Flapjack infrastructure: equal decrements preserve the inliner state
relation. -/
theorem inStateRel_decClock {C F : Type} (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (target : BviState C F) (states : InStateRel source target) (ticks : Nat) :
    InStateRel (BviSem.decClock ticks source) (BviSem.decClock ticks target) := by
  simpa [BviSem.decClock, states.2.1] using inStateRel_with_clock source target states (source.clock - ticks)

/-- Flapjack infrastructure: an inliner-related state has the same clock and
observable FFI state as its source. -/
theorem inStateRel_observables {C F : Type} (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (target : BviState C F) (states : InStateRel source target) :
    target.clock = source.clock ∧ target.ffi = source.ffi := ⟨states.2.1, states.2.2.2.1⟩

/-- Flapjack infrastructure: both direct and indirect code lookup preserve
arguments and select related bodies under the inliner state relation. -/
theorem findCode_inStateRel {C F : Type} (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (target : BviState C F) (destination : Option Nat) (values args : List Value) (body : Bvi.Exp)
    (states : InStateRel source target) (found : findCode destination values source.code = some (args, body)) :
    ∃ transformed, findCode destination values target.code = some (args, transformed) ∧
      ExpRel target.code body transformed := by
  have codeRel := states.2.2.2.2.2.2.2.2
  cases destination with
  | some name =>
    simp only [findCode] at found ⊢
    cases lookup : sptLookup name source.code with
    | none => simp [lookup] at found
    | some entry =>
      obtain ⟨arity, sourceBody⟩ := entry
      by_cases length : values.length = arity
      · simp [lookup, length] at found
        obtain ⟨rfl, rfl⟩ := found.symm
        obtain ⟨transformed, targetLookup, related⟩ := codeRel name arity sourceBody lookup
        exact ⟨transformed, by simp [targetLookup, length], related⟩
      · simp [lookup, length] at found
  | none =>
    simp only [findCode] at found ⊢
    by_cases empty : values.isEmpty = true
    · simp [empty] at found
    · simp only [empty, Bool.false_eq_true, ↓reduceIte] at found ⊢
      cases last : Flapjack.holLast values with
      | codePtr name =>
        cases lookup : sptLookup name source.code with
        | none => simp [last, lookup] at found
        | some entry =>
          obtain ⟨arity, sourceBody⟩ := entry
          by_cases length : values.length = arity + 1
          · simp [last, lookup, length] at found
            obtain ⟨rfl, rfl⟩ := found.symm
            obtain ⟨transformed, targetLookup, related⟩ := codeRel name arity sourceBody lookup
            exact ⟨transformed, by simp [targetLookup, length], related⟩
          · simp [last, lookup, length] at found
      | _ => simp [last] at found

end Flapjack.Compiler.Backend.BviInline
