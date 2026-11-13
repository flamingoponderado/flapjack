module

public import Flapjack.Compiler.Backend.BviInline.Proofs.InlineCall
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

@[expose] public section

/-! State relation for the BVI inlining pass. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem BackendProps

/-- Thread the inlining cache through a downstream compiler callback. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "in_cc_def"]
def inCc {C CNext Code Data : Type}
    (compiler : C → List (Nat × Nat × Bvi.Exp) → Option (Code × Data × CNext)) :
    Spt (Nat × Bvi.Exp) × C → List (Nat × Nat × Bvi.Exp) →
      Option (Code × Data × Spt (Nat × Bvi.Exp) × CNext) :=
  stateCc inlineAllSource compiler

/-- Transform each future code segment using its stored wrapper cache. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "in_co_def"]
def inCo {Index C : Type}
    (oracle : Index → (Spt (Nat × Bvi.Exp) × C) × List (Nat × Nat × Bvi.Exp)) :
    Index → C × List (Nat × Nat × Bvi.Exp) :=
  stateCo inlineAllSource oracle

/-- The inlining compiler adapter is the generic state compiler adapter. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "in_cc_eq_state_cc"]
theorem inCcEqStateCc {C CNext Code Data : Type}
    (compiler : C → List (Nat × Nat × Bvi.Exp) → Option (Code × Data × CNext)) :
    inCc compiler = stateCc inlineAllSource compiler := rfl

/-- The inlining oracle adapter is the generic state oracle adapter. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "in_co_eq_state_co"]
theorem inCoEqStateCo {Index C : Type}
    (oracle : Index → (Spt (Nat × Bvi.Exp) × C) × List (Nat × Nat × Bvi.Exp)) :
    inCo oracle = stateCo inlineAllSource oracle := rfl

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
