import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveResources

/-! Compositional source event and resource monotonicity. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Flapjack induction property toward the source evaluator's event, stack,
and safety monotonicity theorems. It applies to the actual evaluator result. -/
def ResourceMono {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  state.ffi.ioEvents <+: (evaluate program state).2.ffi.ioEvents ∧
  BackendProps.optionLe state.stackMax (evaluate program state).2.stackMax ∧
  ((evaluate program state).2.safeForSpace = true → state.safeForSpace = true)

/-- Skipping preserves all three observations. -/
theorem resourceMono_skip {C F : Type} (state : State C F) : ResourceMono .skip state := by
  simp [ResourceMono, evaluate, BackendProps.optionLe_refl]

/-- A local move either preserves resource fields or reports a type error. -/
theorem resourceMono_move {C F : Type} (dest src : Nat) (state : State C F) :
    ResourceMono (.move dest src) state := by
  cases found : getVar src state.locals <;>
    simp [ResourceMono, evaluate, found, setVar, BackendProps.optionLe_refl]

/-- Clock exhaustion and decrement both leave resource observations intact. -/
theorem resourceMono_tick {C F : Type} (state : State C F) : ResourceMono .tick state := by
  by_cases zero : state.clock = 0 <;>
    simp [ResourceMono, evaluate, zero, flushState, decClock, BackendProps.optionLe_refl]

/-- Sequential source execution composes the three resource properties. -/
theorem resourceMono_seq {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (firstMono : ResourceMono first state)
    (secondMono : ∀ state : State C F, ResourceMono second state) :
    ResourceMono (.seq first second) state := by
  cases firstRun : evaluate first state with
  | mk result mid =>
    have firstFacts : state.ffi.ioEvents <+: mid.ffi.ioEvents ∧
        BackendProps.optionLe state.stackMax mid.stackMax ∧
        (mid.safeForSpace = true → state.safeForSpace = true) := by
      simpa [ResourceMono, firstRun] using firstMono
    cases result with
    | some result =>
      simpa [ResourceMono, evaluate, firstRun, fixClock] using firstFacts
    | none =>
      let clamped := { mid with clock := min state.clock mid.clock }
      have secondFacts := secondMono clamped
      have seqRun : evaluate (.seq first second) state = evaluate second clamped := by
        simp [evaluate, firstRun, fixClock, clamped]
      rw [ResourceMono, seqRun]
      refine ⟨?_, ?_, ?_⟩
      · exact List.IsPrefix.trans firstFacts.1 secondFacts.1
      · exact BackendProps.optionLe_trans _ _ _ ⟨firstFacts.2.1, secondFacts.2.1⟩
      · exact fun safe => firstFacts.2.2 (secondFacts.2.2 safe)

/-- A conditional inherits source resource monotonicity from either branch. -/
theorem resourceMono_if {C F : Type} (name : Nat) (yes no : DataLang.Prog) (state : State C F)
    (yesMono : ResourceMono yes state) (noMono : ResourceMono no state) :
    ResourceMono (.ifThenElse name yes no) state := by
  cases found : getVar name state.locals with
  | none => simp [ResourceMono, evaluate, found, BackendProps.optionLe_refl]
  | some value =>
    by_cases yes : isBool true value
    · simpa [ResourceMono, evaluate, found, yes] using yesMono
    · by_cases no : isBool false value
      · simpa [ResourceMono, evaluate, found, yes, no] using noMono
      · simp [ResourceMono, evaluate, found, yes, no, BackendProps.optionLe_refl]

/-- Source allocation bookkeeping itself satisfies the three properties,
including when cutting the environment fails. -/
theorem resourceMono_makeSpace {C F : Type} (amount : Nat) (names : NumSet) (state : State C F) :
    ResourceMono (.makeSpace amount names) state := by
  cases cut : cutEnv names state.locals with
  | none => simp [ResourceMono, evaluate, cut, BackendProps.optionLe_refl]
  | some env =>
    simp [ResourceMono, evaluate, cut, addSpace, BackendProps.optionLe_refl]
    tauto

end Flapjack.Compiler.Backend.DataSem
