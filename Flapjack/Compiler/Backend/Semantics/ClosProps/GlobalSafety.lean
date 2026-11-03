import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Compiler.Backend.Semantics.ClosSem.State

/-! Closure-language value, result, and state global-write safety. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem
open FlatProps (emptyGlobalBag)

/-- Captured closures and nested values do not contain global-writing bodies. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "vsgc_free_def" 1800]
def vsgcFree : Value → Prop
  | .block _ values => ∀ value ∈ values, vsgcFree value
  | .closure _ args env _ body =>
      setGlobals body = emptyGlobalBag ∧
        (∀ value ∈ args, vsgcFree value) ∧ (∀ value ∈ env, vsgcFree value)
  | .recclosure _ args env bodies _ =>
      elistGlobals (bodies.map Prod.snd) = emptyGlobalBag ∧
        (∀ value ∈ args, vsgcFree value) ∧ (∀ value ∈ env, vsgcFree value)
  | _ => True
termination_by value => sizeOf value
decreasing_by all_goals have := List.sizeOf_lt_of_mem ‹_›; simp_wf; omega

/-- A result is safe if its returned or raised values are safe. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "rsgc_free_def"]
def rsgcFree : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value → Prop
  | .val values => ∀ value ∈ values, vsgcFree value
  | .err (.abort _) => True
  | .err (.raise value) => vsgcFree value

/-- Unit is free of global-writing closures. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "vsgc_free_Unit"]
theorem vsgcFreeUnit : vsgcFree unitValue := by simp [unitValue, vsgcFree]

/-- Both closure-language Boolean values are safe. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "vsgc_free_Boolv"]
theorem vsgcFreeBool (b : Bool) : vsgcFree (boolValue b) := by simp [boolValue, vsgcFree]

namespace StateGlobalSafety
/-- Canonical finite-map state and its broad view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Code, references, globals and future compiler programs are safe. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "ssgc_free_def"
  (fmap_as_finite_support := [refs, code])]
def ssgcFree {C F : Type} (s : State C F) : Prop :=
  (∀ n arity body, s.code.lookup n = some (arity, body) → setGlobals body = emptyGlobalBag) ∧
  (∀ n values, s.refs.lookup n = some (.valueArray values) → ∀ value ∈ values, vsgcFree value) ∧
  (∀ n mode value, s.refs.lookup n = some (.thunk mode value) → vsgcFree value) ∧
  (∀ value, some value ∈ s.globals → vsgcFree value) ∧
  (∀ n expressions aux, (s.compileOracle n).2 = (expressions, aux) →
    (∀ e ∈ expressions, esgcFree e) ∧ elistGlobals (aux.map (fun entry => entry.2.2)) = emptyGlobalBag)

/-- Updating the clock does not affect state global-write safety. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "ssgc_free_clockupd"
  (fmap_as_finite_support := [refs, code])]
theorem ssgcFreeClock {C F : Type} (s : State C F) (f : Nat → Nat) :
    ssgcFree {s with clock := f s.clock} ↔ ssgcFree s := Iff.rfl

/-- Decrementing the clock preserves state global-write safety. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "ssgc_free_dec_clock"
  (fmap_as_finite_support := [refs, code])]
theorem ssgcFreeDecClock {C F : Type} (n : Nat) (s : State C F) :
    ssgcFree (decClock n s) ↔ ssgcFree s := Iff.rfl

end StateGlobalSafety
end Flapjack.Compiler.Backend.ClosProps
