import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Misc.ShiftSeq

/-! Dynamic installation in the proof-side closure semantics. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Decode a list of integer-encoded byte words. The choice is unique but
this operation remains untagged until source and carrier review is complete. -/
noncomputable def valueToBytes (value : Value) : Option (List (BitVec 8)) := by
  classical
  exact if h : ∃ bytes, valueToList value = some (bytes.map (fun b => .number b.toNat)) then
    some (Classical.choose h) else none

/-- Decode a list of 64-bit words. -/
noncomputable def valueToWords (value : Value) : Option (List (BitVec 64)) := by
  classical
  exact if h : ∃ words, valueToList value = some (words.map Value.word64) then
    some (Classical.choose h) else none

private theorem listMap_injective {α β : Type} (f : α → β) (injective : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro xs ys equal
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at equal
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at equal
      simp [injective equal.1, ih equal.2]

private theorem uniqueChoice_eq_some {α : Type} (P : α → Prop)
    (unique : ∀ x y, P x → P y → x = y) (value : α) :
    (by classical exact if h : ∃ x, P x then some (Classical.choose h) else none) = some value ↔ P value := by
  classical
  by_cases existsValue : ∃ x, P x
  · simp only [existsValue, dif_pos, Option.some.injEq]
    constructor
    · intro same
      rw [← same]
      exact Classical.choose_spec existsValue
    · intro valid
      exact unique _ _ (Classical.choose_spec existsValue) valid
  · simp [existsValue]
    intro valid
    exact existsValue ⟨value, valid⟩

/-- The closure byte decoder succeeds exactly for its encoded byte list. -/
theorem valueToBytes_eq_some (value : Value) (bytes : List (BitVec 8)) :
    valueToBytes value = some bytes ↔
      valueToList value = some (bytes.map (fun b => .number b.toNat)) := by
  classical
  apply uniqueChoice_eq_some
  intro xs ys hx hy
  apply listMap_injective (fun b : BitVec 8 => Value.number b.toNat)
  · intro x y equal
    injection equal with same
    apply BitVec.eq_of_toNat_eq
    exact Int.ofNat.inj same
  · exact Option.some.inj (hx.symm.trans hy)

/-- The closure word decoder succeeds exactly for its encoded word list. -/
theorem valueToWords_eq_some (value : Value) (words : List (BitVec 64)) :
    valueToWords value = some words ↔ valueToList value = some (words.map Value.word64) := by
  classical
  apply uniqueChoice_eq_some
  intro xs ys hx hy
  apply listMap_injective Value.word64
  · intro x y equal
    cases equal
    rfl
  · exact Option.some.inj (hx.symm.trans hy)

/-- Validate compiler output and install the new code and shifted oracle.
Invalid input leaves the state unchanged; a valid installation updates state
even when its clock is zero and the result is timeout. This proof-side model
is untagged pending finite-map, decoder, and evaluator correspondence review. -/
noncomputable def doInstall {C F : Type} (values : List Value) (state : State C F) :
    Result (List ClosLang.Exp) Value × State C F := by
  classical
  let error : Result (List ClosLang.Exp) Value × State C F := (.err (.abort .typeError), state)
  exact match values with
    | [bytesValue, wordsValue] =>
      match valueToBytes bytesValue, valueToWords wordsValue with
      | some bytes, some words =>
        let (config, expressions, auxiliary) := state.compileOracle 0
        let newOracle := Flapjack.holShiftSeq 1 state.compileOracle
        if (∀ index ∈ auxiliary.map Prod.fst, state.code.lookup index = none) ∧
            (auxiliary.map Prod.fst).Nodup then
          match state.compile config (expressions, auxiliary) with
          | some (compiledBytes, compiledWords, nextConfig) =>
            if bytes = compiledBytes ∧ words = compiledWords ∧
                (newOracle 0).1 = nextConfig ∧ expressions ≠ [] then
              let next := { state with
                code := state.code.updateListEq auxiliary
                compileOracle := newOracle
                clock := state.clock - 1 }
              if state.clock = 0 then (.err (.abort .timeoutError), next) else (.val expressions, next)
            else error
          | none => error
        else error
      | _, _ => error
    | _ => error

/-- An installation request with any arity other than two returns a type
error and leaves the state unchanged. -/
theorem doInstall_wrongArity {C F : Type} (values : List Value) (state : State C F)
    (arity : values.length ≠ 2) :
    doInstall values state = (.err (.abort .typeError), state) := by
  cases values with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons second rest =>
      cases rest with
      | nil => simp at arity
      | cons third rest => rfl

/-- Installation never increases the clock, including the valid-install
timeout path that updates the code and oracle. This proof-side lemma has not
yet been reviewed against the HOL theorem and finite-map representation. -/
theorem doInstall_clock_le {C F : Type} (values : List Value) (state next : State C F)
    (result : Result (List ClosLang.Exp) Value) (run : doInstall values state = (result, next)) :
    next.clock ≤ state.clock := by
  classical
  unfold doInstall at run
  repeat' first | split at run | simp_all
  all_goals try simp_all
  all_goals cases run.2
  all_goals simp only
  all_goals omega

/-- A successful installation consumes exactly one unit of positive clock. -/
theorem doInstall_success_clock {C F : Type} (values : List Value) (state next : State C F)
    (expressions : List ClosLang.Exp) (run : doInstall values state = (.val expressions, next)) :
    0 < state.clock ∧ next.clock = state.clock - 1 := by
  classical
  unfold doInstall at run
  repeat' first | split at run | simp_all
  all_goals try simp_all
  all_goals cases run.2
  all_goals simp only
  all_goals simp only [and_true]
  all_goals omega

end Flapjack.Compiler.Backend.ClosSem
