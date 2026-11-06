import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions
import Flapjack.Misc.ShiftSeq

/-! Clock and dynamic-compilation helpers for the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem

/-- Apply a flat expression to unit, as used when forcing a thunk. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "AppUnit_def"]
def appUnit (expr : FlatLang.Exp) : FlatLang.Exp :=
  .app .none (.src .opapp) [expr, .con .none none []]

/-- Decrement the evaluator clock with natural-number subtraction. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "dec_clock_def"]
def decClock {C F : Type} (state : State C F) : State C F :=
  { state with clock := state.clock - 1 }

/-- Clamp an evaluation result's clock to the incoming clock. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "fix_clock_def"]
def fixClock {C F D E α : Type} (state : State C F) (result : State D E × α) : State D E × α :=
  ({ result.1 with clock := min state.clock result.1.clock }, result.2)

/-- A fixed result clock never exceeds the incoming clock. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "fix_clock_IMP"]
theorem fixClock_imp {C F D E α : Type} (state : State C F) (next : State D E) (result : α)
    (pair : State D E × α) (evaluated : fixClock state pair = (next, result)) :
    next.clock ≤ state.clock := by
  have clockEq := congrArg (fun p : State D E × α => p.1.clock) evaluated
  simp only [fixClock] at clockEq
  rw [← clockEq]
  exact Nat.min_le_left _ _

/-- Decode the unique byte sequence represented by a flat list. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "v_to_bytes_def"]
noncomputable def valueToBytes (value : Value) : Option (List (BitVec 8)) := by
  classical
  exact if h : ∃ bytes, valueToList value = some (bytes.map (Value.litv ∘ AstHOL.Lit.word8)) then
    some (Classical.choose h) else none

/-- Decode the unique 64-bit word sequence represented by a flat list. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "v_to_words_def"]
noncomputable def valueToWords (value : Value) : Option (List (BitVec 64)) := by
  classical
  exact if h : ∃ words, valueToList value = some (words.map (Value.litv ∘ AstHOL.Lit.word64)) then
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
      have sameHead := injective equal.1
      have sameTail := ih equal.2
      simp [sameHead, sameTail]

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

/-- Flapjack infrastructure: decoding succeeds exactly for the uniquely
represented byte list. -/
theorem valueToBytes_eq_some (value : Value) (bytes : List (BitVec 8)) :
    valueToBytes value = some bytes ↔
      valueToList value = some (bytes.map (Value.litv ∘ AstHOL.Lit.word8)) := by
  classical
  apply uniqueChoice_eq_some
  intro xs ys hx hy
  apply listMap_injective (Value.litv ∘ AstHOL.Lit.word8)
  · intro x y equal
    cases equal
    rfl
  · exact Option.some.inj (hx.symm.trans hy)

/-- Flapjack infrastructure: decoding succeeds exactly for the uniquely
represented word list. -/
theorem valueToWords_eq_some (value : Value) (words : List (BitVec 64)) :
    valueToWords value = some words ↔
      valueToList value = some (words.map (Value.litv ∘ AstHOL.Lit.word64)) := by
  classical
  apply uniqueChoice_eq_some
  intro xs ys hx hy
  apply listMap_injective (Value.litv ∘ AstHOL.Lit.word64)
  · intro x y equal
    cases equal
    rfl
  · exact Option.some.inj (hx.symm.trans hy)

/-- Check the compiler oracle and install a nonempty compiled declaration list. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_eval_def"]
noncomputable def doEval {C : Type} (values : List Value) (config : InstallConfig C) :
    Option (List FlatLang.Exp × InstallConfig C × Value) := by
  classical
  exact match values with
    | [bytesValue, wordsValue] =>
      match valueToBytes bytesValue, valueToWords wordsValue with
      | some bytes, some words =>
        let (compilerState, decs) := config.compileOracle 0
        let nextOracle := holShiftSeq 1 config.compileOracle
        match config.compile compilerState decs with
        | some (compiledBytes, compiledWords, nextState) =>
          if bytes = compiledBytes ∧ words = compiledWords ∧ decs ≠ [] ∧
              (nextOracle 0).1 = nextState then
            some (decs, { config with compileOracle := nextOracle }, unitValue)
          else none
        | none => none
      | _, _ => none
    | _ => none

end Flapjack.Compiler.Backend.FlatSem
