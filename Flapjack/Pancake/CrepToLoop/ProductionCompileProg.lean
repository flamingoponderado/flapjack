import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.PanToCrep.Compile

namespace Flapjack.CrepToLoopProduction
open Basis.Pure.MlString

/-- Exact whole-program input payload. Return-shape metadata has already been
consumed by Pan-to-Crep and is not an input of original compile_prog. -/
def sourcePrograms {width : Nat} [NeZero width]
    (functions : List (CompiledFunction (BitVec width))) :
    List (MlString × List Nat × CrepProgHOL width) :=
  functions.map fun function => (ofString function.name, function.params, crepProgToHOL function.body)

/-- The real production String-to-mlstring support boundary, including every
nested Call/ExtCall name. No unsupported name is silently converted. -/
def namesSupported {width : Nat} (functions : List (CompiledFunction (BitVec width))) : Bool :=
  functions.all fun function => CrepNameRangedBool function.name && CrepProgNameRangedBool function.body

/-- Complete native whole-program producer for the RISC-V source lane. It
invokes original compile_prog once and retains all original 64+n row names,
direct calls, live sets and native Loop bodies. Rejected names return none;
there is no legacy-label fallback or rebase. This untagged callable producer
is Flapjack infrastructure, not a duplicate HOL declaration or a claim that
CLI/downstream entry, stub and runtime consumers are already connected. -/
def compileProgFromProduction? {width : Nat} [NeZero width]
    (functions : List (CompiledFunction (BitVec width))) :
    Option (List (Nat × List Nat × HolLoopProg width)) :=
  if namesSupported functions then some (compileProgHOLExact .riscv (sourcePrograms functions)) else none

theorem namesSupported_iff {width : Nat}
    (functions : List (CompiledFunction (BitVec width))) :
    namesSupported functions = true ↔
      (∀ function ∈ functions, CrepNameRanged function.name) ∧
      (∀ function ∈ functions, CrepProgNameRanged function.body) := by
  simp only [namesSupported, List.all_eq_true, Bool.and_eq_true,
    crepNameRangedBool_eq_true_iff, crepProgNameRangedBool_eq_true_iff]
  constructor
  · intro h
    exact ⟨fun f hf => (h f hf).1, fun f hf => (h f hf).2⟩
  · rintro ⟨hn, hb⟩ f hf
    exact ⟨hn f hf, hb f hf⟩

/-- Only the supported source-name conditions are premises. The complete
original native result is derived, with no result/run/context callback. -/
theorem compileProgFromProduction_supported {width : Nat} [NeZero width]
    (functions : List (CompiledFunction (BitVec width)))
    (names : ∀ function ∈ functions, CrepNameRanged function.name)
    (bodies : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    compileProgFromProduction? functions =
      some (compileProgHOLExact .riscv (sourcePrograms functions)) := by
  simp [compileProgFromProduction?, (namesSupported_iff functions).mpr ⟨names, bodies⟩]

/-- Successful producer calls derive both complete original output and every
source carrier boundary. This describes the actual API, not a HOL correctness
port with an added successful-pass hypothesis. -/
theorem compileProgFromProduction_result {width : Nat} [NeZero width]
    (functions : List (CompiledFunction (BitVec width)))
    (output : List (Nat × List Nat × HolLoopProg width))
    (produced : compileProgFromProduction? functions = some output) :
    (∀ function ∈ functions, CrepNameRanged function.name) ∧
    (∀ function ∈ functions, CrepProgNameRanged function.body) ∧
    output = compileProgHOLExact .riscv (sourcePrograms functions) := by
  unfold compileProgFromProduction? at produced
  split at produced
  · rename_i supported
    have boundaries := (namesSupported_iff functions).mp supported
    exact ⟨boundaries.1, boundaries.2, (Option.some.inj produced).symm⟩
  · contradiction

/-- Every original compile_prog input field roundtrips on the declared source
boundary. Return-shape metadata is deliberately not part of this payload. -/
theorem sourcePrograms_roundTrip {width : Nat} [NeZero width]
    (functions : List (CompiledFunction (BitVec width)))
    (names : ∀ function ∈ functions, CrepNameRanged function.name)
    (bodies : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    (sourcePrograms functions).map (fun (name, params, body) =>
      (toStringOfBytes name, params, crepProgOfHOL body)) =
      functions.map (fun function => (function.name, function.params, function.body)) := by
  simp only [sourcePrograms, List.map_map]
  apply List.map_congr_left
  intro function member
  simp only [Function.comp_apply]
  rw [toStringOfBytes_ofString_of_bytes function.name (names function member),
    crepProgOfHOL_crepProgToHOL function.body (bodies function member)]

private theorem zipWith_rowNames {α β : Type}
    (labels : List Nat) (inputs : List α) (compile : Nat → α → β)
    (lengths : labels.length = inputs.length) :
    (List.zipWith (fun name input => (name, compile name input)) labels inputs).map Prod.fst = labels := by
  induction labels generalizing inputs with
  | nil => simp
  | cons label labels ih =>
    cases inputs with
    | nil => simp at lengths
    | cons input inputs =>
      simp only [List.zipWith_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using lengths)

/-- All original row names, for arbitrary supported input programs. There is
no legacy label base and no input/output-code-table assumption. -/
theorem compileProgFromProduction_rowNames {width : Nat} [NeZero width]
    (functions : List (CompiledFunction (BitVec width)))
    (names : ∀ function ∈ functions, CrepNameRanged function.name)
    (bodies : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    (compileProgFromProduction? functions).map (List.map Prod.fst) =
      some ((List.range functions.length).map (fun n => n + firstLoopName)) := by
  rw [compileProgFromProduction_supported functions names bodies]
  simp only [Option.map_some, compileProgHOLExact]
  rw [zipWith_rowNames]
  · simp [sourcePrograms]
  · simp

end Flapjack.CrepToLoopProduction
