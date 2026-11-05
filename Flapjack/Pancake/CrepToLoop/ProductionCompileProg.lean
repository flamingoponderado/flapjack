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

end Flapjack.CrepToLoopProduction
