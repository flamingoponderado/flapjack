import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Shared statement for exact `ncompile_correct` case ports

This is Flapjack-specific proof organization: it bundles the exact evaluator,
compiler, and five source/target relations used by the HOL theorem's individual
constructor cases. It is not a standalone HOL declaration and is intentionally
untagged. Constructor case theorems carry the original `ncompile_correct`
reference.
-/

namespace Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

open Flapjack
open Flapjack.LoopSemStateFiniteExact

/-- The exact result translation in HOL `ncompile_correct`'s conclusion. -/
def resultToLoop {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → Option (LoopResultExact width)
  | none => none
  | some .error => some .error
  | some .timeOut => some .timeOut
  | some (.break label) => some (.break label)
  | some (.continue label) => some (.continue label)
  | some (.return values) => some (.result (values.map wlabWlocExact))
  | some (.exception value) => some (.exception (.word value))
  | some (.finalFfi event) => some (.finalFfi event)

/-- The result-dependent locals component of HOL `ncompile_correct`. -/
def localsResultRel {width : Nat} [NeZero width] {F : Type}
    (context : CrepToLoopContextExact) (live : NumSet)
    (result : Option (CrepResultHOLExact width))
    (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) : Prop :=
  match result with
  | none => crepToLoopLocalsRelExact context live source.locals target.locals
  | some (.break _) => crepToLoopLocalsRelExact context live source.locals target.locals
  | some (.continue _) => crepToLoopLocalsRelExact context live source.locals target.locals
  | some .error => False
  | _ => True

/-- Exact statement shape shared by the `ncompile_correct` constructor cases.
    The source/target evaluation is existential as in HOL, and no target run or
    result is assumed. -/
def Property {width : Nat} [NeZero width] {F : Type}
    (context : CrepToLoopContextExact) (live : NumSet)
    (program : CrepProgHOL width) : Prop :=
  ∀ (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F)
    (result : Option (CrepResultHOLExact width))
    (sourceFinal : CrepSemHOLState width F),
    evalCrepSemHOLProgExact source program = (result, sourceFinal) →
    result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact context source.code target.code →
    crepToLoopLocalsRelExact context live source.locals target.locals →
    ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
      (targetFinal : LoopSemStateFiniteExact width F),
      LoopSemStateFiniteExact.evaluate (compileHOLExact context live program)
        { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel context live result sourceFinal targetFinal

end Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
