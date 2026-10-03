import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Install
namespace Flapjack.Test.StackRawCallInstallParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.InstallCase

example {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    SimulationResult (comp info (.install ptr len dptr dlen ret)) info target post result :=
  compCorrectInstall ptr len dptr dlen ret info source target post result hypothesis

example {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    SimulationResult (comp info (.install ptr len dptr dlen ret)) info target post result :=
  compCorrectInstall ptr len dptr dlen ret info source target post result hypothesis

example {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    SimulationResult (comp info (.install ptr len dptr dlen ret)) info target post result :=
  compCorrectInstall ptr len dptr dlen ret info source target post result hypothesis

example {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    SimulationResult (comp info (.install ptr len dptr dlen ret)) info target post result :=
  compCorrectInstall ptr len dptr dlen ret info source target post result hypothesis

example {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    SimulationResult (comp info (.install ptr len dptr dlen ret)) info target post result :=
  compCorrectInstall ptr len dptr dlen ret info source target post result hypothesis

-- Independent original-HOL union observations: collisions retain old entries,
-- while keys absent from the old tree expose the installed entry.
example : sptLookup 0 (sptUnion (.ls 7) (.ls 9)) = some (7 : Nat) := by simp [sptLookup_sptUnion, sptLookup]
example : sptLookup 0 (sptUnion (.ls 7) (.ls 9)) = some (7 : Nat) := by native_decide
example : sptLookup 2 (sptUnion (sptFromAList [(0, 7)])
    (sptFromAList [(2, 9)])) = some (9 : Nat) := by simp [sptLookup_sptUnion, sptLookup_sptFromAList, sptAListLookup]
example : sptLookup 2 (sptUnion (sptFromAList [(0, 7)])
    (sptFromAList [(2, 9)])) = some (9 : Nat) := by native_decide
end Flapjack.Test.StackRawCallInstallParity
