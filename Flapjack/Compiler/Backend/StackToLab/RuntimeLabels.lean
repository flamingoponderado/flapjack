import Flapjack.Pancake.CrepToLoop
import Flapjack.Compiler.Backend.StackToLab.InitializedProduction

/-! Flapjack production namespace translation. There is no HOL declaration:
the legacy executed runtime reserves Raise0/StoreConsts1/GC2 and begins source
functions at3; the original whole initializer reserves Init0/Halt1/Halt2 and
uses canonical GC4/Raise5/StoreConsts6 with source functions beginning at64.
The numeric suffixes in exported makesym symbols are section ordinals, not
these global code names. Only global
section names are translated. Registers, local labels, loop depths, words and
byte-observable names retain their original carriers and values.
-/
namespace Flapjack.Compiler.Backend.StackToLab.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend.StackLang

def originalSection (label : Nat) : Nat :=
  match label with
  | 0 => Flapjack.raiseStubLocation
  | 1 => Flapjack.storeConstsStubLocation
  | 2 => Flapjack.Compiler.Backend.StackLang.gcStubLocation
  | other => other + (Flapjack.firstLoopName - 3)

def legacySection (label : Nat) : Nat :=
  if Flapjack.firstLoopName ≤ label then label - (Flapjack.firstLoopName - 3)
  else match label with
    | 4 => 2
    | 5 => 0
    | 6 => 1
    | _ => 0

/-- Every legacy section has a distinct original global name. -/
theorem legacy_original (label : Nat) : legacySection (originalSection label) = label := by
  cases label with
  | zero => rfl
  | succ label => cases label with
    | zero => rfl
    | succ label => cases label with
      | zero => rfl
      | succ label =>
        have bound : Flapjack.firstLoopName ≤ (label + 3) + (Flapjack.firstLoopName - 3) := by
          simp only [Flapjack.firstLoopName]
          omega
        change legacySection ((label + 3) + (Flapjack.firstLoopName - 3)) = label + 3
        rw [legacySection, if_pos bound] <;>
          simp only [Flapjack.firstLoopName] at * <;> omega

/-- Translate every global label-bearing constructor, recursively including
both call continuations. Break/Continue payloads are loop depths, not globals. -/
def mapGlobals {width : Nat} [NeZero width] (rename : Nat → Nat)
    (program : HolProg width) : HolProg width :=
  match program with
  | .seq first second => .seq (mapGlobals rename first) (mapGlobals rename second)
  | .ite cmp reg imm first second =>
      .ite cmp reg imm (mapGlobals rename first) (mapGlobals rename second)
  | .loop body => .loop (mapGlobals rename body)
  | .call returns target handler =>
      .call (match returns with
        | none => none
        | some (body, register, sectionId, localLabel) =>
            some (mapGlobals rename body, register, rename sectionId, localLabel))
        (match target with | .inl label => .inl (rename label) | .inr reg => .inr reg)
        (match handler with
        | none => none
        | some (body, sectionId, localLabel) =>
            some (mapGlobals rename body, rename sectionId, localLabel))
  | .jumpLower left right target => .jumpLower left right (rename target)
  | .storeConsts source bitmap stub => .storeConsts source bitmap (stub.map rename)
  | .locValue reg sectionId localLabel => .locValue reg (rename sectionId) localLabel
  | .rawCall target => .rawCall (rename target)
  | other => other
termination_by sizeOf program

/-- Global renaming is reversible on every constructor and both optional call
bodies. This is production representation infrastructure, not HOL simulation. -/
theorem mapGlobals_inverse {width : Nat} [NeZero width] (rename undo : Nat → Nat)
    (cancel : ∀ label, undo (rename label) = label) (program : HolProg width) :
    mapGlobals undo (mapGlobals rename program) = program := by
  induction program using mapGlobals.induct <;>
    try simp_all [mapGlobals, Option.map_map]
  case case4 returns target handler ihReturns ihHandler =>
    rcases returns with _ | ⟨body, register, sectionId, localLabel⟩ <;>
      rcases handler with _ | ⟨handlerBody, handlerSection, handlerLocal⟩ <;>
      cases target <;> simp_all [mapGlobals]
  case case6 source bitmap stub =>
    cases stub <;> simp_all [Function.comp_def]

/-- Complete native input normalization prior to inserting the original stubs. -/
def originalInputs {width : Nat} [NeZero width] (programs : List (Nat × HolProg width)) :
    List (Nat × HolProg width) :=
  programs.map (fun entry => (originalSection entry.1, mapGlobals originalSection entry.2))

end Flapjack.Compiler.Backend.StackToLab.RuntimeLabels
