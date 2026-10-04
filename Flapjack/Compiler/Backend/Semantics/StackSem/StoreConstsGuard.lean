import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Misc.Sptree

namespace Flapjack.StackSemStoreConstsGuard

open Compiler.Backend.StackLang

/-- Flapjack structural decision procedure for the one code shape used by
the HOL optional StoreConsts stub guard. It never compares opaque payloads. -/
def isStoreConstsStub {width : Nat} [NeZero width] (t1 t2 : Nat) : HolProg width → Bool
  | .seq (.storeConsts a b none) (.ret 0) => decide (a = t1 ∧ b = t2)
  | _ => false

/-- Flapjack infrastructure: the structural decision procedure implements
actual program equality, without an equality-class assumption on word values. -/
theorem isStoreConstsStub_iff {width : Nat} [NeZero width] (t1 t2 : Nat) (program : HolProg width) :
    isStoreConstsStub t1 t2 program = true ↔
      program = .seq (.storeConsts t1 t2 none) (.ret 0) := by
  cases program <;> simp [isStoreConstsStub]
  case seq first second =>
    cases first <;> simp
    case storeConsts a b stub =>
      cases stub <;> cases second <;> simp
      case none.ret value =>
        cases value <;> simp [and_comm]

/-- Exact HOL optional stub guard. NONE bypasses lookup; SOME n requires
exactly Seq (StoreConsts t1 t2 NONE) (Return 0) at label n. The shared HOL
word dimension uses the reviewed positive-width HolProg carrier; code is an
sptree, not a finite map. This
proof-side prerequisite does not claim full evaluator or production routing. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def checkStoreConstsOpt {width : Nat} [NeZero width] (t1 t2 : Nat) (stub : Option Nat)
    (code : Spt (HolProg width)) : Bool :=
  match stub with
  | none => true
  | some label =>
      match sptLookup label code with
      | none => false
      | some program => isStoreConstsStub t1 t2 program

/-- Flapjack equality certificate for the SOME equation of the HOL guard. -/
theorem checkStoreConstsOpt_some_iff {width : Nat} [NeZero width] (t1 t2 label : Nat)
    (code : Spt (HolProg width)) :
    checkStoreConstsOpt t1 t2 (some label) code = true ↔
      sptLookup label code = some (.seq (.storeConsts t1 t2 none) (.ret 0)) := by
  cases h : sptLookup label code with
  | none => simp [checkStoreConstsOpt, h]
  | some program => simp [checkStoreConstsOpt, h, isStoreConstsStub_iff]

end Flapjack.StackSemStoreConstsGuard
