import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.InstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original Alloc instruction-validity case with the complete source
hypotheses and actual compiler-output conclusion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstAlloc {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (destination : Nat) (cutsets : WordLangCutsetsHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.alloc destination cutsets : WordLangProgHOL (BitVec width))) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.alloc destination cutsets : WordLangProgHOL (BitVec width))) = true) :
    fullInstOkLessExact config (ssaCcTrans (.alloc destination cutsets : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  simp [ssaCcTrans, listNextVarRenameMove, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Install instruction-validity case with the complete source
hypotheses and actual compiler-output conclusion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstInstall {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (ptr len dptr dlen : Nat) (cutsets : WordLangCutsetsHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.install ptr len dptr dlen cutsets : WordLangProgHOL (BitVec width))) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.install ptr len dptr dlen cutsets : WordLangProgHOL (BitVec width))) = true) :
    fullInstOkLessExact config (ssaCcTrans (.install ptr len dptr dlen cutsets : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  simp [ssaCcTrans, listNextVarRenameMove, fullInstOkLessExact, fullInstOkLessWith]

/-- Original FFI instruction-validity case with the complete source
hypotheses and actual compiler-output conclusion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstFFI {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (index : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 : Nat) (cutsets : WordLangCutsetsHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.ffi index ptr len ptr2 len2 cutsets : WordLangProgHOL (BitVec width))) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.ffi index ptr len ptr2 len2 cutsets : WordLangProgHOL (BitVec width))) = true) :
    fullInstOkLessExact config (ssaCcTrans (.ffi index ptr len ptr2 len2 cutsets : WordLangProgHOL (BitVec width)) ssa next tables).1 = true := by
  simp [ssaCcTrans, listNextVarRenameMove, fullInstOkLessExact, fullInstOkLessWith]

end Flapjack.WordAlloc
