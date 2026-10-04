import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.InstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original Skip case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstSkip {width : Nat} [NeZero width]
    (config : AsmConfigExact width)

    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.skip) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.skip)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.skip) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Move case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstMove {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (priority : Nat) (moves : List (Nat × Nat))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.move priority moves) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.move priority moves)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.move priority moves) ssa next tables).1 = true := by
  generalize produced : listNextVarRename (moves.map Prod.fst) ssa next = result
  rcases result with ⟨names, map, counter⟩
  simp [ssaCcTrans, produced, fullInstOkLessExact, fullInstOkLessWith]

/-- Original StoreConsts case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstStoreConsts {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (a b c d : Nat) (ws : List (Bool × BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.storeConsts a b c d ws) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.storeConsts a b c d ws)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.storeConsts a b c d ws) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Assign case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstAssign {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (name : Nat) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.assign name exp) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.assign name exp)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.assign name exp) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Get case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstGet {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (name : Nat) (store : WordStoreHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.get name store) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.get name store)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.get name store) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Store case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstStore {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (exp : WordLangExpHOL (BitVec width)) (name : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.store exp name) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.store exp name)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.store exp name) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Raise case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstRaise {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (name : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.raise name) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.raise name)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.raise name) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original OpCurrHeap case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstOpCurrHeap {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (op : BinOp) (dst src : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.opCurrHeap op dst src) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.opCurrHeap op dst src)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.opCurrHeap op dst src) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith, HolInst.ofWordLangInst, instOkLessExact]

/-- Original Return case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstReturn {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (label : Nat) (values : List Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.return label values) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.return label values)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.return label values) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Tick case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstTick {width : Nat} [NeZero width]
    (config : AsmConfigExact width)

    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.tick) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.tick)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.tick) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original Set case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstSet {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (store : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.set store exp) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.set store exp)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.set store exp) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original LocValue case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstLocValue {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (dst src : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.locValue dst src) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.locValue dst src)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.locValue dst src) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original CodeBufferWrite case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstCodeBufferWrite {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (addr value : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.codeBufferWrite addr value) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.codeBufferWrite addr value)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.codeBufferWrite addr value) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

/-- Original DataBufferWrite case with the original allocation-class/map hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstDataBufferWrite {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (addr value : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : everyVarHOL (fun x => decide (x < next)) ((.dataBufferWrite addr value) : WordLangProgHOL (BitVec width)) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config ((.dataBufferWrite addr value)) = true) :
    fullInstOkLessExact config (ssaCcTrans (.dataBufferWrite addr value) ssa next tables).1 = true := by
  simp [ssaCcTrans, fullInstOkLessExact, fullInstOkLessWith]

end Flapjack.WordAlloc
