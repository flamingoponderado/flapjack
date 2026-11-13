module

public import Flapjack.Compiler.Encoders.Arm8.ArithLemmas
public import Flapjack.Compiler.Encoders.MemBytes
public import Flapjack.Compiler.Encoders.AsmSem
public import Flapjack.Compiler.Encoders.AsmSem.Step
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Shared ARMv8 memory lemmas

Carrier-independent facts used by both the closed ARMv8 machine model
(`Machine/`) and the L3 ARMv8 encoder-correctness chain
(`L3/CorrectnessEncoding/`).  They mention only `AsmState` (the source
semantics) and a plain memory map `BitVec 64 → BitVec 8`, so they live here
rather than being copied into both trees.

`writeMemBytes` is the little-endian byte write on a memory map; the closed
model's `writeMemN` is the same write on its state carrier, and
`Machine/State.lean` records that definitional link.  The lemmas below match
the source `writeMemWord`/`readMemWord` against it at each byte count the
lowering emits, and record which bytes a load leaves readable.

No HOL claim is introduced here: these are the memory facts both renderings
of the ARMv8 target share.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- The memory-map part of a little-endian `size`-byte write. -/
def writeMemBytes (m : BitVec 64 → BitVec 8) (size : Nat) (address : BitVec 64)
    (value : BitVec 64) : BitVec 64 → BitVec 8 :=
  let byteAt (n : Nat) : BitVec 8 := (value >>> (8 * n)).setWidth 8
  match size with
  | 0 => m
  | 1 => fun a => if a = address then byteAt 0 else m a
  | 2 => fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else m a)
  | 3 => fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else if a = address + 2 then byteAt 2
      else m a)
  | 4 => fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else if a = address + 2 then byteAt 2
      else if a = address + 3 then byteAt 3
      else m a)
  | _ => fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else if a = address + 2 then byteAt 2
      else if a = address + 3 then byteAt 3
      else if a = address + 4 then byteAt 4
      else if a = address + 5 then byteAt 5
      else if a = address + 6 then byteAt 6
      else if a = address + 7 then byteAt 7
      else m a)

/-! ## The machine writes, byte by byte

`writeMemWord` writes byte `k` from `value >>> (8 * k)` at `a + k`; the
memory-map write writes the same bytes through an explicit chain of `if`s.  The
lemmas below match the two up at each byte count the lowering uses. -/

/-- The `k`-th byte of a little-endian write is the `k`-fold right shift. -/
theorem ushr8_iter (v : BitVec 64) (k : Nat) :
    v >>> (8 * k : Nat) = (fun x : BitVec 64 => x >>> (8 : Nat))^[k] v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, BitVec.shiftRight_add, ih, Function.iterate_succ_apply']

/-- The byte `k` of a value, in the shifted form `writeMemWord` produces. -/
theorem byteShift (v : BitVec 64) (k : Nat) :
    (v >>> (8 * k : Nat)).setWidth 8 =
      ((fun x : BitVec 64 => x >>> (8 : Nat))^[k] v).setWidth 8 := by
  rw [ushr8_iter]

/-- `readMemWord` preserves the register file. -/
theorem readMemWord_regs (a : BitVec 64) (n : Nat) (s : AsmState 64) :
    (readMemWord (resultWidth := 64) a n s).2.regs = s.regs := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
      rw [readMemWord_succ]
      simp only [assertState]
      exact ih _ _

/-- `writeMemWord` preserves the register file. -/
theorem writeMemWord_regs (a : BitVec 64) (n : Nat) (v : BitVec 64) (s : AsmState 64) :
    (writeMemWord (valueWidth := 64) a n v s).regs = s.regs := by
  induction n generalizing a v s with
  | zero => rfl
  | succ n ih =>
      rw [writeMemWord_succ]
      simp only [assertState, updMem]
      exact ih _ _ _

/-- A one-byte source store is the memory-map one-byte write. -/
theorem writeMemWord_mem_one (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 1 v s).mem x = writeMemBytes m 1 a v x := by
  simp only [writeMemWord, writeMemBytes, updMem_mem, assertState_mem]
  simp [hm]

/-- A two-byte source store is the memory-map two-byte write. -/
theorem writeMemWord_mem_two (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 2 v s).mem x = writeMemBytes m 2 a v x := by
  simp only [writeMemWord, writeMemBytes, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, ite_false]
  simp [hm]

/-- A four-byte source store is the memory-map four-byte write. -/
theorem writeMemWord_mem_four (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 4 v s).mem x = writeMemBytes m 4 a v x := by
  simp only [writeMemWord, writeMemBytes, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, ite_false]
  rw [show a + 1 + 1 + 1 = a + 3 by bv_omega, show a + 1 + 1 = a + 2 by bv_omega]
  rw [byteShift v 1, byteShift v 0]
  simp [hm]

/-- An eight-byte source store is the memory-map eight-byte write. -/
theorem writeMemWord_mem_eight (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 8 v s).mem x = writeMemBytes m 8 a v x := by
  simp only [writeMemWord, writeMemBytes, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, ite_false]
  rw [show a + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a + 7 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 + 1 = a + 6 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 = a + 5 by bv_omega,
    show a + 1 + 1 + 1 + 1 = a + 4 by bv_omega,
    show a + 1 + 1 + 1 = a + 3 by bv_omega,
    show a + 1 + 1 = a + 2 by bv_omega]
  rw [byteShift v 1, byteShift v 2, byteShift v 3, byteShift v 4, byteShift v 5,
    byteShift v 6, byteShift v 0]
  simp [hm]

/-- The source store and the memory-map store agree at every byte count the
lowering emits. -/
theorem writeMemWord_memSize (s : AsmState 64) (m : BitVec 64 → BitVec 8) (size : Nat)
    (hsize : size < 4) (a v x : BitVec 64) (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a (2 ^ size) v s).mem x =
      writeMemBytes m (2 ^ size) a v x := by
  interval_cases size
  · exact writeMemWord_mem_one s m a v x hm
  · exact writeMemWord_mem_two s m a v x hbe hm
  · exact writeMemWord_mem_four s m a v x hbe hm
  · exact writeMemWord_mem_eight s m a v x hbe hm

/-- A load leaves the source state's memory domain bytes readable: they are in
the domain of the state it reads. -/
theorem memLoadDomain (op : HolMemop) (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64)
    (size : Nat) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 2 ^ size → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, ite_false] at hfail
  obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
  exact readMemWord_domain (s1.regs base + off) (2 ^ size) s1 hbe hf

end Flapjack.Compiler.Encoders.Arm8
