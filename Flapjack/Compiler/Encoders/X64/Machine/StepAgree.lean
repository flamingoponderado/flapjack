module

public import Mathlib.Tactic
public import Flapjack.Compiler.Encoders.X64.Machine.Agree
public import Flapjack.Compiler.Encoders.X64.Machine.Congruence
public import Flapjack.Compiler.Encoders.X64.Machine.DecodeCongr

@[expose] public section

/-!
# Step agreement and framing for the closed x86-64 model

`X64Agree d s t` (`Machine/Agree.lean`) says two states have the same PC,
registers, XMM file, flags and failure flag, and the same bytes on `d`.  This
module proves that one `x64Next` step preserves that relation as long as the
step stays inside `d`, and that a step leaves every byte outside `d` alone.
These are the step-agreement and framing facts an `encoder_correct` proof for
the x86-64 target needs.

`FetchSafe d s` asks for the bytes the decoder reads: when decoding succeeds
with length `len`, the bytes `pc, pc+1, …, pc+len-1`; when it fails, the whole
sixteen-byte window `pc, …, pc+15` the decoder may examine.  An x86-64 encoding
is 1–10 bytes and `asm_step` only guarantees the bytes of the instruction being
executed, so the length-based form is what the per-instruction cases can
discharge.  `decode_congr_upto` turns agreement below the reported length into
agreement on the decoded instruction, and `decode_congr` does the same for the
sixteen-byte window when decoding fails.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack

/-! ## The byte addresses an instruction touches -/

/-- The byte addresses `a, a + 1, …, a + n - 1`. -/
def bytesAt (a : BitVec 64) (n : Nat) : List (BitVec 64) :=
  (List.range n).map (fun j => a + BitVec.ofNat 64 j)

/-- Byte `j` of `bytesAt a n`. -/
theorem mem_bytesAt {a : BitVec 64} {n j : Nat} (hj : j < n) :
    a + BitVec.ofNat 64 j ∈ bytesAt a n := by
  simp only [bytesAt, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

/-- The byte addresses one closed x86-64 instruction reads or writes.  The
memory-operand forms (`movRM`, `movMR`, `movzxRM`, and `movDQ` through a memory
operand) are the only instructions that touch memory. -/
def x64Touched (s : X64State) (i : X64Insn) : List (BitVec 64) :=
  match i with
  | .movRM sz _ base disp => bytesAt (readReg s base + disp) (sizeBytes sz)
  | .movMR sz _ base disp => bytesAt (readReg s base + disp) (sizeBytes sz)
  | .movzxRM sz1 _ _ base disp => bytesAt (readReg s base + disp) (sizeBytes sz1)
  | .sse (.movDQ _ quad _ rm) =>
      match effectiveAddress s 0 rm with
      | some addr => bytesAt addr (if quad then 8 else 4)
      | none => []
  | _ => []

/-- The domain facts `x64Touched` provides for a load, one byte at a time. -/
theorem x64Touched_movRM {d : BitVec 64 → Prop} {s : X64State} (sz : ZSize) (dst base : Nat)
    (disp : BitVec 64)
    (hacc : ∀ a ∈ x64Touched s (.movRM sz dst base disp), d a) :
    ∀ j, j < sizeBytes sz → d (readReg s base + disp + BitVec.ofNat 64 j) :=
  fun j hj => hacc _ (by simp only [x64Touched]; exact mem_bytesAt hj)

/-- The domain facts `x64Touched` provides for a store, one byte at a time. -/
theorem x64Touched_movMR {d : BitVec 64 → Prop} {s : X64State} (sz : ZSize) (src base : Nat)
    (disp : BitVec 64)
    (hacc : ∀ a ∈ x64Touched s (.movMR sz src base disp), d a) :
    ∀ j, j < sizeBytes sz → d (readReg s base + disp + BitVec.ofNat 64 j) :=
  fun j hj => hacc _ (by simp only [x64Touched]; exact mem_bytesAt hj)

/-- The domain facts `x64Touched` provides for a zero-extending load, one byte
at a time. -/
theorem x64Touched_movzxRM {d : BitVec 64 → Prop} {s : X64State} (sz1 sz2 : ZSize)
    (dst base : Nat) (disp : BitVec 64)
    (hacc : ∀ a ∈ x64Touched s (.movzxRM sz1 sz2 dst base disp), d a) :
    ∀ j, j < sizeBytes sz1 → d (readReg s base + disp + BitVec.ofNat 64 j) :=
  fun j hj => hacc _ (by simp only [x64Touched]; exact mem_bytesAt hj)

/-- Number of bytes `writeMemN size` stores: `size` bytes up to four, eight from
five on. -/
def writtenBytes (size : Nat) : Nat := if size = 0 then 0 else if size ≤ 4 then size else 8

/-- `writeMemN` stores at most eight bytes. -/
theorem writtenBytes_le_eight (size : Nat) : writtenBytes size ≤ 8 := by
  by_cases h0 : size = 0
  · subst h0; decide
  · by_cases h4 : size ≤ 4
    · simp only [writtenBytes, ite_eq_right h0, ite_eq_left h4]; omega
    · simp only [writtenBytes, ite_eq_right h0, ite_eq_right h4]
      omega

/-- The emitted operand sizes store exactly as many bytes as they access. -/
theorem writtenBytes_sizeBytes (sz : ZSize) : writtenBytes (sizeBytes sz) = sizeBytes sz := by
  cases sz <;> simp [sizeBytes, writtenBytes]

/-! ## Byte chains

`writeMemN` updates the memory by a chain of `if a = address + n then byte n
else …` tests.  `byteChain` is that chain as a list of `(address, byte)` pairs,
which makes the proofs below independent of how many bytes an access writes.
-/

/-- The if-chain `if a = e₀ then b₀ else if a = e₁ then b₁ else … else x`. -/
def byteChain (x : BitVec 8) : List (BitVec 64 × BitVec 8) → BitVec 64 → BitVec 8
  | [], _ => x
  | (e, b) :: t, a => if a = e then b else byteChain x t a

/-- A byte chain depends only on its final fallback byte. -/
theorem byteChain_congr {x y : BitVec 8} (h : x = y) (l : List (BitVec 64 × BitVec 8))
    (a : BitVec 64) : byteChain x l a = byteChain y l a := by
  subst h
  rfl

/-- A byte chain whose addresses are all different from `a` returns its
fallback byte at `a`. -/
theorem byteChain_of_ne {x : BitVec 8} {l : List (BitVec 64 × BitVec 8)} {a : BitVec 64}
    (h : ∀ e b, (e, b) ∈ l → a ≠ e) : byteChain x l a = x := by
  induction l generalizing a with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨e, b⟩ := p
      have hne : a ≠ e := h e b (by simp)
      have ht : ∀ e' b', (e', b') ∈ t → a ≠ e' := fun e' b' hm => h e' b' (by simp [hm])
      simp only [byteChain, ite_eq_right hne]
      exact ih ht

/-- The `(address, byte)` pairs `writeMemN` stores, in write order.  The `i = 0`
case is written as the bare `address` so that the chain matches `writeMemN`
definitionally. -/
def writeChain (size : Nat) (address v : BitVec 64) : List (BitVec 64 × BitVec 8) :=
  (List.range (writtenBytes size)).map
    fun i => (if i = 0 then address else address + BitVec.ofNat 64 i,
      (v >>> (8 * i)).setWidth 8)

/-- Every byte a write chain stores is `address` or `address + i` for an `i`
below the number of stored bytes. -/
theorem mem_writeChain {size : Nat} {address v e : BitVec 64} {b : BitVec 8}
    (h : (e, b) ∈ writeChain size address v) :
    ∃ i, i < writtenBytes size ∧
      e = (if i = 0 then address else address + BitVec.ofNat 64 i) := by
  simp only [writeChain, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, hi, (congrArg Prod.fst he).symm⟩

/-- Every byte a write chain stores lies inside the bytes touched by a load or
store of the same size. -/
theorem mem_writeChain_sizeBytes {sz : ZSize} {address v e : BitVec 64} {b : BitVec 8}
    (h : (e, b) ∈ writeChain (sizeBytes sz) address v) :
    ∃ i, i < sizeBytes sz ∧ e = (if i = 0 then address else address + BitVec.ofNat 64 i) := by
  obtain ⟨i, hi, he⟩ := mem_writeChain h
  exact ⟨i, by rw [writtenBytes_sizeBytes] at hi; exact hi, he⟩

/-- The `i`-th chain address is `address` or `address + i`. -/
theorem ne_chainAddr {address a : BitVec 64} {i : Nat} (h0 : a ≠ address)
    (hi : a ≠ address + BitVec.ofNat 64 i) :
    a ≠ (if i = 0 then address else address + BitVec.ofNat 64 i) := by
  by_cases hz : i = 0
  · simpa only [hz, ite_true] using h0
  · simpa only [hz, ite_false] using hi

/-- The memory after `writeMemN` is the byte chain of the stored pairs. -/
theorem writeMemN_mem (s : X64State) (size : Nat) (address v : BitVec 64) (a : BitVec 64) :
    (writeMemN s size address v).mem a = byteChain (s.mem a) (writeChain size address v) a := by
  by_cases h0 : size = 0
  · subst h0; rfl
  · by_cases h1 : size = 1
    · subst h1; rfl
    · by_cases h2 : size = 2
      · subst h2; rfl
      · by_cases h3 : size = 3
        · subst h3; rfl
        · by_cases h4 : size = 4
          · subst h4; rfl
          · rw [writeMemN.eq_6 s size address v h0 h1 h2 h3 h4]
            simp only [writeChain, writtenBytes, ite_eq_right h0, ite_eq_right (by omega : ¬ size ≤ 4)]
            rfl

/-! ## Congruence for the byte-wise memory accessors -/

/-- Two states agreeing on `d` read the same `size`-byte little-endian value. -/
theorem readMemN_congr {s t : X64State} {d : BitVec 64 → Prop}
    (hmem : ∀ a, d a → s.mem a = t.mem a) (size : Nat) (address : BitVec 64)
    (hacc : ∀ j, j < writtenBytes size → d (address + BitVec.ofNat 64 j)) :
    readMemN s size address = readMemN t size address := by
  have hb : ∀ j, j < writtenBytes size → s.mem (address + BitVec.ofNat 64 j) =
      t.mem (address + BitVec.ofNat 64 j) := fun j hj => hmem _ (hacc j hj)
  by_cases h0 : size = 0
  · subst h0; simp only [readMemN]
  · by_cases h1 : size = 1
    · subst h1
      have e0 : s.mem address = t.mem address := by simpa using hb 0 (by decide)
      simp only [readMemN, e0]
    · by_cases h2 : size = 2
      · subst h2
        have e0 : s.mem address = t.mem address := by simpa using hb 0 (by decide)
        have e1 : s.mem (address + 1) = t.mem (address + 1) := hb 1 (by decide)
        simp only [readMemN, e0, e1]
      · by_cases h3 : size = 3
        · subst h3
          have e0 : s.mem address = t.mem address := by simpa using hb 0 (by decide)
          have e1 : s.mem (address + 1) = t.mem (address + 1) := hb 1 (by decide)
          have e2 : s.mem (address + 2) = t.mem (address + 2) := hb 2 (by decide)
          simp only [readMemN, e0, e1, e2]
        · by_cases h4 : size = 4
          · subst h4
            have e0 : s.mem address = t.mem address := by simpa using hb 0 (by decide)
            have e1 : s.mem (address + 1) = t.mem (address + 1) := hb 1 (by decide)
            have e2 : s.mem (address + 2) = t.mem (address + 2) := hb 2 (by decide)
            have e3 : s.mem (address + 3) = t.mem (address + 3) := hb 3 (by decide)
            simp only [readMemN, e0, e1, e2, e3]
          · have hw : writtenBytes size = 8 := by
              simp only [writtenBytes, ite_eq_right h0, ite_eq_right (by omega : ¬ size ≤ 4)]
            have e0 : s.mem address = t.mem address := by simpa using hb 0 (by omega)
            have e1 : s.mem (address + 1) = t.mem (address + 1) := hb 1 (by omega)
            have e2 : s.mem (address + 2) = t.mem (address + 2) := hb 2 (by omega)
            have e3 : s.mem (address + 3) = t.mem (address + 3) := hb 3 (by omega)
            have e4 : s.mem (address + 4) = t.mem (address + 4) := hb 4 (by omega)
            have e5 : s.mem (address + 5) = t.mem (address + 5) := hb 5 (by omega)
            have e6 : s.mem (address + 6) = t.mem (address + 6) := hb 6 (by omega)
            have e7 : s.mem (address + 7) = t.mem (address + 7) := hb 7 (by omega)
            rw [readMemN.eq_6 s size address h0 h1 h2 h3 h4,
              readMemN.eq_6 t size address h0 h1 h2 h3 h4]
            simp only [e0, e1, e2, e3, e4, e5, e6, e7]

/-- Two states agreeing on `d` write the same bytes, so they still agree on `d`. -/
theorem writeMemN_congr {s t : X64State} {d : BitVec 64 → Prop}
    (hmem : ∀ a, d a → s.mem a = t.mem a) (size : Nat) (address v : BitVec 64) :
    ∀ a, d a → (writeMemN s size address v).mem a = (writeMemN t size address v).mem a := by
  intro a ha
  rw [writeMemN_mem, writeMemN_mem]
  exact byteChain_congr (hmem a ha) _ a

/-! ## Register, XMM and flag updates -/

theorem writeReg_regs (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeReg s r v).regs = fun x => if x = num2Zreg r then v else s.regs x := rfl
theorem writeXmm_xmm (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeXmm s r v).xmm = fun x => if x = r % 8 then
      ((s.xmm (r % 8)).setWidth 128 &&& BitVec.ofNat 128 (2 ^ 128 - 2 ^ 64)) |||
        v.setWidth 128 else s.xmm x := rfl

/-- Writing the low word of an XMM register leaves that word readable. -/
theorem readXmm_writeXmm_self (s : X64State) (r : Nat) (v : BitVec 64) :
    readXmm (writeXmm s r v) r = v := by
  simp only [readXmm, writeXmm]
  bv_normalize
  simp_all

/-- Writing one XMM register leaves a different register's low word alone. -/
theorem readXmm_writeXmm_other (s : X64State) (r x : Nat) (v : BitVec 64)
    (h : x % 8 ≠ r % 8) :
    readXmm (writeXmm s r v) x = readXmm s x := by
  simp only [readXmm, writeXmm]
  rw [ite_eq_right (by omega : ¬ x % 8 = r % 8)]

@[simp] theorem writeReg_mem (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeReg s r v).mem = s.mem := rfl
theorem writeReg_pc (s : X64State) (r : Nat) (v : BitVec 64) : (writeReg s r v).pc = s.pc := rfl
theorem writeReg_xmm (s : X64State) (r : Nat) (v : BitVec 64) : (writeReg s r v).xmm = s.xmm := rfl
theorem writeReg_flags (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeReg s r v).flags = s.flags := rfl
theorem writeReg_failed (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeReg s r v).failed = s.failed := rfl

@[simp] theorem writeXmm_mem (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeXmm s r v).mem = s.mem := rfl
theorem writeXmm_pc (s : X64State) (r : Nat) (v : BitVec 64) : (writeXmm s r v).pc = s.pc := rfl
theorem writeXmm_regs (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeXmm s r v).regs = s.regs := rfl
theorem writeXmm_flags (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeXmm s r v).flags = s.flags := rfl
theorem writeXmm_failed (s : X64State) (r : Nat) (v : BitVec 64) :
    (writeXmm s r v).failed = s.failed := rfl

@[simp] theorem writeRegSized_mem (s : X64State) (sz : ZSize) (dst : Nat) (v : BitVec 64) :
    (writeRegSized sz dst v s).mem = s.mem := by
  cases sz <;> rfl

theorem writeMemN_pc (s : X64State) (size : Nat) (a v : BitVec 64) :
    (writeMemN s size a v).pc = s.pc := by unfold writeMemN; split <;> rfl
theorem writeMemN_regs (s : X64State) (size : Nat) (a v : BitVec 64) :
    (writeMemN s size a v).regs = s.regs := by unfold writeMemN; split <;> rfl
theorem writeMemN_xmm (s : X64State) (size : Nat) (a v : BitVec 64) :
    (writeMemN s size a v).xmm = s.xmm := by unfold writeMemN; split <;> rfl
theorem writeMemN_flags (s : X64State) (size : Nat) (a v : BitVec 64) :
    (writeMemN s size a v).flags = s.flags := by unfold writeMemN; split <;> rfl
theorem writeMemN_failed (s : X64State) (size : Nat) (a v : BitVec 64) :
    (writeMemN s size a v).failed = s.failed := by unfold writeMemN; split <;> rfl

/-- Writing the same register in two agreeing states preserves agreement. -/
theorem writeReg_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (r : Nat) (v : BitVec 64) : X64Agree d (writeReg s r v) (writeReg t r v) := by
  refine ⟨?_, fun x => ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeReg_pc, writeReg_pc, h.pc]
  · simp only [writeReg]
    split <;> simp [h.regs]
  · rw [writeReg_xmm, writeReg_xmm]; exact h.xmm
  · rw [writeReg_flags, writeReg_flags, h.flags]
  · rw [writeReg_failed, writeReg_failed, h.failed]
  · exact h.mem

/-- Writing the same XMM register in two agreeing states preserves agreement. -/
theorem writeXmm_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (r : Nat) (v : BitVec 64) : X64Agree d (writeXmm s r v) (writeXmm t r v) := by
  refine ⟨?_, ?_, fun x => ?_, ?_, ?_, ?_⟩
  · rw [writeXmm_pc, writeXmm_pc, h.pc]
  · rw [writeXmm_regs, writeXmm_regs]; exact h.regs
  · simp only [writeXmm]
    split <;> simp [h.xmm]
  · rw [writeXmm_flags, writeXmm_flags, h.flags]
  · rw [writeXmm_failed, writeXmm_failed, h.failed]
  · exact h.mem

/-- A sized register write agrees in two agreeing states. -/
theorem writeRegSized_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (sz : ZSize) (dst : Nat) (value : BitVec 64) :
    X64Agree d (writeRegSized sz dst value s) (writeRegSized sz dst value t) := by
  have hread : readReg s dst = readReg t dst := h.regs _
  cases sz with
  | z8 hr =>
      simp only [writeRegSized]
      rw [hread]
      exact writeReg_agree h _ _
  | z16 =>
      simp only [writeRegSized]
      rw [hread]
      exact writeReg_agree h _ _
  | z32 => simp only [writeRegSized]; exact writeReg_agree h _ _
  | z64 => simp only [writeRegSized]; exact writeReg_agree h _ _

/-- Setting the flags agrees in two agreeing states. -/
theorem setFlags_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (f : X64Flags) : X64Agree d { s with flags := f } { t with flags := f } := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩
  · rw [h.pc]
  · exact h.regs
  · exact h.xmm
  · rw [h.failed]
  · exact h.mem

/-- Writing memory in two agreeing states preserves agreement. -/
theorem writeMemN_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (size : Nat) (a v : BitVec 64) :
    X64Agree d (writeMemN s size a v) (writeMemN t size a v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeMemN_pc, writeMemN_pc, h.pc]
  · rw [writeMemN_regs, writeMemN_regs]; exact h.regs
  · rw [writeMemN_xmm, writeMemN_xmm]; exact h.xmm
  · rw [writeMemN_flags, writeMemN_flags, h.flags]
  · rw [writeMemN_failed, writeMemN_failed, h.failed]
  · exact writeMemN_congr h.mem size a v

/-- Writing two registers in two agreeing states preserves agreement. -/
theorem writeReg2_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (r1 r2 : Nat) (v1 v2 : BitVec 64) :
    X64Agree d (writeReg (writeReg s r1 v1) r2 v2)
      (writeReg (writeReg t r1 v1) r2 v2) := by
  refine ⟨?_, fun x => ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeReg_pc, writeReg_pc, writeReg_pc, writeReg_pc, h.pc]
  · simp only [writeReg_regs]; rw [h.regs x]
  · rw [writeReg_xmm, writeReg_xmm, writeReg_xmm, writeReg_xmm]; exact h.xmm
  · rw [writeReg_flags, writeReg_flags, writeReg_flags, writeReg_flags, h.flags]
  · rw [writeReg_failed, writeReg_failed, writeReg_failed, writeReg_failed, h.failed]
  · exact h.mem

/-- The effective address only depends on the agreeing state. -/
theorem effectiveAddress_congr {d : BitVec 64 → Prop} {s t : X64State}
    (h : X64Agree d s t) (len : Nat) (rm : ZRM) :
    effectiveAddress s len rm = effectiveAddress t len rm := by
  cases rm with
  | zr r => rfl
  | zm index base disp =>
      cases index with
      | none =>
          cases base with
          | noBase => rfl
          | regBase r =>
              simp only [effectiveAddress, readReg]
              rw [h.regs _]
          | ripBase =>
              simp only [effectiveAddress]
              rw [h.pc]
      | some p => rfl

/-- Writing a register and setting flags agrees in two agreeing states. -/
theorem writeRegSized_setFlags_agree {d : BitVec 64 → Prop} {s t : X64State}
    (h : X64Agree d s t) (sz : ZSize) (dst : Nat) (value : BitVec 64) (f : X64Flags) :
    X64Agree d { (writeRegSized sz dst value s) with flags := f }
      { (writeRegSized sz dst value t) with flags := f } := by
  have h' := writeRegSized_agree h sz dst value
  exact ⟨h'.pc, h'.regs, h'.xmm, rfl, h'.failed, h'.mem⟩

/-- Writing two registers and setting flags agrees in two agreeing states. -/
theorem writeReg2_setFlags_agree {d : BitVec 64 → Prop} {s t : X64State}
    (h : X64Agree d s t) (r1 r2 : Nat) (v1 v2 : BitVec 64) (f : X64Flags) :
    X64Agree d { writeReg (writeReg s r1 v1) r2 v2 with flags := f }
      { writeReg (writeReg t r1 v1) r2 v2 with flags := f } := by
  have h' := writeReg2_agree h r1 r2 v1 v2
  exact ⟨h'.pc, h'.regs, h'.xmm, rfl, h'.failed, h'.mem⟩


/-- A `movDQ` through a memory operand agrees in two agreeing states. -/
theorem execSSE_movDQ_zm_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (toXmm quad : Bool) (xmm : Nat) (index : Option (Nat × Nat)) (base : ZBase)
    (disp : BitVec 64)
    (hEA : effectiveAddress s 0 (.zm index base disp) =
      effectiveAddress t 0 (.zm index base disp))
    (hacc : ∀ a ∈ x64Touched s (.sse (.movDQ toXmm quad xmm (.zm index base disp))), d a) :
    X64Agree d (execSSE (.movDQ toXmm quad xmm (.zm index base disp)) s)
      (execSSE (.movDQ toXmm quad xmm (.zm index base disp)) t) := by
  simp only [execSSE]
  rw [hEA]
  cases hE : effectiveAddress t 0 (.zm index base disp) with
  | none =>
      exact ⟨h.pc, h.regs, h.xmm, h.flags, rfl, h.mem⟩
  | some addr =>
      have hd : ∀ j, j < (if quad then 8 else 4) → d (addr + BitVec.ofNat 64 j) := by
        intro j hj
        exact hacc _ (by simp only [x64Touched, hEA, hE]; exact mem_bytesAt hj)
      have hwb : writtenBytes (if quad then 8 else 4) = (if quad then 8 else 4) := by
        cases quad <;> decide
      cases toXmm with
      | false =>
          simp only [Bool.false_eq_true, ite_false, readXmm]
          rw [h.xmm (xmm % 8)]
          exact writeMemN_agree h (if quad then 8 else 4) addr _
      | true =>
          simp only [ite_true, readXmm]
          rw [readMemN_congr h.mem (if quad then 8 else 4) addr
            (fun j hj => hd j (by rwa [hwb] at hj))]
          exact writeXmm_agree h xmm _

/-- Executing an SSE instruction agrees in two agreeing states. -/
theorem execSSE_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (op : X64SSE) (hacc : ∀ a ∈ x64Touched s (.sse op), d a) :
    X64Agree d (execSSE op s) (execSSE op t) := by
  have hxmmEq : s.xmm = t.xmm := funext h.xmm
  cases op with
  | comisd dst src =>
      simp only [execSSE, readXmm, hxmmEq]
      exact ⟨h.pc, h.regs, fun x => rfl, rfl, h.failed, h.mem⟩
  | movsd dst src =>
      simp only [execSSE, readXmm]
      rw [h.xmm (src % 8)]
      exact writeXmm_agree h dst _
  | pcmpeqq dst src =>
      simp only [execSSE, readXmm, hxmmEq]
      exact ⟨h.pc, h.regs, fun x => rfl, h.flags, h.failed, h.mem⟩
  | psrlqImm dst imm =>
      simp only [execSSE, hxmmEq]
      exact ⟨h.pc, h.regs, fun x => rfl, h.flags, h.failed, h.mem⟩
  | psllqImm dst imm =>
      simp only [execSSE, hxmmEq]
      exact ⟨h.pc, h.regs, fun x => rfl, h.flags, h.failed, h.mem⟩
  | logicPD lop dst src =>
      simp only [execSSE, readXmm]
      rw [h.xmm (dst % 8), h.xmm (src % 8)]
      exact writeXmm_agree h dst _
  | sqrtsd dst src =>
      simp only [execSSE, readXmm]
      rw [h.xmm (src % 8)]
      exact writeXmm_agree h dst _
  | binSD bop dst src =>
      simp only [execSSE, readXmm]
      rw [h.xmm (dst % 8), h.xmm (src % 8)]
      exact writeXmm_agree h dst _
  | movDQ toXmm quad xmm rm =>
      cases rm with
      | zr reg =>
          cases toXmm with
          | false =>
              simp only [execSSE, Bool.false_eq_true, ite_false, readXmm, readReg]
              rw [h.xmm (xmm % 8)]
              exact writeRegSized_agree h _ _ _
          | true =>
              simp only [execSSE, ite_true, readReg]
              rw [h.regs (num2Zreg reg)]
              exact writeXmm_agree h xmm _
      | zm index base disp =>
          exact execSSE_movDQ_zm_agree h toXmm quad xmm index base disp
            (effectiveAddress_congr h 0 _) hacc
  | cvtpd2dq truncate dst src =>
      simp only [execSSE, readXmm]
      rw [h.xmm (src % 8)]
      split
      · exact ⟨h.pc, h.regs, h.xmm, h.flags, rfl, h.mem⟩
      · split
        · exact ⟨h.pc, h.regs, h.xmm, h.flags, rfl, h.mem⟩
        · exact writeXmm_agree h dst _
  | pslldq dst imm =>
      simp only [execSSE, hxmmEq]
      exact ⟨h.pc, h.regs, fun x => rfl, h.flags, h.failed, h.mem⟩
  | psrldq dst imm =>
      simp only [execSSE, hxmmEq]
      exact ⟨h.pc, h.regs, fun x => rfl, h.flags, h.failed, h.mem⟩
  | cvtdq2pd dst src =>
      simp only [execSSE, readXmm]
      rw [h.xmm (src % 8)]
      exact writeXmm_agree h dst _

/-- A step that stays inside `d` preserves agreement. -/
theorem execInsn_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (i : X64Insn) (len : Nat) (hacc : ∀ a ∈ x64Touched s i, d a) :
    X64Agree d (execInsn i len s) (execInsn i len t) := by
  cases i with
  | nop n => exact h
  | movRR sz dst src =>
      simp only [execInsn, readReg]
      rw [h.regs (num2Zreg src)]
      exact writeRegSized_agree h sz dst _
  | movRI sz dst imm =>
      simp only [execInsn]
      exact writeRegSized_agree h sz dst imm
  | movRM sz dst base disp =>
      simp only [execInsn, readReg]
      have hv : readMemN s (sizeBytes sz) (t.regs (num2Zreg base) + disp) =
          readMemN t (sizeBytes sz) (t.regs (num2Zreg base) + disp) := by
        apply readMemN_congr h.mem
        intro j hj
        have hd := hacc _ (by
          simp only [x64Touched]
          exact mem_bytesAt (by rwa [writtenBytes_sizeBytes] at hj))
        simp only [readReg] at hd
        rwa [h.regs (num2Zreg base)] at hd
      rw [h.regs (num2Zreg base), hv]
      exact writeRegSized_agree h sz dst _
  | movMR sz src base disp =>
      simp only [execInsn, readReg]
      rw [h.regs (num2Zreg base), h.regs (num2Zreg src)]
      exact writeMemN_agree h (sizeBytes sz) (t.regs (num2Zreg base) + disp) _
  | movzxRM sz1 sz2 dst base disp =>
      simp only [execInsn, readReg]
      have hv : readMemN s (sizeBytes sz1) (t.regs (num2Zreg base) + disp) =
          readMemN t (sizeBytes sz1) (t.regs (num2Zreg base) + disp) := by
        apply readMemN_congr h.mem
        intro j hj
        have hd := hacc _ (by
          simp only [x64Touched]
          exact mem_bytesAt (by rwa [writtenBytes_sizeBytes] at hj))
        simp only [readReg] at hd
        rwa [h.regs (num2Zreg base)] at hd
      rw [h.regs (num2Zreg base), hv]
      exact writeReg_agree h dst _
  | binopRI op sz dst imm =>
      simp only [execInsn, readReg]
      rw [h.regs (num2Zreg dst), h.flags]
      cases op <;>
        (first | exact setFlags_agree h _ | exact writeRegSized_setFlags_agree h sz dst _ _)
  | binopRR op sz dst src =>
      simp only [execInsn, readReg]
      rw [h.regs (num2Zreg dst), h.regs (num2Zreg src), h.flags]
      cases op <;>
        (first | exact setFlags_agree h _ | exact writeRegSized_setFlags_agree h sz dst _ _)
  | monop op sz dst =>
      simp only [execInsn, readReg]
      rw [h.regs (num2Zreg dst), h.flags]
      cases op with
      | znot => exact writeRegSized_agree h sz dst _
      | zneg => exact writeRegSized_setFlags_agree h sz dst _ _
      | zinc => exact writeRegSized_setFlags_agree h sz dst _ _
      | zdec => exact writeRegSized_setFlags_agree h sz dst _ _
  | mul sz src =>
      have h0 : readReg s 0 = readReg t 0 := by simp only [readReg]; exact h.regs _
      have hsrc : readReg s src = readReg t src := by simp only [readReg]; exact h.regs _
      have hfl : s.flags = t.flags := h.flags
      simp only [execInsn, h0, hsrc, hfl]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [writeReg_pc, writeReg_pc]; exact h.pc
      · intro r; simp only [writeReg_regs]; rw [h.regs r]
      · simp only [writeReg_xmm, writeReg_xmm]; exact h.xmm
      · rfl
      · simp only [writeReg_failed, writeReg_failed]; exact h.failed
      · exact h.mem
  | div sz src =>
      have h2 : readReg s 2 = readReg t 2 := by simp only [readReg]; exact h.regs _
      have h0 : readReg s 0 = readReg t 0 := by simp only [readReg]; exact h.regs _
      have hsrc : readReg s src = readReg t src := by simp only [readReg]; exact h.regs _
      simp only [execInsn, h2, h0, hsrc]
      split
      · exact ⟨h.pc, h.regs, h.xmm, h.flags, rfl, h.mem⟩
      · split
        · exact ⟨h.pc, h.regs, h.xmm, h.flags, rfl, h.mem⟩
        · exact writeReg2_agree h 0 2 _ _
  | cmc =>
      simp only [execInsn]
      rw [h.flags]
      exact ⟨h.pc, h.regs, h.xmm, rfl, h.failed, h.mem⟩
  | setcc cond haveRex dst =>
      simp only [execInsn]
      rw [h.flags]
      exact writeRegSized_agree h _ dst _
  | jcc cond imm =>
      simp only [execInsn]
      rw [h.flags, h.pc]
      split
      · exact ⟨rfl, h.regs, h.xmm, rfl, h.failed, h.mem⟩
      · exact ⟨rfl, h.regs, h.xmm, rfl, h.failed, h.mem⟩
  | jmp dst =>
      simp only [execInsn, readReg]
      rw [h.regs (num2Zreg dst)]
      exact ⟨rfl, h.regs, h.xmm, h.flags, h.failed, h.mem⟩
  | lea sz dst disp =>
      simp only [execInsn]
      rw [h.pc]
      exact writeRegSized_agree h sz dst _
  | sse op =>
      exact execSSE_agree h op hacc

/-- A byte chain over the write chain leaves every byte outside the touched
range unchanged. -/
theorem not_mem_bytesAt {a addr : BitVec 64} {n : Nat} (h : a ∉ bytesAt addr n) :
    ∀ j, j < n → a ≠ addr + BitVec.ofNat 64 j := by
  intro j hj habs
  apply h
  rw [habs]
  exact mem_bytesAt hj

/-- A byte chain over the write chain leaves every byte outside the touched
range unchanged. -/
theorem byteChain_writeChain_of_ne {x : BitVec 8} {size : Nat} {address v a : BitVec 64}
    (hsize : writtenBytes size = size)
    (ha : ∀ j, j < size → a ≠ address + BitVec.ofNat 64 j) :
    byteChain x (writeChain size address v) a = x := by
  apply byteChain_of_ne
  intro e b he
  obtain ⟨j, hj, hej⟩ := mem_writeChain he
  rw [hsize] at hj
  rw [hej]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [ite_true]
    have h := ha 0 hj
    simpa using h
  · simp only [hj0, ite_false]
    exact ha j hj

/-- Every byte outside `x64Touched` is unchanged by an SSE instruction. -/
theorem execSSE_frame (s : X64State) (op : X64SSE) (a : BitVec 64)
    (ha : a ∉ x64Touched s (.sse op)) : (execSSE op s).mem a = s.mem a := by
  cases op with
  | movDQ toXmm quad xmm rm =>
      cases rm with
      | zr reg =>
          simp only [execSSE]
          cases toXmm with
          | true => rfl
          | false =>
              simp only [Bool.false_eq_true, ite_false]
              cases quad <;> rfl
      | zm index base disp =>
          simp only [execSSE]
          cases hE : effectiveAddress s 0 (.zm index base disp) with
          | none => rfl
          | some addr =>
              cases toXmm with
              | true => rfl
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  rw [writeMemN_mem]
                  apply byteChain_writeChain_of_ne
                  · cases quad <;> decide
                  · intro j hj
                    have hnot : a ∉ bytesAt addr (if quad then 8 else 4) := by
                      have hx : x64Touched s (.sse (.movDQ false quad xmm (.zm index base disp))) =
                          bytesAt addr (if quad then 8 else 4) := by
                        simp only [x64Touched, hE]
                      rwa [hx] at ha
                    exact not_mem_bytesAt hnot j hj
  | cvtpd2dq truncate dst src =>
      simp only [execSSE]
      split
      · simp
      · split
        · simp
        · simp
  | _ => rfl

/-- Every byte outside `x64Touched` is unchanged by a closed-model step. -/
theorem execInsn_frame (s : X64State) (i : X64Insn) (len : Nat) (a : BitVec 64)
    (ha : a ∉ x64Touched s i) : (execInsn i len s).mem a = s.mem a := by
  cases i with
  | nop n => rfl
  | movRR sz dst src => simp only [execInsn]; simp
  | movRI sz dst imm => simp only [execInsn]; simp
  | movRM sz dst base disp => simp only [execInsn]; simp
  | movMR sz src base disp =>
      simp only [execInsn]
      rw [writeMemN_mem]
      apply byteChain_writeChain_of_ne
      · exact writtenBytes_sizeBytes sz
      · intro j hj
        simp only [x64Touched] at ha
        exact not_mem_bytesAt ha j hj
  | movzxRM sz1 sz2 dst base disp => simp only [execInsn]; simp
  | binopRI op sz dst imm => simp only [execInsn]; split <;> simp
  | binopRR op sz dst src => simp only [execInsn]; split <;> simp
  | monop op sz dst => cases op <;> simp only [execInsn] <;> simp
  | mul sz src => rfl
  | div sz src =>
      simp only [execInsn]
      split
      · simp
      · split
        · simp
        · simp
  | cmc => rfl
  | setcc cond haveRex dst => simp only [execInsn]; simp
  | jcc cond imm => simp only [execInsn]; split <;> simp
  | jmp dst => rfl
  | lea sz dst disp => simp only [execInsn]; simp
  | sse op => exact execSSE_frame s op a ha

/-! ## Step agreement and framing for `x64Next` -/

/-- The bytes the next instruction is fetched from lie in `d`: the instruction
at `PC` decodes with length `len` and the `len` bytes from `PC` are in `d`.
Requiring the decode to succeed is what the per-instruction cases discharge
(from the decoder inverses); it lets the simulation carry the decoded
instruction across agreeing states without a sixteen-byte window. -/
def FetchSafe (d : BitVec 64 → Prop) (s : X64State) : Prop :=
  ∃ (i : X64Insn) (len : Nat),
    decode (fun k => s.mem (s.pc + BitVec.ofNat 64 k)) = some (i, len) ∧
      ∀ j, j < len → d (s.pc + BitVec.ofNat 64 j)

/-- A step stays inside `d`: the decoded instruction's bytes and every byte it
touches lie in `d`. -/
def StepSafe (d : BitVec 64 → Prop) (s : X64State) : Prop :=
  ∃ (i : X64Insn) (len : Nat),
    decode (fun k => s.mem (s.pc + BitVec.ofNat 64 k)) = some (i, len) ∧
      (∀ j, j < len → d (s.pc + BitVec.ofNat 64 j)) ∧
      ∀ a ∈ x64Touched s i, d a

/-- One closed-model step preserves agreement on `d` when it stays inside
`d`. -/
theorem x64Next_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (hsafe : StepSafe d s) : X64Agree d (x64Next s) (x64Next t) := by
  obtain ⟨insn, len, hdec_s, hfetch, htouch⟩ := hsafe
  have hmem : ∀ j, j < len →
      s.mem (s.pc + BitVec.ofNat 64 j) = t.mem (t.pc + BitVec.ofNat 64 j) := by
    intro j hj
    have hd : d (s.pc + BitVec.ofNat 64 j) := hfetch j hj
    show s.mem (s.pc + BitVec.ofNat 64 j) = t.mem (t.pc + BitVec.ofNat 64 j)
    rw [← h.pc]
    exact h.mem _ hd
  have hdec_t : decode (fun k => t.mem (t.pc + BitVec.ofNat 64 k)) = some (insn, len) :=
    decode_congr_upto _ _ insn len hdec_s hmem
  have hdecode : decode (fun k => s.mem (s.pc + BitVec.ofNat 64 k)) =
      decode (fun k => t.mem (t.pc + BitVec.ofNat 64 k)) := by
    rw [hdec_s, hdec_t]
  unfold x64Next
  rw [h.failed, hdecode]
  split
  · exact h
  · split
    · rename_i insn' len' hdec
      have hpair : insn = insn' ∧ len = len' :=
        Prod.mk.inj (Option.some.inj (hdec_s.symm.trans (hdecode.trans hdec)))
      obtain ⟨hinsn, hlen⟩ := hpair
      have htouch' : ∀ a ∈ x64Touched s insn', d a := by
        intro a ha
        rw [← hinsn] at ha
        exact htouch a ha
      have hagree := execInsn_agree h insn' len' htouch'
      split
      · exact hagree
      · exact hagree
      · refine ⟨?_, hagree.regs, hagree.xmm, hagree.flags, hagree.failed, hagree.mem⟩
        rw [h.pc]
    · exact ⟨h.pc, h.regs, h.xmm, h.flags, rfl, h.mem⟩

/-- One closed-model step leaves every byte outside `d` alone. -/
theorem x64Next_frame {d : BitVec 64 → Prop} {s : X64State} (hsafe : StepSafe d s)
    (a : BitVec 64) (ha : ¬ d a) : (x64Next s).mem a = s.mem a := by
  obtain ⟨insn, len, hdec_s, hfetch, htouch⟩ := hsafe
  unfold x64Next
  split
  · rfl
  · split
    · rename_i insn' len' hdec
      have hpair : insn' = insn ∧ len' = len :=
        Prod.mk.inj (Option.some.inj (hdec.symm.trans hdec_s))
      obtain ⟨hinsn, hlen⟩ := hpair
      have htouch' : ∀ b ∈ x64Touched s insn', d b := by
        intro b hb
        rw [hinsn] at hb
        exact htouch b hb
      have hframe := execInsn_frame s insn' len' a (fun hmem => ha (htouch' a hmem))
      split
      · exact hframe
      · exact hframe
      · exact hframe
    · rfl

end Flapjack.Compiler.Encoders.X64
