import Flapjack.Compiler.Encoders.Arm8.Machine.MulCarryCase

/-!
# The ARMv8 memory instruction cases of `encoder_correct`

This is the ARM8 analogue of `Flapjack/Mips32/TargetProof/Mem.lean`: the eight
`mem_op` forms (`load`/`load8`/`load16`/`load32` and the four stores) of
`encoder_correct arm8Target`.

Each of them lowers (`loadStoreAst`) either to one `loadStoreImmediate` or, for
an offset that is neither nine-bit signed nor a twelve-bit scaled unsigned
offset, to an `addSubImmediate` into the temporary register `26` followed by a
small `loadStoreImmediate`.  The case proof therefore has two branches, and the
interesting parts are:

* the effective address `readReg ms base + off` agrees with the source
  `readReg s1 base + off`, and on the two-instruction path the intermediate
  `addSubImmediate` result plus its immediate is that same address;
* the bytes the machine reads/writes (`readMemN`/`writeMemN`, little-endian)
  agree with the source `readMemWord`/`writeMemWord` at the eight byte counts
  the lowering uses;
* a failed source alignment check forces every read byte into the domain, so the
  bytes the target reads are the bytes the source read, and a store keeps the
  domain (`writeMemWord_memDomain`);
* the temporary register is in `arm8Config.avoidRegs`, so the intermediate
  register write is invisible to the state relation.

These are the ARM8 construction cases of `arm8_encoder_correct`; the ARM8
encoding is a byte-for-byte port of the CakeML ARMv8 encoder rather than of a
HOL script, so no case carries a `@[hol]` reference.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## The byte bridge between source and target memory -/

/-- The little-endian value `readMemWord` assembles out of the bytes at `a`,
`a + 1`, `a + 2`, ... -/
def readBytes (mem : BitVec 64 → BitVec 8) (a : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => (readBytes mem (a + 1) n) <<< (8 : Nat) ||| (mem a).setWidth 64

/-- The numeral `0` of the word carrier is the empty word, so that the `BitVec`
zero lemmas apply to the base case of `readBytes`. -/
theorem zero64 : ((0 : BitVec 64) = 0#64) := rfl

/-- The value `readMemWord` assembles is the little-endian word of the bytes it
reads (with the little-endian addressing of `arm8Config`, `be = false`). -/
theorem readMemWord_fst (a : BitVec 64) (n : Nat) (s : AsmState 64) (hbe : s.be = false) :
    (readMemWord (resultWidth := 64) a n s).1 = readBytes s.mem a n := by
  induction n generalizing a s with
  | zero => simp [readMemWord, readBytes]
  | succ n ih =>
      rw [readMemWord_succ, hbe]
      simp only [Bool.false_eq_true, if_false]
      generalize hr : readMemWord (resultWidth := 64) (a + 1) n s = r
      obtain ⟨w, s1⟩ := r
      have hmem := readMemWord_mem_eq_direct (resultWidth := 64) (a + 1) n s
      rw [hr] at hmem
      have hw : w = readBytes s.mem (a + 1) n := by
        have h := ih (a + 1) s hbe
        rw [hr] at h
        exact h
      have hread : readMem a s1 = s.mem a := by
        have hmem' : s1.mem = s.mem := hmem
        simp only [readMem, hmem']
      rw [hw, hread]
      rfl

/-- `readMemWord` preserves the endianness flag. -/
theorem readMemWord_be (a : BitVec 64) (n : Nat) (s : AsmState 64) :
    (readMemWord (resultWidth := 64) a n s).2.be = s.be := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
      rw [readMemWord_succ]
      simp only [assertState_be]
      exact ih _ _

/-- `readMemWord` preserves the memory domain. -/
theorem readMemWord_memDomain (a : BitVec 64) (n : Nat) (s : AsmState 64) :
    (readMemWord (resultWidth := 64) a n s).2.memDomain = s.memDomain := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
      rw [readMemWord_succ]
      simp only [assertState_memDomain]
      exact ih _ _

/-- `readMemWord` preserves the register file. -/
theorem readMemWord_regs (a : BitVec 64) (n : Nat) (s : AsmState 64) :
    (readMemWord (resultWidth := 64) a n s).2.regs = s.regs := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
      rw [readMemWord_succ]
      simp only [assertState]
      exact ih _ _

/-- `writeMemWord` preserves the endianness flag. -/
theorem writeMemWord_be (a : BitVec 64) (n : Nat) (w : BitVec 64) (s : AsmState 64) :
    (writeMemWord (valueWidth := 64) a n w s).be = s.be := by
  induction n generalizing a w s with
  | zero => rfl
  | succ n ih =>
      rw [writeMemWord_succ]
      simp only [assertState_be, updMem_be]
      exact ih _ _ _

/-- `writeMemWord` preserves the memory domain. -/
theorem writeMemWord_memDomain (a : BitVec 64) (n : Nat) (w : BitVec 64) (s : AsmState 64) :
    (writeMemWord (valueWidth := 64) a n w s).memDomain = s.memDomain := by
  induction n generalizing a w s with
  | zero => rfl
  | succ n ih =>
      rw [writeMemWord_succ]
      simp only [assertState_memDomain, updMem_memDomain]
      exact ih _ _ _

/-- A successful `readMemWord` reads all of its bytes out of the domain.  This is
the domain side of the source alignment guard: `memLoad` fails unless the read
succeeds, so the bytes the target reads are the bytes the source read. -/
theorem readMemWord_domain (a : BitVec 64) (n : Nat) (s : AsmState 64) (hbe : s.be = false)
    (h : (readMemWord (resultWidth := 64) a n s).2.failed = false) :
    ∀ k, k < n → s.memDomain (a + BitVec.ofNat 64 k) := by
  induction n generalizing a s with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk
      classical
      rw [readMemWord_succ] at h
      simp only [hbe, Bool.false_eq_true, if_false] at h
      set s1 : AsmState 64 := (readMemWord (resultWidth := 64) (a + 1) n s).2 with hs1
      simp only [assertState, Bool.or_eq_false_iff] at h
      obtain ⟨hdom, hf⟩ := h
      have hdom' : s1.memDomain a := by
        have hc : decide (s1.memDomain a) = true := by
          cases hd : decide (s1.memDomain a) with
          | false => rw [hd] at hdom; exact Bool.noConfusion hdom
          | true => rfl
        exact of_decide_eq_true hc
      have hf' : (readMemWord (resultWidth := 64) (a + 1) n s).2.failed = false := by
        rw [← hs1]; exact hf
      rcases k with _ | k
      · have hdom'' : s1.memDomain a := hdom'
        rw [hs1, readMemWord_memDomain] at hdom''
        simpa using hdom''
      · have hk' : k < n := by omega
        have hrec := ih (a + 1) s hbe hf' k hk'
        rw [show a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) by bv_omega] at hrec
        exact hrec

/-- The one-byte value of `readBytes`. -/
theorem readBytes_one (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 1 = (m a).setWidth 64 := by
  simp [readBytes]

/-- The two-byte value of `readBytes`. -/
theorem readBytes_two (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 2 = (m (a + 1)).setWidth 64 <<< (8 : Nat) ||| (m a).setWidth 64 := by
  simp [readBytes]

/-- The four-byte value of `readBytes`. -/
theorem readBytes_four (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 4 = (m (a + 3)).setWidth 64 <<< (24 : Nat) |||
      (m (a + 2)).setWidth 64 <<< (16 : Nat) |||
      (m (a + 1)).setWidth 64 <<< (8 : Nat) ||| (m a).setWidth 64 := by
  simp only [readBytes, Nat.reduceAdd, zero64, BitVec.zero_shiftLeft, BitVec.zero_or,
    BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, BitVec.or_assoc]
  rw [show a + 1 + 1 + 1 = a + 3 by bv_omega, show a + 1 + 1 = a + 2 by bv_omega]

/-- The eight-byte value of `readBytes`. -/
theorem readBytes_eight (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    readBytes m a 8 = (m (a + 7)).setWidth 64 <<< (56 : Nat) |||
      (m (a + 6)).setWidth 64 <<< (48 : Nat) |||
      (m (a + 5)).setWidth 64 <<< (40 : Nat) |||
      (m (a + 4)).setWidth 64 <<< (32 : Nat) |||
      (m (a + 3)).setWidth 64 <<< (24 : Nat) |||
      (m (a + 2)).setWidth 64 <<< (16 : Nat) |||
      (m (a + 1)).setWidth 64 <<< (8 : Nat) ||| (m a).setWidth 64 := by
  simp only [readBytes, Nat.reduceAdd, zero64, BitVec.zero_shiftLeft, BitVec.zero_or,
    BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, BitVec.or_assoc]
  rw [show a + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a + 7 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 + 1 = a + 6 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 = a + 5 by bv_omega,
    show a + 1 + 1 + 1 + 1 = a + 4 by bv_omega,
    show a + 1 + 1 + 1 = a + 3 by bv_omega,
    show a + 1 + 1 = a + 2 by bv_omega]

/-- The machine reads one byte as `readBytes` does. -/
theorem readMemN_one (s : Arm8State) (a : BitVec 64) : readMemN s 1 a = readBytes s.mem a 1 := by
  rw [readBytes_one]; rfl

/-- The machine reads two bytes as `readBytes` does. -/
theorem readMemN_two (s : Arm8State) (a : BitVec 64) : readMemN s 2 a = readBytes s.mem a 2 := by
  rw [readBytes_two]; rfl

/-- The machine reads four bytes as `readBytes` does. -/
theorem readMemN_four (s : Arm8State) (a : BitVec 64) : readMemN s 4 a = readBytes s.mem a 4 := by
  rw [readBytes_four]; rfl

/-- The machine reads eight bytes as `readBytes` does. -/
theorem readMemN_eight (s : Arm8State) (a : BitVec 64) : readMemN s 8 a = readBytes s.mem a 8 := by
  rw [readBytes_eight]; rfl


/-! ## The machine writes, byte by byte

`writeMemWord` writes byte `k` from `value >>> (8 * k)` at `a + k`; the machine's
`writeMemN` writes the same bytes through an explicit chain of `if`s.  The
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

/-- A machine state whose only content is the memory: `readMemN` and `writeMemN`
never look at anything else. -/
def memState (m : BitVec 64 → BitVec 8) : Arm8State where
  regs := fun _ => 0
  pc := 0
  n := false
  z := false
  c := false
  v := false
  mem := m
  memDomain := fun _ => False
  failed := false

/-- A one-byte source store is the machine's one-byte write. -/
theorem writeMemWord_mem_one (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 1 v s).mem x = (writeMemN (memState m) 1 a v).mem x := by
  simp only [writeMemWord, writeMemN, memState, updMem_mem, assertState_mem]
  simp [hm]

/-- A two-byte source store is the machine's two-byte write. -/
theorem writeMemWord_mem_two (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 2 v s).mem x = (writeMemN (memState m) 2 a v).mem x := by
  simp only [writeMemWord, writeMemN, memState, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, if_false]
  simp [hm]

/-- A four-byte source store is the machine's four-byte write. -/
theorem writeMemWord_mem_four (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 4 v s).mem x = (writeMemN (memState m) 4 a v).mem x := by
  simp only [writeMemWord, writeMemN, memState, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, if_false]
  rw [show a + 1 + 1 + 1 = a + 3 by bv_omega, show a + 1 + 1 = a + 2 by bv_omega]
  rw [byteShift v 1, byteShift v 0]
  simp [hm]

/-- An eight-byte source store is the machine's eight-byte write. -/
theorem writeMemWord_mem_eight (s : AsmState 64) (m : BitVec 64 → BitVec 8) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a 8 v s).mem x = (writeMemN (memState m) 8 a v).mem x := by
  simp only [writeMemWord, writeMemN, memState, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, if_false]
  rw [show a + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a + 7 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 + 1 = a + 6 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 = a + 5 by bv_omega,
    show a + 1 + 1 + 1 + 1 = a + 4 by bv_omega,
    show a + 1 + 1 + 1 = a + 3 by bv_omega,
    show a + 1 + 1 = a + 2 by bv_omega]
  rw [byteShift v 1, byteShift v 2, byteShift v 3, byteShift v 4, byteShift v 5,
    byteShift v 6, byteShift v 0]
  simp [hm]

/-- The source store and the machine store agree at every byte count the
lowering emits. -/
theorem writeMemWord_memSize (s : AsmState 64) (m : BitVec 64 → BitVec 8) (size : Nat)
    (hsize : size < 4) (a v x : BitVec 64) (hbe : s.be = false) (hm : s.mem x = m x) :
    (writeMemWord (valueWidth := 64) a (2 ^ size) v s).mem x =
      (writeMemN (memState m) (2 ^ size) a v).mem x := by
  interval_cases size
  · exact writeMemWord_mem_one s m a v x hm
  · exact writeMemWord_mem_two s m a v x hbe hm
  · exact writeMemWord_mem_four s m a v x hbe hm
  · exact writeMemWord_mem_eight s m a v x hbe hm

/-! ## The machine reads -/

/-- The machine reads `2 ^ size` bytes as `readBytes` does. -/
theorem readMemN_eq (s : Arm8State) (size : Nat) (hsize : size < 4) (a : BitVec 64) :
    readMemN s (2 ^ size) a = readBytes s.mem a (2 ^ size) := by
  interval_cases size
  · exact readMemN_one s a
  · exact readMemN_two s a
  · exact readMemN_four s a
  · exact readMemN_eight s a

/-- `readBytes` only looks at the bytes at `a`, `a + 1`, ... -/
theorem readBytes_congr (m m' : BitVec 64 → BitVec 8) (a : BitVec 64) (n : Nat)
    (h : ∀ k, k < n → m (a + BitVec.ofNat 64 k) = m' (a + BitVec.ofNat 64 k)) :
    readBytes m a n = readBytes m' a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      have h0 : m a = m' a := by simpa using h 0 (by omega)
      have hrec : readBytes m (a + 1) n = readBytes m' (a + 1) n := by
        refine ih (a + 1) ?_
        intro k hk
        have hk' := h (k + 1) (by omega)
        rwa [show a + BitVec.ofNat 64 (k + 1) = a + 1 + BitVec.ofNat 64 k by bv_omega] at hk'
      simp only [readBytes]
      rw [hrec, h0]

/-- The value a source load assembles is the value the machine load assembles:
the addresses agree, and the bytes the source read are in the domain, where the
initial state relation states that the two memories agree. -/
theorem readValue_agree (a : BitVec 64) (size : Nat) (hsize : size < 4) (s : AsmState 64)
    (ms : Arm8State) (hbe : s.be = false)
    (hdom : ∀ k, k < 2 ^ size → s.memDomain (a + BitVec.ofNat 64 k))
    (hmem : ∀ x, s.memDomain x → ms.mem x = s.mem x) :
    (readMemWord (resultWidth := 64) a (2 ^ size) s).1 = readMemN ms (2 ^ size) a := by
  rw [readMemWord_fst a (2 ^ size) s hbe, readMemN_eq ms size hsize]
  exact readBytes_congr _ _ _ _ (fun k hk => (hmem _ (hdom k hk)).symm)

/-! ## The offset window of `asm_ok` -/

/-- The `asm_ok` offset window `[-4351, 4350]` of the word- and half-word-sized
memory forms. -/
theorem offsetBounds_4351 (al : Nat) (off : BitVec 64)
    (h : asmOffsetOkExact al ((-4351 : BitVec 64), (4350 : BitVec 64)) off = true) :
    (-4351 : Int) ≤ off.toInt ∧ off.toInt ≤ 4350 := by
  simp only [asmOffsetOkExact, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlo, hhi⟩, -⟩ := h
  have hl : ((-4351 : BitVec 64)).toInt = -4351 := by decide
  have hh : ((4350 : BitVec 64)).toInt = 4350 := by decide
  rw [hl] at hlo
  rw [hh] at hhi
  exact ⟨hlo, hhi⟩

/-- The `asm_ok` offset window `[-256, 4095]` of the byte-sized memory forms. -/
theorem offsetBounds_256 (al : Nat) (off : BitVec 64)
    (h : asmOffsetOkExact al ((-256 : BitVec 64), (4095 : BitVec 64)) off = true) :
    (-256 : Int) ≤ off.toInt ∧ off.toInt ≤ 4095 := by
  simp only [asmOffsetOkExact, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlo, hhi⟩, -⟩ := h
  have hl : ((-256 : BitVec 64)).toInt = -256 := by decide
  have hh : ((4095 : BitVec 64)).toInt = 4095 := by decide
  rw [hl] at hlo
  rw [hh] at hhi
  exact ⟨hlo, hhi⟩

/-- `asm_ok` puts the destination and the base register in range of the
encoder. -/
theorem memRegOk_of_asm (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (h : asmOkExact (.inst (.mem op r (.addr base off))) arm8Config = true) :
    asmRegOkExact r arm8Config = true ∧ asmRegOkExact base arm8Config = true := by
  cases op <;>
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h
  all_goals exact ⟨h.1.1, h.1.2⟩

/-- `asm_ok` bounds the offset of every word- and half-word-sized memory form by
`[-4351, 4350]`. -/
theorem memOffset_of_asm (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (h1 : op ≠ .load8) (h2 : op ≠ .store8)
    (h : asmOkExact (.inst (.mem op r (.addr base off))) arm8Config = true) :
    (-4351 : Int) ≤ off.toInt ∧ off.toInt ≤ 4350 := by
  cases op with
  | load8 => exact absurd rfl h1
  | store8 => exact absurd rfl h2
  | load =>
      simp only [asmOkExact, asmInstOkExact] at h
      simp at h
      exact offsetBounds_4351 0 off
        (by simpa only [asmAddrOffsetOkExact, arm8Config] using h.2)
  | store =>
      simp only [asmOkExact, asmInstOkExact] at h
      simp at h
      exact offsetBounds_4351 0 off
        (by simpa only [asmAddrOffsetOkExact, arm8Config] using h.2)
  | load32 =>
      simp only [asmOkExact, asmInstOkExact] at h
      simp at h
      exact offsetBounds_4351 0 off
        (by simpa only [asmAddrOffsetOkExact, arm8Config] using h.2)
  | store32 =>
      simp only [asmOkExact, asmInstOkExact] at h
      simp at h
      exact offsetBounds_4351 0 off
        (by simpa only [asmAddrOffsetOkExact, arm8Config] using h.2)
  | load16 =>
      simp only [asmOkExact, asmInstOkExact] at h
      simp at h
      exact offsetBounds_4351 0 off
        (by simpa only [asmHwOffsetOkExact, arm8Config] using h.2.1)
  | store16 =>
      simp only [asmOkExact, asmInstOkExact] at h
      simp at h
      exact offsetBounds_4351 0 off
        (by simpa only [asmHwOffsetOkExact, arm8Config] using h.2.1)

/-- `asm_ok` bounds the offset of the byte-sized memory forms by
`[-256, 4095]`. -/
theorem memByteOffset_of_asm (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (h1 : op = .load8 ∨ op = .store8)
    (h : asmOkExact (.inst (.mem op r (.addr base off))) arm8Config = true) :
    (-256 : Int) ≤ off.toInt ∧ off.toInt ≤ 4095 := by
  rcases h1 with hl | hl
  · subst hl
    simp only [asmOkExact, asmInstOkExact] at h
    simp at h
    exact offsetBounds_256 0 off
      (by simpa only [asmByteOffsetOkExact, arm8Config] using h.2)
  · subst hl
    simp only [asmOkExact, asmInstOkExact] at h
    simp at h
    exact offsetBounds_256 0 off
      (by simpa only [asmByteOffsetOkExact, arm8Config] using h.2)

/-- A nine-bit signed offset in range. -/
theorem fitsSigned9_of_range {off : BitVec 64} (h1 : (-256 : Int) ≤ off.toInt)
    (h2 : off.toInt ≤ 255) : fitsSigned 9 off = true :=
  fitsSigned_of_range 9 off (by decide) (by decide) h1 h2

/-- A nine-bit signed offset out of range. -/
theorem not_fitsSigned9 {off : BitVec 64} (h : fitsSigned 9 off = false) :
    off.toInt < -256 ∨ 255 < off.toInt := by
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  exact absurd (fitsSigned9_of_range hc.1 hc.2) (by rw [h]; exact Bool.noConfusion)


/-! ## Executing the emitted forms -/

/-- Executing a loading `loadStoreImmediate`. -/
theorem execInsn_loadStoreImmediate_load (s : Arm8State) (size : Nat) (rg : Bool)
    (sg u : Bool) (off : W) (rn rt : Nat) :
    execInsn s (.loadStoreImmediate size rg .load sg u off rn rt) =
      writeReg s rt (readMemN s (2 ^ size) (readReg s rn + off)) := by
  simp only [execInsn]

/-- Executing a storing `loadStoreImmediate`. -/
theorem execInsn_loadStoreImmediate_store (s : Arm8State) (size : Nat) (rg : Bool)
    (sg u : Bool) (off : W) (rn rt : Nat) :
    execInsn s (.loadStoreImmediate size rg .store sg u off rn rt) =
      writeMemN s (2 ^ size) (readReg s rn + off) (readReg s rt) := by
  simp only [execInsn]

/-- The `loadStoreImmediate` forms are flag-blind: the `regsize`, `signed` and
`unsignedOffset` fields do not affect the executed transition. -/
theorem execInsn_loadStoreImmediate_flags (s : Arm8State) (size : Nat) (rg rg' : Bool)
    (memop : MemOp) (sg sg' u u' : Bool) (off : W) (rn rt : Nat) :
    execInsn s (.loadStoreImmediate size rg memop sg u off rn rt) =
      execInsn s (.loadStoreImmediate size rg' memop sg' u' off rn rt) := by
  cases memop <;> simp only [execInsn]

/-- The `loadStoreImmediate` forms are flag-blind for the memory they touch. -/
theorem arm8Touched_loadStoreImmediate_flags (s : Arm8State) (size : Nat) (rg rg' : Bool)
    (memop memop' : MemOp) (sg sg' u u' : Bool) (off : W) (rn rt rt' : Nat) :
    arm8Touched s (.loadStoreImmediate size rg memop sg u off rn rt) =
      arm8Touched s (.loadStoreImmediate size rg' memop' sg' u' off rn rt') := by
  simp only [arm8Touched]

/-- The encodings of a `loadStoreImmediate` agree when the unsigned form is not
taken: the encoder falls through to the signed form either way. -/
theorem encodeBytes_mem_true_false (size : Nat) (rg : Bool) (memop : MemOp) (off : W)
    (rn rt : Nat) (hfits : fitsSigned 9 off = true)
    (hne : off ≠ (BitVec.ofNat 64 ((off >>> size).toNat % 4096)) <<< size) :
    encodeBytes (.loadStoreImmediate size rg memop false true off rn rt) =
      encodeBytes (.loadStoreImmediate size rg memop false false off rn rt) := by
  have hd : decide (off = (BitVec.ofNat 64 ((off >>> size).toNat % 4096)) <<< size) = false :=
    decide_eq_false_iff_not.mpr hne
  have hi : encodeInsn (.loadStoreImmediate size rg memop false true off rn rt) =
      encodeInsn (.loadStoreImmediate size rg memop false false off rn rt) := by
    simp only [encodeInsn, encodeInsn32, hfits, hd, Bool.and_false, if_true]
  simp only [encodeBytes, hi]

/-- One machine step executes an unsigned-offset memory instruction whose scaled
offset is exactly the instruction's offset. -/
theorem arm8Next_memUnsigned (s : Arm8State) (d : BitVec 64 → Prop) (size : Nat) (rg : Bool)
    (memop : MemOp) (off : W) (rn rt : Nat) (hsize : size < 4) (hrn : rn < 32)
    (hrt : rt < 32)
    (hshape : off = (BitVec.ofNat 64 ((off >>> size).toNat % 4096)) <<< size)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size rg memop false true off rn rt)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.loadStoreImmediate size rg memop false true off rn rt) := by
  have hrg : encodeBytes (.loadStoreImmediate size rg memop false true off rn rt) =
      encodeBytes (.loadStoreImmediate size false memop false true off rn rt) := rfl
  have hb : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size false memop false true off rn rt)) s.mem d := by
    rw [← hrg]; exact hbytes
  rw [arm8Next_loadStoreImmediateUnsigned s d size false memop off rn rt hsize rfl hrn hrt
    hshape hb]
  exact execInsn_loadStoreImmediate_flags { s with pc := s.pc + 4 } size false rg memop
    false false true true off rn rt

/-- One machine step executes a signed-offset memory instruction encoded in its
signed form. -/
theorem arm8Next_memSigned (s : Arm8State) (d : BitVec 64 → Prop) (size : Nat) (rg : Bool)
    (memop : MemOp) (off : W) (rn rt : Nat) (hsize : size < 4) (hrn : rn < 32)
    (hrt : rt < 32) (hfits : fitsSigned 9 off = true)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size rg memop false false off rn rt)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.loadStoreImmediate size rg memop false false off rn rt) := by
  have hrg : encodeBytes (.loadStoreImmediate size rg memop false false off rn rt) =
      encodeBytes (.loadStoreImmediate size false memop false false off rn rt) := rfl
  have hb : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size false memop false false off rn rt)) s.mem d := by
    rw [← hrg]; exact hbytes
  rw [arm8Next_loadStoreImmediateSigned s d size false memop off rn rt hsize rfl hrn hrt
    hfits hb]
  exact execInsn_loadStoreImmediate_flags { s with pc := s.pc + 4 } size false rg memop
    false false false false off rn rt

/-- One machine step executes a memory instruction whose offset does not fit the
unsigned form, although the lowering set the unsigned bit. -/
theorem arm8Next_memSignedTrue (s : Arm8State) (d : BitVec 64 → Prop) (size : Nat)
    (rg : Bool) (memop : MemOp) (off : W) (rn rt : Nat) (hsize : size < 4)
    (hrn : rn < 32) (hrt : rt < 32) (hfits : fitsSigned 9 off = true)
    (hne : off ≠ (BitVec.ofNat 64 ((off >>> size).toNat % 4096)) <<< size)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size rg memop false true off rn rt)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.loadStoreImmediate size rg memop false true off rn rt) := by
  have hb : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size rg memop false false off rn rt)) s.mem d := by
    rw [← encodeBytes_mem_true_false size rg memop off rn rt hfits hne]
    exact hbytes
  rw [arm8Next_memSigned s d size rg memop off rn rt hsize hrn hrt hfits hb]
  exact execInsn_loadStoreImmediate_flags { s with pc := s.pc + 4 } size false rg memop
    false false true true off rn rt

/-- One machine step executes the small load/store of the two-instruction
lowering: the temporary register's value plus the small offset is the effective
address. -/
theorem arm8Next_memSecond (s : Arm8State) (d : BitVec 64 → Prop) (size : Nat) (rg : Bool)
    (memop : MemOp) (u : Bool) (c : W) (rn rt : Nat) (hsize : size < 4) (hrn : rn < 32)
    (hrt : rt < 32) (hfits : fitsSigned 9 c = true)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.loadStoreImmediate size rg memop false u c rn rt)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.loadStoreImmediate size rg memop false u c rn rt) := by
  by_cases hsc : c = (BitVec.ofNat 64 ((c >>> size).toNat % 4096)) <<< size
  · cases u
    · exact arm8Next_memSigned s d size rg memop c rn rt hsize hrn hrt hfits hbytes
    · exact arm8Next_memUnsigned s d size rg memop c rn rt hsize hrn hrt hsc hbytes
  · cases u
    · exact arm8Next_memSigned s d size rg memop c rn rt hsize hrn hrt hfits hbytes
    · exact arm8Next_memSignedTrue s d size rg memop c rn rt hsize hrn hrt hfits hsc hbytes

/-- The scaled offset of a memory instruction. -/
abbrev scaledOff (size : Nat) (off : W) : W :=
  (BitVec.ofNat 64 ((off >>> size).toNat % 4096)) <<< size

/-- `encodeBytes` is the four bytes of the encoded word. -/
theorem encodeBytes_getD (i : Insn) :
    encodeBytes i = wordBytes ((encodeInsn i).getD 0) := by
  cases h : encodeInsn i with
  | none => simp only [encodeBytes, h, Option.getD_none, wordBytes]; decide
  | some w => simp only [encodeBytes, h, Option.getD_some]

/-- The fetched word is the encoding word of any instruction whose bytes are at
the PC. -/
theorem fetchWord_wordBytes' (s : Arm8State) (w : W) (d : BitVec 64 → Prop)
    (h : bytesInMemoryHOL s.pc (wordBytes w) s.mem d) : fetchWord s = w.setWidth 32 := by
  simp only [wordBytes, bytesInMemoryHOL] at h
  rcases h with ⟨h0, _, h1, _, h2, _, h3, _⟩
  have h2' : s.mem (s.pc + 2) = w.extractLsb' 16 8 := by simpa [BitVec.add_assoc] using h2
  have h3' : s.mem (s.pc + 3) = w.extractLsb' 24 8 := by simpa [BitVec.add_assoc] using h3
  exact fetchWord_wordBytes s w h0 h1 h2' h3'

/-- The instruction decoded at the PC is the one whose encoding the bytes hold. -/
theorem decode_fetchWord_getD (s : Arm8State) (i : Insn) (d : BitVec 64 → Prop)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes i) s.mem d)
    (hdec : decodeInsn ((encodeInsn i).getD 0) = some i) :
    decodeInsn32 (fetchWord s) = some i := by
  have hb : bytesInMemoryHOL s.pc (wordBytes ((encodeInsn i).getD 0)) s.mem d := by
    rw [← encodeBytes_getD]; exact hbytes
  rw [fetchWord_wordBytes' s _ d hb]
  rw [show decodeInsn32 (((encodeInsn i).getD 0).setWidth 32) =
    decodeInsn ((encodeInsn i).getD 0) from by simp [decodeInsn]]
  exact hdec

/-- One machine step executes a memory instruction, in the canonical form the
decoder produces. -/
theorem arm8Next_memCanonical (s : Arm8State) (d : BitVec 64 → Prop) (size : Nat)
    (memop : MemOp) (off : W) (rn rt : Nat) (hsize : size < 4) (hrn : rn < 32)
    (hrt : rt < 32) (hform : off = scaledOff size off ∨ fitsSigned 9 off = true)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.loadStoreImmediate size false memop
      false (decide (off = scaledOff size off)) off rn rt)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.loadStoreImmediate size false memop false (decide (off = scaledOff size off)) off rn rt) := by
  by_cases h : off = scaledOff size off
  · rw [decide_eq_true h] at hbytes ⊢
    exact arm8Next_memUnsigned s d size false memop off rn rt hsize hrn hrt h hbytes
  · rw [decide_eq_false h] at hbytes ⊢
    rcases hform with h1 | h2
    · exact absurd h1 h
    · exact arm8Next_memSigned s d size false memop off rn rt hsize hrn hrt h2 hbytes

/-- A state whose bytes at the PC are a memory instruction is step-safe once the
bytes the instruction touches are in the domain. -/
theorem stepSafe_mem (s : Arm8State) (d : BitVec 64 → Prop) (size : Nat) (memop : MemOp)
    (off : W) (rn rt : Nat)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.loadStoreImmediate size false memop
      false (decide (off = scaledOff size off)) off rn rt)) s.mem d)
    (hdec : decodeInsn ((encodeInsn (.loadStoreImmediate size false memop false
      (decide (off = scaledOff size off)) off rn rt)).getD 0)
      = some (.loadStoreImmediate size false memop false
        (decide (off = scaledOff size off)) off rn rt))
    (htouch : ∀ a, a ∈ arm8Touched s (.loadStoreImmediate size false memop false
      (decide (off = scaledOff size off)) off rn rt) → d a) :
    StepSafe d s := by
  have hdecf := decode_fetchWord_getD s _ d hbytes hdec
  have hdom := bytesInMemoryHOL_domain hbytes
  have hlen := encodeBytes_length (.loadStoreImmediate size false memop false
    (decide (off = scaledOff size off)) off rn rt)
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hdom 0 (by rw [hlen]; omega)
    · simpa using hdom 1 (by rw [hlen]; omega)
    · simpa using hdom 2 (by rw [hlen]; omega)
    · simpa using hdom 3 (by rw [hlen]; omega)
  · intro i hi x hx
    rw [hdecf] at hi
    cases hi
    exact htouch x hx

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
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
  exact readMemWord_domain (s1.regs base + off) (2 ^ size) s1 hbe hf


/-- The PC does not affect the machine's memory reads. -/
theorem readMemN_pcUpdate (s : Arm8State) (pc : BitVec 64) (n : Nat) (a : BitVec 64) :
    readMemN { s with pc := pc } n a = readMemN s n a := rfl

/-- A machine memory write leaves the register file alone. -/
theorem writeMemN_regs (s : Arm8State) (n : Nat) (a v : BitVec 64) :
    (writeMemN s n a v).regs = s.regs := by
  obtain _ | _ | _ | _ | _ | n := n <;> rfl

/-- A machine memory write leaves the failure flag alone. -/
theorem writeMemN_failed (s : Arm8State) (n : Nat) (a v : BitVec 64) :
    (writeMemN s n a v).failed = s.failed := by
  obtain _ | _ | _ | _ | _ | n := n <;> rfl

/-- A machine memory write preserves state validity. -/
theorem arm8StateOk_writeMemN (s : Arm8State) (n : Nat) (a v : BitVec 64) :
    arm8StateOk (writeMemN s n a v) = arm8StateOk s := by
  obtain _ | _ | _ | _ | _ | n := n <;> rfl

/-- A machine memory write leaves the PC alone. -/
theorem writeMemN_pc (s : Arm8State) (n : Nat) (a v : BitVec 64) :
    (writeMemN s n a v).pc = s.pc := by
  obtain _ | _ | _ | _ | _ | n := n <;> rfl

/-- The machine's memory write depends on the state only through its memory. -/
theorem writeMemN_mem_of_mem (s t : Arm8State) (h : s.mem = t.mem) (n : Nat) (a v : BitVec 64)
    (x : BitVec 64) : (writeMemN s n a v).mem x = (writeMemN t n a v).mem x := by
  obtain _ | _ | _ | _ | _ | n := n <;> simp only [writeMemN, h]

/-- A load lowered to a single memory instruction. -/
theorem case_memLoadOne (op : HolMemop) (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64)
    (ms : Arm8State) (size : Nat)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (hsize : size < 4)
    (hform : off = scaledOff size off ∨ fitsSigned 9 off = true)
    (hast : arm8Enc (.inst (.mem op r (.addr base off))) =
      encodeBytes (.loadStoreImmediate size false .load false
        (decide (off = scaledOff size off)) off base r))
    (hdom : ∀ k, k < 2 ^ size → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k))
    (h : asmStep arm8Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hokr, hokb⟩ := memRegOk_of_asm op r base off st.asmOk
  obtain ⟨hrlt, hrav, hrne⟩ := regOk_of_asm hokr
  obtain ⟨hblt, hbav, hbne⟩ := regOk_of_asm hokb
  have hr32 : r < 32 := by simpa [arm8Config] using hrlt
  have hb32 : base < 32 := by simpa [arm8Config] using hblt
  have hbdom : base < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains base = false := by
    simpa [arm8Target_config] using (show base < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains base = false from ⟨hblt, hbav⟩)
  have hrdom : r < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains r = false := by
    simpa [arm8Target_config] using (show r < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains r = false from ⟨hrlt, hrav⟩)
  have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 4 := by
    rw [hast]; exact encodeBytes_length _
  have hupd : asmUpd (.inst (.mem op r (.addr base off))) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 4 := by rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ i, s2.regs i =
      (if i = r then (readMemWord (s1.regs base + off) (2 ^ size) s1).1 else s1.regs i) := by
    intro i
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, st.be,
      Bool.false_eq_true, if_false]
  have hbase : ms.regs base = s1.regs base := st.reg base hbdom
  have hregr : ms.regs r = s1.regs r := st.reg r hrdom
  have haddr : readReg ms base + off = s1.regs base + off := by
    simp only [readReg, if_neg hbne, hbase]
  have hreadr : readReg ms r = s1.regs r := by
    simp only [readReg, if_neg hrne, hregr]
  have hvalue : (readMemWord (s1.regs base + off) (2 ^ size) s1).1 =
      readMemN ms (2 ^ size) (readReg ms base + off) := by
    rw [haddr]
    exact readValue_agree _ size hsize s1 ms st.be hdom st.mem
  have hbytes : bytesInMemoryHOL ms.pc (encodeBytes (.loadStoreImmediate size false .load false
      (decide (off = scaledOff size off)) off base r)) ms.mem s1.memDomain := by
    rw [← hast]; exact st.bytes
  have hdec : decodeInsn ((encodeInsn (.loadStoreImmediate size false .load false
      (decide (off = scaledOff size off)) off base r)).getD 0) =
      some (.loadStoreImmediate size false .load false
        (decide (off = scaledOff size off)) off base r) :=
    decode_encode_loadStoreImmediate size false .load off base r hsize rfl hb32 hr32 hform
  have htouch : ∀ a, a ∈ arm8Touched ms (.loadStoreImmediate size false .load false
      (decide (off = scaledOff size off)) off base r) → s1.memDomain a := by
    intro a ha
    have ha' : a ∈ bytesAt (readReg ms base + off) (2 ^ size) := by
      simpa only [arm8Touched] using ha
    simp only [bytesAt, List.mem_map, List.mem_range] at ha'
    obtain ⟨j, hj, rfl⟩ := ha'
    rw [haddr]
    exact hdom j hj
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.loadStoreImmediate size false .load false (decide (off = scaledOff size off)) off base r) :=
    arm8Next_memCanonical ms s1.memDomain size .load off base r hsize hb32 hr32 hform hbytes
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_mem ms s1.memDomain size .load off base r hbytes hdec htouch
  have hal4 : holAligned 2 (4 : BitVec 64) = true := aligned_of_mod 4 (by decide)
  have hal : holAligned 2 (ms.pc + 4) = true := by
    rw [(alignedAddSub 2 ms.pc 4 hal4).1, st.aligned]
  have hq1 : targetStateRel arm8Target s2 (arm8Next ms) := by
    rw [hnext, execInsn_loadStoreImmediate_load]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk, writeReg, if_neg hrne]
      exact arm8StateOk_set _ hal st.msFailed
    · simp only [writeReg, if_neg hrne]
      show ms.pc + 4 = s2.pc
      rw [st.pc, hs2pc]
    · intro x hx
      simp only [arm8Target_getByte, writeReg, if_neg hrne]
      show ms.mem x = s2.mem x
      rw [hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro i hi
      simp only [arm8Target_getReg, writeReg, if_neg hrne]
      by_cases hir : i = r
      · subst hir
        rw [if_pos rfl, readMemN_pcUpdate, readReg_pcUpdate, hs2regs i, if_pos rfl]
        exact hvalue.symm
      · rw [if_neg hir, hs2regs i, if_neg hir]
        exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  have hcode : allPcs (arm8Target.config.encode (.inst (.mem op r (.addr base off)))).length
      s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    have hi : arm8Next^[0 + 1] ms = arm8Next ms := by
      rw [Nat.zero_add, Function.iterate_one]
    rw [hi]
    exact hq1
  refine encoderCaseStep (.inst (.mem op r (.addr base off))) s1 s2 ms 0 hs2dom hcode ?_ ?_ hq
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hsafe0
  · intro k h1 h2
    omega


/-- A `Bool` equal to `false` is not `true`. -/
theorem not_of_eq_false {b : Bool} (h : b = false) : ¬b := by
  rw [h]
  intro h'
  exact Bool.noConfusion h'

/-- A store writes only bytes the source state has in its memory domain. -/
theorem writeMemWord_domain (a : BitVec 64) (n : Nat) (v : BitVec 64) (s : AsmState 64)
    (hbe : s.be = false) (h : ¬ (writeMemWord (valueWidth := 64) a n v s).failed) :
    ∀ k, k < n → s.memDomain (a + BitVec.ofNat 64 k) := by
  induction n generalizing a v s with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk
      rw [writeMemWord_succ] at h
      have hif : (if s.be then a - 1 else a + 1) = a + 1 := by
        rw [hbe]
        rw [if_neg (by decide : ¬((false : Bool) = true))]
      rw [hif] at h
      set s1 : AsmState 64 :=
        writeMemWord (valueWidth := 64) (a + 1) n (v >>> (8 : Nat)) s with hs1
      obtain ⟨hdom, hfl⟩ := not_failed_assertState h
      have hfl' : (writeMemWord (valueWidth := 64) (a + 1) n (v >>> (8 : Nat)) s).failed = false := by
        rw [updMem_failed] at hfl
        rw [← hs1]
        exact hfl
      have hdom' : s.memDomain a := by
        classical
        rw [hs1, writeMemWord_memDomain] at hdom
        exact of_decide_eq_true hdom
      rcases k with _ | k
      · simpa using hdom'
      · have hk' : k < n := by omega
        have hrec := ih (a + 1) (v >>> (8 : Nat)) s hbe (not_of_eq_false hfl') k hk'
        rw [show a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) by bv_omega] at hrec
        exact hrec

/-- `writeMemWord` preserves the register file. -/
theorem writeMemWord_regs (a : BitVec 64) (n : Nat) (v : BitVec 64) (s : AsmState 64) :
    (writeMemWord (valueWidth := 64) a n v s).regs = s.regs := by
  induction n generalizing a v s with
  | zero => rfl
  | succ n ih =>
      rw [writeMemWord_succ]
      simp only [assertState, updMem]
      exact ih _ _ _

/-- A store lowered to a single memory instruction. -/
theorem case_memStoreOne (op : HolMemop) (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64)
    (ms : Arm8State) (size : Nat)
    (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ size))
    (hsize : size < 4)
    (hform : off = scaledOff size off ∨ fitsSigned 9 off = true)
    (hast : arm8Enc (.inst (.mem op r (.addr base off))) =
      encodeBytes (.loadStoreImmediate size false .store false
        (decide (off = scaledOff size off)) off base r))
    (h : asmStep arm8Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hokr, hokb⟩ := memRegOk_of_asm op r base off st.asmOk
  obtain ⟨hrlt, hrav, hrne⟩ := regOk_of_asm hokr
  obtain ⟨hblt, hbav, hbne⟩ := regOk_of_asm hokb
  have hr32 : r < 32 := by simpa [arm8Config] using hrlt
  have hb32 : base < 32 := by simpa [arm8Config] using hblt
  have hbdom : base < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains base = false := by
    simpa [arm8Target_config] using (show base < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains base = false from ⟨hblt, hbav⟩)
  have hrdom : r < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains r = false := by
    simpa [arm8Target_config] using (show r < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains r = false from ⟨hrlt, hrav⟩)
  have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 4 := by
    rw [hast]; exact encodeBytes_length _
  have hupd : asmUpd (.inst (.mem op r (.addr base off))) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 4 := by rw [← hupd]; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs : ∀ i, s2.regs i = s1.regs i := by
    intro i
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2memWord : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) (2 ^ size) (s1.regs r) s1).mem x := by
    intro x
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, st.be, Bool.false_eq_true, if_false]
  have hbase : ms.regs base = s1.regs base := st.reg base hbdom
  have hregr : ms.regs r = s1.regs r := st.reg r hrdom
  have haddr : readReg ms base + off = s1.regs base + off := by
    simp only [readReg, if_neg hbne, hbase]
  have hvalr : readReg ms r = s1.regs r := by
    simp only [readReg, if_neg hrne, hregr]
  have hbytes : bytesInMemoryHOL ms.pc (encodeBytes (.loadStoreImmediate size false .store false
      (decide (off = scaledOff size off)) off base r)) ms.mem s1.memDomain := by
    rw [← hast]; exact st.bytes
  have hdec : decodeInsn ((encodeInsn (.loadStoreImmediate size false .store false
      (decide (off = scaledOff size off)) off base r)).getD 0) =
      some (.loadStoreImmediate size false .store false
        (decide (off = scaledOff size off)) off base r) :=
    decode_encode_loadStoreImmediate size false .store off base r hsize rfl hb32 hr32 hform
  have hfail : s2.failed = false := boolOfNotTrue st.ok
  have hfailW : (writeMemWord (valueWidth := 64) (s1.regs base + off) (2 ^ size) (s1.regs r)
      s1).failed = false := by
    rw [← hupd] at hfail
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, st.be, Bool.false_eq_true, if_false] at hfail
    obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
    exact hf
  have hdomW := writeMemWord_domain (s1.regs base + off) (2 ^ size) (s1.regs r) s1 st.be
    (not_of_eq_false hfailW)
  have htouch : ∀ a, a ∈ arm8Touched ms (.loadStoreImmediate size false .store false
      (decide (off = scaledOff size off)) off base r) → s1.memDomain a := by
    intro a ha
    have ha' : a ∈ bytesAt (readReg ms base + off) (2 ^ size) := by
      simpa only [arm8Touched] using ha
    simp only [bytesAt, List.mem_map, List.mem_range] at ha'
    obtain ⟨j, hj, rfl⟩ := ha'
    rw [haddr]
    exact hdomW j hj
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.loadStoreImmediate size false .store false (decide (off = scaledOff size off)) off base r) :=
    arm8Next_memCanonical ms s1.memDomain size .store off base r hsize hb32 hr32 hform hbytes
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_mem ms s1.memDomain size .store off base r hbytes hdec htouch
  have hal4 : holAligned 2 (4 : BitVec 64) = true := aligned_of_mod 4 (by decide)
  have hal : holAligned 2 (ms.pc + 4) = true := by
    rw [(alignedAddSub 2 ms.pc 4 hal4).1, st.aligned]
  have hq1 : targetStateRel arm8Target s2 (arm8Next ms) := by
    rw [hnext, execInsn_loadStoreImmediate_store]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk, arm8StateOk_writeMemN]
      exact arm8StateOk_set _ hal st.msFailed
    · simp only [arm8Target_getPc, writeMemN_pc]
      show ms.pc + 4 = s2.pc
      rw [st.pc, hs2pc]
    · intro x hx
      simp only [arm8Target_getByte, readReg_pcUpdate]
      rw [hs2memWord x, haddr, hvalr]
      rw [writeMemWord_memSize s1 ms.mem size hsize (s1.regs base + off) (s1.regs r) x st.be
        (st.mem x (hs2dom ▸ hx)).symm]
      exact writeMemN_mem_of_mem (s := { ms with pc := ms.pc + 4 }) (t := memState ms.mem)
        rfl (2 ^ size) (s1.regs base + off) (s1.regs r) x
    · intro i hi
      simp only [arm8Target_getReg, writeMemN_regs]
      rw [hs2regs i]
      exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  have hcode : allPcs (arm8Target.config.encode (.inst (.mem op r (.addr base off)))).length
      s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    have hi : arm8Next^[0 + 1] ms = arm8Next ms := by
      rw [Nat.zero_add, Function.iterate_one]
    rw [hi]
    exact hq1
  refine encoderCaseStep (.inst (.mem op r (.addr base off))) s1 s2 ms 0 hs2dom hcode ?_ ?_ hq
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hsafe0
  · intro k h1 h2
    omega


/-- A byte offset in `[0, 4095]` is its own scaled form. -/
theorem eq_scaledOff_zero {off : W} (hmsb : off.msb = false) (hlo : 0 ≤ off.toInt)
    (hhi : off.toInt ≤ 4095) : off = scaledOff 0 off := by
  have htoNat : off.toInt = (off.toNat : Int) := BitVec.toInt_eq_toNat_of_msb hmsb
  have hle : off.toNat ≤ 4095 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [scaledOff, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, BitVec.toNat_ofNat]
  omega

/-- A scaled byte offset is non-negative. -/
theorem scaledOff_zero_toInt_nonneg (off : W) : 0 ≤ (scaledOff 0 off).toInt := by
  have hnat : (scaledOff 0 off).toNat ≤ 4095 := by
    simp only [scaledOff, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, BitVec.toNat_ofNat]
    omega
  have hmsb : (scaledOff 0 off).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    omega
  rw [BitVec.toInt_eq_toNat_of_msb hmsb]
  exact Int.natCast_nonneg _

/-- An eight-bit load. -/
theorem case_load8 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .load8 r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .load8 r (.addr base off))) s1 s2 ms := by
  have st := arm8Start _ s1 s2 ms h
  have hast0 : arm8Enc (.inst (.mem .load8 r (.addr base off))) =
      encodeBytes (.loadStoreImmediate 0 false .load false (!off.msb) off base r) := by
    simp [arm8Enc, arm8Ast, arm8Inst]
  have hlen : (arm8Enc (.inst (.mem .load8 r (.addr base off)))).length = 4 := by
    rw [hast0]; exact encodeBytes_length _
  have hupd : asmUpd (.inst (.mem .load8 r (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  obtain ⟨hlo, hhi⟩ := memByteOffset_of_asm .load8 r base off (Or.inl rfl) st.asmOk
  have hdom := memLoadDomain .load8 r base off s1 s2 0 (s1.pc + BitVec.ofNat 64 4) rfl hupd
    st.be st.ok
  by_cases hmsb : off.msb = true
  · have hfits : fitsSigned 9 off = true :=
      fitsSigned9_of_range hlo (by have := BitVec.toInt_neg_of_msb_true hmsb; omega)
    have hne : ¬(off = scaledOff 0 off) := by
      intro hc
      have h1 : 0 ≤ (scaledOff 0 off).toInt := scaledOff_zero_toInt_nonneg off
      rw [← hc] at h1
      have h2 : off.toInt < 0 := BitVec.toInt_neg_of_msb_true hmsb
      omega
    have hfalse : (!off.msb) = false := by rw [hmsb]; rfl
    have hdec : decide (off = scaledOff 0 off) = false := by
      rw [decide_eq_false_iff_not]
      exact hne
    have hast : arm8Enc (.inst (.mem .load8 r (.addr base off))) =
        encodeBytes (.loadStoreImmediate 0 false .load false
          (decide (off = scaledOff 0 off)) off base r) := by
      rw [hast0, hfalse, hdec]
    exact case_memLoadOne .load8 r base off s1 s2 ms 0 rfl (by decide) (Or.inr hfits) hast hdom h
  · have hmsbf : off.msb = false := by
      cases hh : off.msb with
      | false => rfl
      | true => exact absurd hh hmsb
    have hshape : off = scaledOff 0 off :=
      eq_scaledOff_zero hmsbf (BitVec.toInt_nonneg_of_msb_false hmsbf) hhi
    have htrue : (!off.msb) = true := by rw [hmsbf]; rfl
    have hdec : decide (off = scaledOff 0 off) = true := decide_eq_true hshape
    have hast : arm8Enc (.inst (.mem .load8 r (.addr base off))) =
        encodeBytes (.loadStoreImmediate 0 false .load false
          (decide (off = scaledOff 0 off)) off base r) := by
      rw [hast0, htrue, hdec]
    exact case_memLoadOne .load8 r base off s1 s2 ms 0 rfl (by decide) (Or.inl hshape) hast hdom h

/-- An eight-bit store. -/
theorem case_store8 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .store8 r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .store8 r (.addr base off))) s1 s2 ms := by
  have st := arm8Start _ s1 s2 ms h
  have hast0 : arm8Enc (.inst (.mem .store8 r (.addr base off))) =
      encodeBytes (.loadStoreImmediate 0 false .store false (!off.msb) off base r) := by
    simp [arm8Enc, arm8Ast, arm8Inst]
  have hlen : (arm8Enc (.inst (.mem .store8 r (.addr base off)))).length = 4 := by
    rw [hast0]; exact encodeBytes_length _
  have hupd : asmUpd (.inst (.mem .store8 r (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  obtain ⟨hlo, hhi⟩ := memByteOffset_of_asm .store8 r base off (Or.inr rfl) st.asmOk
  by_cases hmsb : off.msb = true
  · have hfits : fitsSigned 9 off = true :=
      fitsSigned9_of_range hlo (by have := BitVec.toInt_neg_of_msb_true hmsb; omega)
    have hne : ¬(off = scaledOff 0 off) := by
      intro hc
      have h1 : 0 ≤ (scaledOff 0 off).toInt := scaledOff_zero_toInt_nonneg off
      rw [← hc] at h1
      have h2 : off.toInt < 0 := BitVec.toInt_neg_of_msb_true hmsb
      omega
    have hfalse : (!off.msb) = false := by rw [hmsb]; rfl
    have hdec : decide (off = scaledOff 0 off) = false := by
      rw [decide_eq_false_iff_not]
      exact hne
    have hast : arm8Enc (.inst (.mem .store8 r (.addr base off))) =
        encodeBytes (.loadStoreImmediate 0 false .store false
          (decide (off = scaledOff 0 off)) off base r) := by
      rw [hast0, hfalse, hdec]
    exact case_memStoreOne .store8 r base off s1 s2 ms 0 rfl (by decide) (Or.inr hfits) hast h
  · have hmsbf : off.msb = false := by
      cases hh : off.msb with
      | false => rfl
      | true => exact absurd hh hmsb
    have hshape : off = scaledOff 0 off :=
      eq_scaledOff_zero hmsbf (BitVec.toInt_nonneg_of_msb_false hmsbf) hhi
    have htrue : (!off.msb) = true := by rw [hmsbf]; rfl
    have hdec : decide (off = scaledOff 0 off) = true := decide_eq_true hshape
    have hast : arm8Enc (.inst (.mem .store8 r (.addr base off))) =
        encodeBytes (.loadStoreImmediate 0 false .store false
          (decide (off = scaledOff 0 off)) off base r) := by
      rw [hast0, htrue, hdec]
    exact case_memStoreOne .store8 r base off s1 s2 ms 0 rfl (by decide) (Or.inl hshape) hast h


/-- The emitted word of a signed-offset memory instruction does not depend on
the unsigned-offset flag when the offset is not its own scaled form. -/
theorem encodeInsn_loadStoreImmediateSignedAny (size : Nat) (rg : Bool) (memop : MemOp)
    (u : Bool) (c : W) (rn rt : Nat) (hfits : fitsSigned 9 c = true)
    (hne : c ≠ scaledOff size c) :
    encodeInsn (.loadStoreImmediate size rg memop false u c rn rt) =
      some ((fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
        (9, c.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]).setWidth 64) := by
  have hp : decide (c = scaledOff size c) = false := by
    rw [decide_eq_false_iff_not]
    exact hne
  unfold encodeInsn
  rw [show encodeInsn32 (.loadStoreImmediate size rg memop false u c rn rt)
      = some (fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
          (9, c.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]) by
    simp only [encodeInsn32, loadStoreOpc, hp, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, hfits]
    cases memop <;> rfl]
  rfl

/-- The emitted bytes of a signed-offset memory instruction do not depend on the
unsigned-offset flag when the offset is not its own scaled form. -/
theorem encodeBytes_loadStoreImmediate_flag (size : Nat) (memop : MemOp) (u : Bool)
    (c : W) (rn rt : Nat) (hfits : fitsSigned 9 c = true) (hne : c ≠ scaledOff size c) :
    encodeBytes (.loadStoreImmediate size false memop false u c rn rt) =
      encodeBytes (.loadStoreImmediate size false memop false false c rn rt) := by
  rw [show encodeBytes (.loadStoreImmediate size false memop false u c rn rt) =
      wordBytes ((fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
        (9, c.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]).setWidth 64) from by
    simp only [encodeBytes, encodeInsn_loadStoreImmediateSignedAny size false memop u c rn rt
      hfits hne],
    show encodeBytes (.loadStoreImmediate size false memop false false c rn rt) =
      wordBytes ((fields [(2, size), (6, 56), (2, loadStoreOpc memop), (1, 0),
        (9, c.toNat % 512), (1, 0), (1, 0), (5, rn), (5, rt)]).setWidth 64) from by
      simp only [encodeBytes, encodeInsn_loadStoreImmediateSigned size false memop c rn rt hfits]]



/-- A state whose bytes hold an `addSubImmediate` is step-safe for it. -/
theorem stepSafe_memFirst (s : Arm8State) (d : BitVec 64 → Prop) (u : Bool) (b : W)
    (base : Nat) (himm : b.toNat < 4096) (hb32 : base < 32) (htemp32 : temp < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.addSubImmediate (!u) false b base temp)) s.mem d) : StepSafe d s :=
  stepSafe_of_encode s d (.addSubImmediate (!u) false b base temp)
    ((fields [(1, 1), (1, bit (!u)), (1, bit false), (7, 0b1000100),
      (12, b.toNat % 4096), (5, base), (5, temp)]).setWidth 64)
    hbytes (encodeInsn_addSubImmediate (!u) false b base temp himm)
    (decode_encode_addSubImmediate (!u) false b base temp himm hb32 htemp32)
    (by simp [arm8Touched])

/-- A load lowered to an `add` of the offset into the temporary register
followed by a small load. -/
theorem case_memLoadTwo (op : HolMemop) (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64)
    (ms : Arm8State) (size : Nat) (u : Bool) (b c : W)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (hsize : size < 4)
    (himm : b.toNat < 4096)
    (hfitsc : fitsSigned 9 c = true)
    (hnec : c ≠ scaledOff size c)
    (haddr : ∀ x : W, (if u then x + b else x - b) + c = x + off)
    (hast : arm8Enc (.inst (.mem op r (.addr base off))) =
      ([.addSubImmediate (!u) false b base temp,
        .loadStoreImmediate size false .load false u c temp r].flatMap encodeBytes))
    (hdom : ∀ k, k < 2 ^ size → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k))
    (h : asmStep arm8Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hokr, hokb⟩ := memRegOk_of_asm op r base off st.asmOk
  obtain ⟨hrlt, hrav, hrne⟩ := regOk_of_asm hokr
  obtain ⟨hblt, hbav, hbne⟩ := regOk_of_asm hokb
  have hr32 : r < 32 := by simpa [arm8Config] using hrlt
  have hb32 : base < 32 := by simpa [arm8Config] using hblt
  have htemp31 : temp ≠ 31 := by decide
  have htemp32 : temp < 32 := by decide
  have hbdom : base < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains base = false := by
    simpa [arm8Target_config] using (show base < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains base = false from ⟨hblt, hbav⟩)
  have hrdom : r < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains r = false := by
    simpa [arm8Target_config] using (show r < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains r = false from ⟨hrlt, hrav⟩)
  have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 8 := by
    rw [hast]
    simp [List.flatMap_cons, encodeBytes_length]
  have hupd : asmUpd (.inst (.mem op r (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 8 := by rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ i, s2.regs i =
      (if i = r then (readMemWord (s1.regs base + off) (2 ^ size) s1).1 else s1.regs i) := by
    intro i
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, st.be,
      Bool.false_eq_true, if_false]
  have hsplit : bytesInMemoryHOL ms.pc (encodeBytes (.addSubImmediate (!u) false b base temp))
        ms.mem s1.memDomain ∧
      bytesInMemoryHOL (ms.pc + 4)
        (encodeBytes (.loadStoreImmediate size false .load false u c temp r)) ms.mem
        s1.memDomain := by
    refine (bytesInMemory_two _ _ _ _ _).1 ?_
    rw [← hast]
    exact st.bytes
  obtain ⟨hb1, hb2⟩ := hsplit
  have hbv : ms.regs base = s1.regs base := st.reg base hbdom
  have hstep1 : arm8Next ms = writeReg { ms with pc := ms.pc + 4 } temp
      (if u then s1.regs base + b else s1.regs base - b) := by
    rw [arm8Next_addSubImmediate ms s1.memDomain (!u) false b base temp himm hb32 htemp32 hb1]
    have hrd : readReg { ms with pc := ms.pc + 4 } base = s1.regs base := by
      rw [readReg_pcUpdate, readReg, if_neg hbne, hbv]
    cases u with
    | true =>
        rw [show (!true : Bool) = false from rfl]
        rw [execInsn_addSubImmediate_add { ms with pc := ms.pc + 4 } b base temp]
        rw [if_pos rfl, hrd]
    | false =>
        rw [show (!false : Bool) = true from rfl]
        rw [execInsn_addSubImmediate_sub { ms with pc := ms.pc + 4 } b base temp]
        rw [if_neg (by decide : ¬((false : Bool) = true)), hrd]
  set t1 : Arm8State := writeReg { ms with pc := ms.pc + 4 } temp
    (if u then s1.regs base + b else s1.regs base - b) with ht1
  obtain ⟨ht1pc, ht1mem, ht1regs, ht1failed, ht1temp⟩ := execWriteFields htemp31 ht1
  have ht1addr : t1.regs temp + c = s1.regs base + off := by
    rw [ht1temp]
    exact haddr _
  have hbytes2C : bytesInMemoryHOL t1.pc
      (encodeBytes (.loadStoreImmediate size false .load false
        (decide (c = scaledOff size c)) c temp r)) t1.mem s1.memDomain := by
    have hp : decide (c = scaledOff size c) = false := by
      rw [decide_eq_false_iff_not]
      exact hnec
    rw [ht1pc, hp, ← encodeBytes_loadStoreImmediate_flag size .load u c temp r hfitsc hnec,
      funext ht1mem]
    exact hb2
  have hdec2 : decodeInsn ((encodeInsn (.loadStoreImmediate size false .load false
      (decide (c = scaledOff size c)) c temp r)).getD 0)
      = some (.loadStoreImmediate size false .load false
        (decide (c = scaledOff size c)) c temp r) :=
    decode_encode_loadStoreImmediate size false .load c temp r hsize rfl htemp32 hr32
      (Or.inr hfitsc)
  have htouch2 : ∀ a, a ∈ arm8Touched t1
      (.loadStoreImmediate size false .load false (decide (c = scaledOff size c)) c temp r) →
      s1.memDomain a := by
    intro a ha
    have ha' : a ∈ bytesAt (readReg t1 temp + c) (2 ^ size) := by
      simpa only [arm8Touched] using ha
    simp only [bytesAt, List.mem_map, List.mem_range] at ha'
    obtain ⟨j, hj, rfl⟩ := ha'
    simp only [readReg, if_neg htemp31]
    rw [ht1addr]
    exact hdom j hj
  have hnext2 : arm8Next t1 = execInsn { t1 with pc := t1.pc + 4 }
      (.loadStoreImmediate size false .load false (decide (c = scaledOff size c)) c temp r) :=
    arm8Next_memCanonical t1 s1.memDomain size .load c temp r hsize htemp32 hr32
      (Or.inr hfitsc) hbytes2C
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_memFirst ms s1.memDomain u b base himm hb32 htemp32 hb1
  have hsafe1 : StepSafe s1.memDomain t1 :=
    stepSafe_mem t1 s1.memDomain size .load c temp r hbytes2C hdec2 htouch2
  have hal4 : holAligned 2 (4 : BitVec 64) = true := aligned_of_mod 4 (by decide)
  have hal : holAligned 2 (ms.pc + 4) = true := by
    rw [(alignedAddSub 2 ms.pc 4 hal4).1, st.aligned]
  have hal2 : holAligned 2 (t1.pc + 4) = true := by
    rw [ht1pc]
    exact (alignedAddSub 2 (ms.pc + 4) 4 hal4).1.trans (by rw [hal])
  have hq1 : targetStateRel arm8Target s2 (arm8Next t1) := by
    rw [hnext2, execInsn_loadStoreImmediate_load]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk, writeReg, if_neg hrne]
      exact arm8StateOk_set _ hal2 (ht1failed.trans st.msFailed)
    · simp only [arm8Target_getPc, writeReg, if_neg hrne]
      show t1.pc + 4 = s2.pc
      rw [ht1pc, st.pc, hs2pc]
      bv_omega
    · intro x hx
      simp only [arm8Target_getByte, writeReg, if_neg hrne]
      rw [hs2mem x]
      exact (ht1mem x).trans (st.mem x (hs2dom ▸ hx))
    · intro i hi
      simp only [arm8Target_getReg, writeReg, if_neg hrne]
      by_cases hir : i = r
      · subst hir
        rw [if_pos rfl, hs2regs i, if_pos rfl]
        show readMemN t1 (2 ^ size) (readReg t1 temp + c) =
          (readMemWord (s1.regs base + off) (2 ^ size) s1).1
        have haddr' : readReg t1 temp + c = s1.regs base + off := by
          simp only [readReg, if_neg htemp31]
          exact ht1addr
        rw [haddr']
        refine (readValue_agree (s1.regs base + off) size hsize s1 t1 st.be hdom ?_).symm
        intro x hx
        rw [ht1mem x]
        exact st.mem x hx
      · rw [if_neg hir, hs2regs i, if_neg hir]
        have hne26 : i ≠ temp := by
          intro h26
          subst h26
          have hc : arm8Target.config.avoidRegs.contains temp = false := hi.2
          rw [show arm8Target.config.avoidRegs.contains temp = true from by decide] at hc
          exact Bool.noConfusion hc
        rw [ht1regs i hne26]
        exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  have hcode : allPcs (arm8Target.config.encode (.inst (.mem op r (.addr base off)))).length
      s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hposT : t1.pc ∈
      allPcs (arm8Target.config.encode (.inst (.mem op r (.addr base off)))).length
        s1.pc arm8Target.config.codeAlignment := by
    rw [ht1pc, st.pc, show arm8Target.config.codeAlignment = 2 from rfl,
      arm8Target_config, arm8Config_encode, hlen]
    simpa using mem_allPcs_step4 8 1 s1.pc (by decide)
  have hiter : arm8Next^[1] ms = t1 := by
    rw [Function.iterate_one]
    exact hstep1.trans ht1.symm
  have hq : targetStateRel arm8Target s2 (arm8Next^[1 + 1] ms) := by
    have hi : arm8Next^[1 + 1] ms = arm8Next t1 := by
      rw [Function.iterate_succ_apply', Function.iterate_one]
      exact congrArg arm8Next hiter
    rw [hi]
    exact hq1
  refine encoderCaseStep (.inst (.mem op r (.addr base off))) s1 s2 ms 1 hs2dom hcode ?_ ?_ hq
  · intro k hk
    rcases k with _ | k
    · simpa using hsafe0
    · have hk1 : k = 0 := by omega
      subst hk1
      rw [Function.iterate_succ_apply', Function.iterate_zero, id, hstep1]
      exact hsafe1
  · intro k h1 h2
    have hk1 : k = 1 := by omega
    subst hk1
    have h1eq : arm8Next^[1] ms = t1 := hiter
    rw [h1eq]
    refine ⟨?_, ?_, hposT⟩
    · refine arm8StateOk_set t1 ?_ ?_
      · rw [ht1pc]
        exact hal
      · exact ht1failed.trans st.msFailed
    · intro pc hpc
      exact ht1mem pc


/-- A store lowered to an `add` of the offset into the temporary register
followed by a small store. -/
theorem case_memStoreTwo (op : HolMemop) (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64)
    (ms : Arm8State) (size : Nat) (u : Bool) (b c : W)
    (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ size))
    (hsize : size < 4)
    (himm : b.toNat < 4096)
    (hfitsc : fitsSigned 9 c = true)
    (hnec : c ≠ scaledOff size c)
    (haddr : ∀ x : W, (if u then x + b else x - b) + c = x + off)
    (hast : arm8Enc (.inst (.mem op r (.addr base off))) =
      ([.addSubImmediate (!u) false b base temp,
        .loadStoreImmediate size false .store false u c temp r].flatMap encodeBytes))
    (h : asmStep arm8Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hokr, hokb⟩ := memRegOk_of_asm op r base off st.asmOk
  obtain ⟨hrlt, hrav, hrne⟩ := regOk_of_asm hokr
  obtain ⟨hblt, hbav, hbne⟩ := regOk_of_asm hokb
  have hr32 : r < 32 := by simpa [arm8Config] using hrlt
  have hb32 : base < 32 := by simpa [arm8Config] using hblt
  have htemp31 : temp ≠ 31 := by decide
  have htemp32 : temp < 32 := by decide
  have hbdom : base < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains base = false := by
    simpa [arm8Target_config] using (show base < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains base = false from ⟨hblt, hbav⟩)
  have hrdom : r < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains r = false := by
    simpa [arm8Target_config] using (show r < arm8Config.regCount ∧
      arm8Config.avoidRegs.contains r = false from ⟨hrlt, hrav⟩)
  have hrne26 : r ≠ temp := by
    intro h26
    have hc : arm8Target.config.avoidRegs.contains r = false := hrdom.2
    rw [h26, show arm8Target.config.avoidRegs.contains temp = true from by decide] at hc
    exact Bool.noConfusion hc
  have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 8 := by
    rw [hast]
    simp [List.flatMap_cons, encodeBytes_length]
  have hupd : asmUpd (.inst (.mem op r (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 8 := by rw [← hupd]; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs : ∀ i, s2.regs i = s1.regs i := by
    intro i
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2memWord : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) (2 ^ size) (s1.regs r) s1).mem x := by
    intro x
    rw [← hupd]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, st.be, Bool.false_eq_true, if_false]
  have hfail : s2.failed = false := boolOfNotTrue st.ok
  have hfailW : (writeMemWord (valueWidth := 64) (s1.regs base + off) (2 ^ size) (s1.regs r)
      s1).failed = false := by
    rw [← hupd] at hfail
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, st.be, Bool.false_eq_true, if_false] at hfail
    obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
    exact hf
  have hdomW := writeMemWord_domain (s1.regs base + off) (2 ^ size) (s1.regs r) s1 st.be
    (not_of_eq_false hfailW)
  have hsplit : bytesInMemoryHOL ms.pc (encodeBytes (.addSubImmediate (!u) false b base temp))
        ms.mem s1.memDomain ∧
      bytesInMemoryHOL (ms.pc + 4)
        (encodeBytes (.loadStoreImmediate size false .store false u c temp r)) ms.mem
        s1.memDomain := by
    refine (bytesInMemory_two _ _ _ _ _).1 ?_
    rw [← hast]
    exact st.bytes
  obtain ⟨hb1, hb2⟩ := hsplit
  have hbv : ms.regs base = s1.regs base := st.reg base hbdom
  have hstep1 : arm8Next ms = writeReg { ms with pc := ms.pc + 4 } temp
      (if u then s1.regs base + b else s1.regs base - b) := by
    rw [arm8Next_addSubImmediate ms s1.memDomain (!u) false b base temp himm hb32 htemp32 hb1]
    have hrd : readReg { ms with pc := ms.pc + 4 } base = s1.regs base := by
      rw [readReg_pcUpdate, readReg, if_neg hbne, hbv]
    cases u with
    | true =>
        rw [show (!true : Bool) = false from rfl]
        rw [execInsn_addSubImmediate_add { ms with pc := ms.pc + 4 } b base temp]
        rw [if_pos rfl, hrd]
    | false =>
        rw [show (!false : Bool) = true from rfl]
        rw [execInsn_addSubImmediate_sub { ms with pc := ms.pc + 4 } b base temp]
        rw [if_neg (by decide : ¬((false : Bool) = true)), hrd]
  set t1 : Arm8State := writeReg { ms with pc := ms.pc + 4 } temp
    (if u then s1.regs base + b else s1.regs base - b) with ht1
  obtain ⟨ht1pc, ht1mem, ht1regs, ht1failed, ht1temp⟩ := execWriteFields htemp31 ht1
  have ht1addr : t1.regs temp + c = s1.regs base + off := by
    rw [ht1temp]
    exact haddr _
  have hbytes2C : bytesInMemoryHOL t1.pc
      (encodeBytes (.loadStoreImmediate size false .store false
        (decide (c = scaledOff size c)) c temp r)) t1.mem s1.memDomain := by
    have hp : decide (c = scaledOff size c) = false := by
      rw [decide_eq_false_iff_not]
      exact hnec
    rw [ht1pc, hp, ← encodeBytes_loadStoreImmediate_flag size .store u c temp r hfitsc hnec,
      funext ht1mem]
    exact hb2
  have hdec2 : decodeInsn ((encodeInsn (.loadStoreImmediate size false .store false
      (decide (c = scaledOff size c)) c temp r)).getD 0)
      = some (.loadStoreImmediate size false .store false
        (decide (c = scaledOff size c)) c temp r) :=
    decode_encode_loadStoreImmediate size false .store c temp r hsize rfl htemp32 hr32
      (Or.inr hfitsc)
  have htouch2 : ∀ a, a ∈ arm8Touched t1
      (.loadStoreImmediate size false .store false (decide (c = scaledOff size c)) c temp r) →
      s1.memDomain a := by
    intro a ha
    have ha' : a ∈ bytesAt (readReg t1 temp + c) (2 ^ size) := by
      simpa only [arm8Touched] using ha
    simp only [bytesAt, List.mem_map, List.mem_range] at ha'
    obtain ⟨j, hj, rfl⟩ := ha'
    simp only [readReg, if_neg htemp31]
    rw [ht1addr]
    exact hdomW j hj
  have hnext2 : arm8Next t1 = execInsn { t1 with pc := t1.pc + 4 }
      (.loadStoreImmediate size false .store false (decide (c = scaledOff size c)) c temp r) :=
    arm8Next_memCanonical t1 s1.memDomain size .store c temp r hsize htemp32 hr32
      (Or.inr hfitsc) hbytes2C
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_memFirst ms s1.memDomain u b base himm hb32 htemp32 hb1
  have hsafe1 : StepSafe s1.memDomain t1 :=
    stepSafe_mem t1 s1.memDomain size .store c temp r hbytes2C hdec2 htouch2
  have hal4 : holAligned 2 (4 : BitVec 64) = true := aligned_of_mod 4 (by decide)
  have hal : holAligned 2 (ms.pc + 4) = true := by
    rw [(alignedAddSub 2 ms.pc 4 hal4).1, st.aligned]
  have hal2 : holAligned 2 (t1.pc + 4) = true := by
    rw [ht1pc]
    exact (alignedAddSub 2 (ms.pc + 4) 4 hal4).1.trans (by rw [hal])
  have hq1 : targetStateRel arm8Target s2 (arm8Next t1) := by
    rw [hnext2, execInsn_loadStoreImmediate_store]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk, arm8StateOk_writeMemN]
      exact arm8StateOk_set _ hal2 (ht1failed.trans st.msFailed)
    · simp only [arm8Target_getPc, writeMemN_pc]
      show t1.pc + 4 = s2.pc
      rw [ht1pc, st.pc, hs2pc]
      bv_omega
    · intro x hx
      simp only [arm8Target_getByte, readReg_pcUpdate]
      rw [hs2memWord x]
      have haddr2 : readReg t1 temp + c = s1.regs base + off := by
        simp only [readReg, if_neg htemp31]
        exact ht1addr
      have hval2 : readReg t1 r = s1.regs r := by
        simp only [readReg, if_neg hrne]
        rw [ht1regs r hrne26]
        exact st.reg r hrdom
      rw [haddr2, hval2]
      rw [writeMemWord_memSize s1 ms.mem size hsize (s1.regs base + off) (s1.regs r) x st.be
        (st.mem x (hs2dom ▸ hx)).symm]
      exact writeMemN_mem_of_mem (s := { t1 with pc := t1.pc + 4 }) (t := memState ms.mem)
        rfl (2 ^ size) (s1.regs base + off) (s1.regs r) x
    · intro i hi
      simp only [arm8Target_getReg, writeMemN_regs]
      have hne26 : i ≠ temp := by
        intro h26
        subst h26
        have hc : arm8Target.config.avoidRegs.contains temp = false := hi.2
        rw [show arm8Target.config.avoidRegs.contains temp = true from by decide] at hc
        exact Bool.noConfusion hc
      rw [ht1regs i hne26, hs2regs i]
      exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  have hcode : allPcs (arm8Target.config.encode (.inst (.mem op r (.addr base off)))).length
      s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hposT : t1.pc ∈
      allPcs (arm8Target.config.encode (.inst (.mem op r (.addr base off)))).length
        s1.pc arm8Target.config.codeAlignment := by
    rw [ht1pc, st.pc, show arm8Target.config.codeAlignment = 2 from rfl,
      arm8Target_config, arm8Config_encode, hlen]
    simpa using mem_allPcs_step4 8 1 s1.pc (by decide)
  have hiter : arm8Next^[1] ms = t1 := by
    rw [Function.iterate_one]
    exact hstep1.trans ht1.symm
  have hq : targetStateRel arm8Target s2 (arm8Next^[1 + 1] ms) := by
    have hi : arm8Next^[1 + 1] ms = arm8Next t1 := by
      rw [Function.iterate_succ_apply', Function.iterate_one]
      exact congrArg arm8Next hiter
    rw [hi]
    exact hq1
  refine encoderCaseStep (.inst (.mem op r (.addr base off))) s1 s2 ms 1 hs2dom hcode ?_ ?_ hq
  · intro k hk
    rcases k with _ | k
    · simpa using hsafe0
    · have hk1 : k = 0 := by omega
      subst hk1
      rw [Function.iterate_succ_apply', Function.iterate_zero, id, hstep1]
      exact hsafe1
  · intro k h1 h2
    have hk1 : k = 1 := by omega
    subst hk1
    have h1eq : arm8Next^[1] ms = t1 := hiter
    rw [h1eq]
    refine ⟨?_, ?_, hposT⟩
    · refine arm8StateOk_set t1 ?_ ?_
      · rw [ht1pc]
        exact hal
      · exact ht1failed.trans st.msFailed
    · intro pc hpc
      exact ht1mem pc

end Flapjack.Compiler.Encoders.Arm8
