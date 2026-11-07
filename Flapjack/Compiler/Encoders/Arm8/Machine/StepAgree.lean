import Mathlib.Tactic.IntervalCases
import Flapjack.Compiler.Encoders.Arm8.Machine.Agree

/-!
# Step agreement and framing for the closed ARMv8 model

`Arm8Agree d s t` (`Machine/Agree.lean`) says two states have the same PC,
registers, flags and failure flag, and the same bytes on `d`.  This module
proves that one `arm8Next` step preserves that relation as long as the step
stays inside `d`, and that a step leaves every byte outside `d` alone.  These
are the step-agreement and framing facts an `encoder_correct` proof for the
ARM8 target needs; they are the ARM8 analogue of the MIPS32
`exec_agree`/`fetchExec_agree`/`next_agree` family.

## The memory a step touches

`arm8Touched s i` lists the byte addresses one instruction reads or writes: a
load or store immediate touches the `2 ^ size` bytes starting at
`readReg s rn + offset`, and every other instruction touches nothing.  This is
a deliberate over-approximation of `readMemN`/`writeMemN`, which use at most
eight bytes: `writtenBytes (2 ^ size) ≤ 2 ^ size`, so every byte the accessors
actually read or write is in `arm8Touched`.  Keeping
the over-approximation makes `arm8Touched` independent of the accessor
internals, and all lemmas below are monotone in the touched set.

`StepSafe d s` is what one `arm8Next` step needs from `d`: `FetchSafe d s` (the
four bytes `pc, pc+1, pc+2, pc+3` of the fetched instruction word) and, for the
instruction those bytes decode to, the bytes in `arm8Touched`.  A failed decode
touches no memory (it only sets `failed`), so this predicate covers the `none`
branch of `arm8Next` too.

## Main results

* `readMemN_congr`/`writeMemN_congr`: the byte-wise memory accessors respect
  agreement on the bytes they touch.  `readMemN` congruence needs agreement on
  `writtenBytes size` bytes, which is exactly the set of bytes it reads;
* `execInsn_agree`/`execInsn_frame`: one instruction preserves agreement on `d`
  and changes no byte outside `d`, provided its accesses lie in `d`;
* `fetchWord_congr`: agreeing states that fetch inside `d` fetch the same word;
* `arm8Next_agree`/`arm8Next_frame`: the same for a whole machine step, with
  `StepSafe` supplying the fetch and access facts.
-/

namespace Flapjack.Compiler.Encoders.Arm8

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

/-- The byte addresses one closed ARM8 instruction reads or writes in state `s`:
the `2 ^ size` bytes at `readReg s rn + offset` for a load or store immediate,
and nothing for every other instruction. -/
def arm8Touched (s : Arm8State) : Insn → List (BitVec 64)
  | .loadStoreImmediate size _ _ _ _ offset rn _ => bytesAt (readReg s rn + offset) (2 ^ size)
  | _ => []

/-- The domain facts `arm8Touched` provides for a load or store, one byte at a
time. -/
theorem arm8Touched_acc {d : BitVec 64 → Prop} {s : Arm8State} (size : Nat) (offset : BitVec 64)
    (rn : Nat) {regsizeWord : Bool} {memop : MemOp} {signed unsignedOffset : Bool} {rt : Nat}
    (hacc : ∀ a ∈ arm8Touched s
      (.loadStoreImmediate size regsizeWord memop signed unsignedOffset offset rn rt), d a) :
    ∀ j, j < 2 ^ size → d (readReg s rn + offset + BitVec.ofNat 64 j) :=
  fun j hj => hacc (readReg s rn + offset + BitVec.ofNat 64 j) (mem_bytesAt hj)

/-! ## Register and flag reads -/

/-- Agreeing states evaluate condition codes the same way. -/
theorem conditionHolds_congr {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (cond : Nat) : conditionHolds s cond = conditionHolds t cond := by
  simp only [conditionHolds, h.n, h.z, h.c, h.v]

/-- `writeReg` leaves the memory alone. -/
theorem writeReg_mem (s : Arm8State) (r : Nat) (v : BitVec 64) : (writeReg s r v).mem = s.mem := by
  unfold writeReg
  split <;> rfl

/-- `writeFlags` leaves the memory alone. -/
theorem writeFlags_mem (s : Arm8State) (f : Arm8Flags) : (writeFlags s f).mem = s.mem := rfl

/-! ## Byte chains

`writeMemN` updates the memory by a chain of `if a = address + n then byte n else …`
tests.  `byteChain` is that chain as a list of `(address, byte)` pairs, which
makes the proofs below independent of how many bytes an access writes.
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

/-- Number of bytes `writeMemN size` stores: `size` bytes below 5 and eight bytes
from 5 on. -/
def writtenBytes (size : Nat) : Nat := if size = 0 then 0 else if size ≤ 4 then size else 8

/-- A load or store of `size` touches `2 ^ size` bytes, and that is at least the
number of bytes `writeMemN (2 ^ size)` stores. -/
theorem writtenBytes_two_pow_le (size : Nat) : writtenBytes (2 ^ size) ≤ 2 ^ size := by
  by_cases h3 : size ≤ 3
  · interval_cases size <;> decide
  · have h4 : 4 ≤ size := by omega
    have hpow : 16 ≤ 2 ^ size := by
      have hp := Nat.pow_le_pow_right (n := 2) (by decide) h4
      simpa using hp
    have h0 : (2 : Nat) ^ size ≠ 0 := by omega
    have h4' : ¬ (2 : Nat) ^ size ≤ 4 := by omega
    simp only [writtenBytes, ite_eq_right h0, ite_eq_right h4']
    omega

/-- The `(address, byte)` pairs `writeMemN` stores, in write order.  The `i = 0`
case is written as the bare `address` so that the chain matches `writeMemN`
definitionally. -/
def writeChain (size : Nat) (address v : BitVec 64) : List (BitVec 64 × BitVec 8) :=
  (List.range (writtenBytes size)).map
    fun i => (if i = 0 then address else address + BitVec.ofNat 64 i, (v >>> (8 * i)).setWidth 8)

/-- Every byte a write chain stores is `address` or `address + i` for an `i`
below the number of stored bytes. -/
theorem mem_writeChain {size : Nat} {address v e : BitVec 64} {b : BitVec 8}
    (h : (e, b) ∈ writeChain size address v) :
    ∃ i, i < writtenBytes size ∧
      e = (if i = 0 then address else address + BitVec.ofNat 64 i) := by
  simp only [writeChain, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, hi, (congrArg Prod.fst he).symm⟩

/-- Every byte a write chain stores lies inside the `2 ^ size` bytes touched by a
load or store of `size`. -/
theorem mem_writeChain_two_pow {size : Nat} {address v e : BitVec 64} {b : BitVec 8}
    (h : (e, b) ∈ writeChain (2 ^ size) address v) :
    ∃ i, i < 2 ^ size ∧ e = (if i = 0 then address else address + BitVec.ofNat 64 i) := by
  obtain ⟨i, hi, he⟩ := mem_writeChain h
  exact ⟨i, Nat.lt_of_lt_of_le hi (writtenBytes_two_pow_le size), he⟩

/-- The `i`-th chain address is `address` or `address + i`. -/
theorem ne_chainAddr {address a : BitVec 64} {i : Nat} (h0 : a ≠ address)
    (hi : a ≠ address + BitVec.ofNat 64 i) :
    a ≠ (if i = 0 then address else address + BitVec.ofNat 64 i) := by
  by_cases hz : i = 0
  · simpa only [hz, ite_true] using h0
  · simpa only [hz, ite_false] using hi

/-- The memory after `writeMemN` is the byte chain of the stored pairs. -/
theorem writeMemN_mem (s : Arm8State) (size : Nat) (address v : BitVec 64) (a : BitVec 64) :
    (writeMemN s size address v).mem a = byteChain (s.mem a) (writeChain size address v) a := by
  by_cases h0 : size = 0
  · subst h0
    rfl
  · by_cases h1 : size = 1
    · subst h1
      rfl
    · by_cases h2 : size = 2
      · subst h2
        rfl
      · by_cases h3 : size = 3
        · subst h3
          rfl
        · by_cases h4 : size = 4
          · subst h4
            rfl
          · rw [writeMemN.eq_6 s size address v h0 h1 h2 h3 h4]
            simp only [writeChain, writtenBytes, ite_eq_right h0, ite_eq_right (by omega : ¬ size ≤ 4)]
            rfl

/-! ## Congruence for the byte-wise memory accessors -/

/-- Two states agreeing on `d` read the same `size`-byte little-endian value. -/
theorem readMemN_congr {s t : Arm8State} {d : BitVec 64 → Prop}
    (hmem : ∀ a, d a → s.mem a = t.mem a) (size : Nat) (address : BitVec 64)
    (hacc : ∀ j, j < writtenBytes size → d (address + BitVec.ofNat 64 j)) :
    readMemN s size address = readMemN t size address := by
  have hb : ∀ j, j < writtenBytes size → s.mem (address + BitVec.ofNat 64 j) =
      t.mem (address + BitVec.ofNat 64 j) := fun j hj => hmem _ (hacc j hj)
  by_cases h0 : size = 0
  · subst h0
    simp only [readMemN]
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
            have e0 : s.mem address = t.mem address := by
              simpa using hb 0 (by omega)
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
theorem writeMemN_congr {s t : Arm8State} {d : BitVec 64 → Prop}
    (hmem : ∀ a, d a → s.mem a = t.mem a) (size : Nat) (address v : BitVec 64) :
    ∀ a, d a → (writeMemN s size address v).mem a = (writeMemN t size address v).mem a := by
  intro a ha
  rw [writeMemN_mem, writeMemN_mem]
  exact byteChain_congr (hmem a ha) _ a

/-! ## Executing one instruction -/

/-- `bitfieldMove` leaves the memory alone. -/
theorem bitfieldMove_mem (s : Arm8State) (inzero extend : Bool) (immr imms rn rd : Nat) :
    (bitfieldMove s inzero extend immr imms rn rd).mem = s.mem := by
  cases hdm : decodeBitMasks 1 imms immr false with
  | none => simp only [bitfieldMove, hdm]
  | some p =>
      obtain ⟨wmask, tmask⟩ := p
      simp only [bitfieldMove, hdm, writeReg_mem]

/-- Reconstituting `t` from `s` and `t`'s memory: the non-memory fields of `t`
are `s`'s.  This is the form in which the instruction proofs compare `s` with
`t`. -/
theorem Arm8Agree.eq_mem {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t) :
    t = { s with mem := t.mem, memDomain := t.memDomain } := by
  obtain ⟨hpc, hregs, hn, hz, hc, hv, hf, _⟩ := h
  cases s with
  | mk sregs spc sn sz sc sv smem sdom sfailed =>
    cases t with
    | mk tregs tpc tn tz tc tv tmem tdom tfailed =>
      dsimp only at hpc hregs hn hz hc hv hf ⊢
      simp only [hpc, hregs, hn, hz, hc, hv, hf]

/-- `s` agrees with the state obtained by giving it `t`'s memory. -/
theorem Arm8Agree.withMem {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t) :
    Arm8Agree d s { s with mem := t.mem, memDomain := t.memDomain } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩

/-- `writeMemN` only replaces the memory of a state. -/
theorem writeMemN_state (s : Arm8State) (size : Nat) (address v : BitVec 64) :
    writeMemN s size address v = { s with mem := (writeMemN s size address v).mem } := by
  by_cases h0 : size = 0
  · subst h0
    rfl
  · by_cases h1 : size = 1
    · subst h1
      rfl
    · by_cases h2 : size = 2
      · subst h2
        rfl
      · by_cases h3 : size = 3
        · subst h3
          rfl
        · by_cases h4 : size = 4
          · subst h4
            rfl
          · rw [writeMemN.eq_6 s size address v h0 h1 h2 h3 h4]

/-- Agreement from the individual field equalities; only the memory conjunct is
restricted to `d`. -/
theorem agree_of_mem {d : BitVec 64 → Prop} {x y : Arm8State}
    (hx : x.pc = y.pc) (hr : x.regs = y.regs) (hn : x.n = y.n) (hz : x.z = y.z) (hc : x.c = y.c)
    (hv : x.v = y.v) (hf : x.failed = y.failed) (hm : ∀ a, d a → x.mem a = y.mem a) :
    Arm8Agree d x y :=
  ⟨hx, hr, hn, hz, hc, hv, hf, hm⟩

/-- `execInsn` respects `Arm8Agree` on `d` whenever the instruction's accesses
lie in `d`. -/
theorem execInsn_agree {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t) (i : Insn)
    (hacc : ∀ a ∈ arm8Touched s i, d a) : Arm8Agree d (execInsn s i) (execInsn t i) := by
  cases i with
  | noOp => exact h
  | moveWide op hw imm16 rd =>
      rw [h.eq_mem]
      cases op <;>
        (simp only [execInsn, writeReg]
         split_ifs <;>
         exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩)
  | addSubImmediate sub setFlags imm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | logicalImmediate op setFlags imm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | logicalShiftedRegister op invert setFlags shift imm rm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | addSubShiftedRegister sub setFlags shift rm imm6 rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | addSubCarry sub setFlags rm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | bitfieldMove inzero extend immr imms rn rd =>
      rw [h.eq_mem]
      cases hdm : decodeBitMasks 1 imms immr false with
      | none =>
          simp only [execInsn, bitfieldMove, hdm]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
      | some p =>
          obtain ⟨wmask, tmask⟩ := p
          simp only [execInsn, bitfieldMove, hdm, writeReg]
          split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | extractRegister imms rm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | shift st rm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | division unsigned rm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | multiplyHigh signed rm rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | multiplyAddSub sub rm ra rn rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | conditionalCompareImmediate opc imm cd nzcv rn =>
      rw [h.eq_mem]
      simp only [execInsn, writeFlags]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | conditionalSelect op o2 cd rm rn rd =>
      -- Rewrite `t` into `s` with `t`'s memory, then read the condition off `s`
      -- so that both sides of the `if` are syntactically the same test.
      rw [h.eq_mem]
      simp only [execInsn]
      rw [← conditionHolds_congr h.withMem cd]
      simp only [writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | loadStoreImmediate size regsizeWord memop signed unsignedOffset offset rn rt =>
      have hacc' := arm8Touched_acc size offset rn hacc
      rw [h.eq_mem]
      have hreg : readReg { s with mem := t.mem, memDomain := t.memDomain } rn = readReg s rn :=
        rfl
      have hval : readReg { s with mem := t.mem, memDomain := t.memDomain } rt = readReg s rt :=
        rfl
      cases memop with
      | load =>
          simp only [execInsn, hreg]
          have hread : readMemN s (2 ^ size) (readReg s rn + offset) =
              readMemN { s with mem := t.mem, memDomain := t.memDomain } (2 ^ size)
                (readReg s rn + offset) :=
            readMemN_congr h.mem (2 ^ size) (readReg s rn + offset)
              (fun j hj => hacc' j (Nat.lt_of_lt_of_le hj (writtenBytes_two_pow_le size)))
          rw [hread]
          simp only [writeReg]
          split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
      | store =>
          simp only [execInsn, hreg, hval]
          rw [writeMemN_state s, writeMemN_state { s with mem := t.mem, memDomain := t.memDomain }]
          refine agree_of_mem rfl rfl rfl rfl rfl rfl rfl ?_
          exact writeMemN_congr (t := { s with mem := t.mem, memDomain := t.memDomain }) h.mem
            (2 ^ size) (readReg s rn + offset) (readReg s rt)
  | branchImmediate imm call =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | branchConditional imm cond =>
      -- As for `conditionalSelect`: one syntactic test lets `split_ifs` split
      -- both branches of the `if` at once.
      rw [h.eq_mem]
      simp only [execInsn]
      rw [← conditionHolds_congr h.withMem cond]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | branchRegister rn kind =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩
  | address page imm rd =>
      rw [h.eq_mem]
      simp only [execInsn, writeReg]
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.mem⟩

/-- An instruction whose accesses lie in `d` changes no byte outside `d`. -/
theorem execInsn_frame {d : BitVec 64 → Prop} {s : Arm8State} {i : Insn} {y : BitVec 64}
    (hacc : ∀ a ∈ arm8Touched s i, d a) (hy : ¬ d y) : (execInsn s i).mem y = s.mem y := by
  cases i with
  | noOp => rfl
  | moveWide op hw imm16 rd =>
      cases op <;> (simp only [execInsn, writeReg]; split_ifs <;> rfl)
  | addSubImmediate sub setFlags imm rn rd =>
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> rfl
  | logicalImmediate op setFlags imm rn rd =>
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> rfl
  | logicalShiftedRegister op invert setFlags shift imm rm rn rd =>
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> rfl
  | addSubShiftedRegister sub setFlags shift rm imm6 rn rd =>
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> rfl
  | addSubCarry sub setFlags rm rn rd =>
      simp only [execInsn, writeReg, writeFlags]
      split_ifs <;> rfl
  | bitfieldMove inzero extend immr imms rn rd =>
      simp only [execInsn]
      rw [bitfieldMove_mem]
  | extractRegister imms rm rn rd =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | shift st rm rn rd =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | division unsigned rm rn rd =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | multiplyHigh signed rm rn rd =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | multiplyAddSub sub rm ra rn rd =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | conditionalCompareImmediate opc imm cd nzcv rn =>
      simp only [execInsn]
      rw [writeFlags_mem]
  | conditionalSelect op o2 cd rm rn rd =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | loadStoreImmediate size regsizeWord memop signed unsignedOffset offset rn rt =>
      have hacc' := arm8Touched_acc size offset rn hacc
      cases memop with
      | load =>
          simp only [execInsn, writeReg]
          split_ifs <;> rfl
      | store =>
          simp only [execInsn]
          rw [writeMemN_mem]
          refine byteChain_of_ne (fun e b hm => ?_)
          obtain ⟨k, hk, he⟩ := mem_writeChain_two_pow hm
          have hA : d (readReg s rn + offset) := by
            simpa using hacc' 0 (Nat.two_pow_pos size)
          have hd : d (readReg s rn + offset + BitVec.ofNat 64 k) := hacc' k hk
          have hne : y ≠ readReg s rn + offset := fun hc => hy (hc.symm ▸ hA)
          have hne' : y ≠ readReg s rn + offset + BitVec.ofNat 64 k := fun hc => hy (hc.symm ▸ hd)
          exact fun hye => ne_chainAddr hne hne' (he ▸ hye)
  | branchImmediate imm call =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | branchConditional imm cond =>
      simp only [execInsn]
      split_ifs <;> rfl
  | branchRegister rn kind =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl
  | address page imm rd =>
      simp only [execInsn, writeReg]
      split_ifs <;> rfl

/-! ## Fetching and the machine step -/

/-- The four bytes of the instruction word fetched at `pc`. -/
def arm8FetchBytes (s : Arm8State) : List (BitVec 64) :=
  [s.pc, s.pc + 1, s.pc + 2, s.pc + 3]

/-- The four bytes of the fetched instruction word lie in `d`. -/
def FetchSafe (d : BitVec 64 → Prop) (s : Arm8State) : Prop :=
  ∀ x ∈ arm8FetchBytes s, d x

/-- `d` covers every byte one `arm8Next` step from `s` fetches or accesses: the
four bytes of the fetched word and, for whichever instruction they decode to,
the bytes that instruction touches.  A failed decode only sets `failed`, so it
needs nothing beyond `FetchSafe`. -/
def StepSafe (d : BitVec 64 → Prop) (s : Arm8State) : Prop :=
  FetchSafe d s ∧ ∀ i, decodeInsn32 (fetchWord s) = some i → ∀ x ∈ arm8Touched s i, d x

/-- Two states that agree on `d` and fetch inside `d` fetch the same word. -/
theorem fetchWord_congr {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (hs : FetchSafe d s) : fetchWord s = fetchWord t := by
  have h0 : d s.pc := hs _ (by simp [arm8FetchBytes])
  have h1 : d (s.pc + 1) := hs _ (by simp [arm8FetchBytes])
  have h2 : d (s.pc + 2) := hs _ (by simp [arm8FetchBytes])
  have h3 : d (s.pc + 3) := hs _ (by simp [arm8FetchBytes])
  simp only [fetchWord, ← h.pc, h.mem _ h0, h.mem _ h1, h.mem _ h2, h.mem _ h3]

/-- Agreement is preserved by advancing the program counter. -/
theorem Arm8Agree.pcAdd {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (k : BitVec 64) : Arm8Agree d { s with pc := s.pc + k } { t with pc := t.pc + k } := by
  obtain ⟨hpc, hregs, hn, hz, hc, hv, hf, hm⟩ := h
  exact ⟨by simp only [hpc], by simp only [hregs], by simp only [hn], by simp only [hz],
    by simp only [hc], by simp only [hv], by simp only [hf], hm⟩

/-- One `arm8Next` step preserves agreement on `d` from a state that steps
inside `d`.  The failed-decode branch only sets `failed` in both states. -/
theorem arm8Next_agree {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (hs : StepSafe d s) : Arm8Agree d (arm8Next s) (arm8Next t) := by
  have hw : fetchWord s = fetchWord t := fetchWord_congr h hs.1
  simp only [arm8Next]
  rw [hw]
  cases hd : decodeInsn32 (fetchWord t) with
  | none => exact ⟨h.pc, h.regs, h.n, h.z, h.c, h.v, rfl, h.mem⟩
  | some i => exact execInsn_agree (h.pcAdd 4) i (hs.2 i (by rw [hw]; exact hd))

/-- One `arm8Next` step from a state that steps inside `d` leaves every byte
outside `d` alone. -/
theorem arm8Next_frame {d : BitVec 64 → Prop} (s : Arm8State) (hs : StepSafe d s)
    (y : BitVec 64) (hy : ¬ d y) : (arm8Next s).mem y = s.mem y := by
  simp only [arm8Next]
  cases hd : decodeInsn32 (fetchWord s) with
  | none => rfl
  | some i => exact execInsn_frame (hs.2 i hd) hy

end Flapjack.Compiler.Encoders.Arm8

