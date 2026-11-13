module

public import Mathlib.Tactic
public import Flapjack.Compiler.Encoders.AsmSem.Memory

@[expose] public section

/-!
# The little-endian byte bridge shared by the X64 and ARM8 memory cases

Both `encoder_correct` memory-case proofs identify the source's `readMemWord`
with the machine's `readMemN` byte reads.  `readBytes` is the little-endian word
of the bytes at `a`, `a + 1`, ..., and the lemmas below relate it to
`readMemWord` and spell out its OR-of-shifts form at the byte counts the two
lowerings use.  This is Flapjack infrastructure shared by the x86-64 and ARMv8
encoders; there is no separately named HOL original.
-/

namespace Flapjack.Compiler.Encoders

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- The little-endian value `readMemWord` assembles out of the bytes at `a`,
`a + 1`, `a + 2`, ... -/
def readBytes (mem : BitVec 64 → BitVec 8) (a : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => (readBytes mem (a + 1) n) <<< (8 : Nat) ||| (mem a).setWidth 64

/-- The numeral `0` of the word carrier is the empty word, so that the `BitVec`
zero lemmas apply to the base case of `readBytes`. -/
theorem zero64 : ((0 : BitVec 64) = 0#64) := rfl

/-- The value `readMemWord` assembles is the little-endian word of the bytes it
reads (`be = false`). -/
theorem readMemWord_fst (a : BitVec 64) (n : Nat) (s : AsmState 64) (hbe : s.be = false) :
    (readMemWord (resultWidth := 64) a n s).1 = readBytes s.mem a n := by
  induction n generalizing a s with
  | zero => simp [readMemWord, readBytes]
  | succ n ih =>
      rw [readMemWord_succ, hbe]
      simp only [Bool.false_eq_true, ite_false]
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

/-- `readMemWord` preserves the memory domain. -/
theorem readMemWord_memDomain (a : BitVec 64) (n : Nat) (s : AsmState 64) :
    (readMemWord (resultWidth := 64) a n s).2.memDomain = s.memDomain := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
      rw [readMemWord_succ]
      simp only [assertState_memDomain]
      exact ih _ _

/-- `writeMemWord` preserves the memory domain. -/
theorem writeMemWord_memDomain (a : BitVec 64) (n : Nat) (w : BitVec 64) (s : AsmState 64) :
    (writeMemWord (valueWidth := 64) a n w s).memDomain = s.memDomain := by
  induction n generalizing a w s with
  | zero => rfl
  | succ n ih =>
      rw [writeMemWord_succ]
      simp only [assertState_memDomain, updMem_memDomain]
      exact ih _ _ _

/-- A `Bool` equal to `false` is not `true`. -/
theorem not_of_eq_false {b : Bool} (h : b = false) : ¬b := by
  rw [h]; intro h'; exact Bool.noConfusion h'

/-- A successful `readMemWord` reads all of its bytes out of the domain. This is
the domain side of the source alignment guard: `memLoad` fails unless the read
succeeds, so the bytes the target reads are the bytes the source read. Shared by
the x86-64 and ARMv8 memory cases. -/
theorem readMemWord_domain (a : BitVec 64) (n : Nat) (s : AsmState 64) (hbe : s.be = false)
    (h : (readMemWord (resultWidth := 64) a n s).2.failed = false) :
    ∀ k, k < n → s.memDomain (a + BitVec.ofNat 64 k) := by
  induction n generalizing a s with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk
      classical
      rw [readMemWord_succ] at h
      simp only [hbe, Bool.false_eq_true, ite_false] at h
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

/-- A store writes only bytes the source state has in its memory domain.
Shared by the x86-64 and ARMv8 memory cases. -/
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
        rw [ite_eq_right (by decide : ¬((false : Bool) = true))]
      rw [hif] at h
      set s1 : AsmState 64 :=
        writeMemWord (valueWidth := 64) (a + 1) n (v >>> (8 : Nat)) s with hs1
      obtain ⟨hdom, hfl⟩ := not_failed_assertState h
      have hfl' : (writeMemWord (valueWidth := 64) (a + 1) n (v >>> (8 : Nat)) s).failed =
          false := by
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

end Flapjack.Compiler.Encoders
