import Flapjack.Compiler.Encoders.AsmSem.Memory

/-!
# Exact asmProps memory-word invariants

Counterpart of `cakeml/compiler/encoders/asm/asmPropsScript.sml`'s
`SND_read_mem_word_consts` (`:339-347`), `write_mem_word_consts` (`:350-357`),
`read_mem_word_IMP_mem_eq` (`:424-...`), `write_mem_word_mem_domain`
(`:433-...`) and `write_mem_word_mem_eq` (`:440-...`).

`'a word` is rendered as `BitVec width` with the reviewed `[NeZero width]`
discharge; `word8` is `BitVec 8`; `('a word) set` domains are the predicate
rendering `BitVec width → Prop`.  Matching the original HOL types, the
address/state word dimension and the read-result (resp. write-value) word
dimension are independent type variables.  All original quantifiers, guards and
conclusions are preserved; no success/domain/width premise is added.
-/

namespace Flapjack
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem
open Classical

set_option maxHeartbeats 1000000 in
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "SND_read_mem_word_consts" (words_as_type_indexed_bitvec)]
theorem sndReadMemWordConsts {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth]
    (n : Nat) (a : BitVec width) (s : AsmState width) :
    (readMemWord (resultWidth := resultWidth) a n s).2.be = s.be ∧
      (readMemWord (resultWidth := resultWidth) a n s).2.lr = s.lr ∧
      (readMemWord (resultWidth := resultWidth) a n s).2.align = s.align ∧
      (readMemWord (resultWidth := resultWidth) a n s).2.memDomain = s.memDomain := by
  induction n generalizing a s with
  | zero => simp [readMemWord]
  | succ n ih =>
      rw [readMemWord_succ]
      generalize hr : readMemWord (resultWidth := resultWidth) (if s.be then a - 1 else a + 1) n s = r
      obtain ⟨w0, s0⟩ := r
      have ih1 := ih (if s.be then a - 1 else a + 1) s
      rw [hr] at ih1
      simpa using ih1

set_option maxHeartbeats 1000000 in
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "write_mem_word_consts" (words_as_type_indexed_bitvec)]
theorem writeMemWordConsts {width : Nat} [NeZero width] {valueWidth : Nat} [NeZero valueWidth]
    (n : Nat) (a : BitVec width) (w : BitVec valueWidth) (s : AsmState width) :
    (writeMemWord (valueWidth := valueWidth) a n w s).be = s.be ∧
      (writeMemWord (valueWidth := valueWidth) a n w s).lr = s.lr ∧
      (writeMemWord (valueWidth := valueWidth) a n w s).align = s.align ∧
      (writeMemWord (valueWidth := valueWidth) a n w s).memDomain = s.memDomain := by
  induction n generalizing a w s with
  | zero => simp [writeMemWord]
  | succ n ih =>
      rw [writeMemWord_succ]
      generalize hr : writeMemWord (valueWidth := valueWidth) (if s.be then a - 1 else a + 1) n (w >>> 8) s = s0
      have ih1 := ih (if s.be then a - 1 else a + 1) (w >>> 8) s
      rw [hr] at ih1
      simpa using ih1

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "read_mem_word_IMP_mem_eq" (words_as_type_indexed_bitvec)]
theorem readMemWord_IMP_mem_eq {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth]
    (a : BitVec width) (k : Nat) (s : AsmState width)
    (w : BitVec resultWidth) (s' : AsmState width)
    (h : readMemWord (resultWidth := resultWidth) a k s = (w, s')) : s'.mem = s.mem := by
  have hd := readMemWord_mem_eq_direct (resultWidth := resultWidth) a k s
  rw [h] at hd
  simpa using hd

set_option maxHeartbeats 1000000 in
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "write_mem_word_mem_domain" (words_as_type_indexed_bitvec)]
theorem writeMemWord_mem_domain {width : Nat} [NeZero width] {valueWidth : Nat} [NeZero valueWidth]
    (k : Nat) (b : BitVec width) (a : BitVec valueWidth) (s : AsmState width) :
    (writeMemWord (valueWidth := valueWidth) b k a s).memDomain = s.memDomain := by
  induction k generalizing b a s with
  | zero => simp [writeMemWord]
  | succ n ih =>
      rw [writeMemWord_succ]
      generalize hr : writeMemWord (valueWidth := valueWidth) (if s.be then b - 1 else b + 1) n (a >>> 8) s = s0
      have ih1 := ih (if s.be then b - 1 else b + 1) (a >>> 8) s
      rw [hr] at ih1
      simpa using ih1

set_option maxHeartbeats 2000000 in
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "write_mem_word_mem_eq" (words_as_type_indexed_bitvec)]
theorem writeMemWord_mem_eq {width : Nat} [NeZero width] {valueWidth : Nat} [NeZero valueWidth]
    (k : Nat) (b : BitVec width) (a : BitVec valueWidth) (s : AsmState width) (x : BitVec width)
    (h : ¬ (writeMemWord (valueWidth := valueWidth) b k a s).failed) (hx : ¬ s.memDomain x) :
    (writeMemWord (valueWidth := valueWidth) b k a s).mem x = s.mem x := by
  induction k generalizing b a s with
  | zero => simp [writeMemWord]
  | succ n ih =>
      generalize hr : writeMemWord (valueWidth := valueWidth) (if s.be then b - 1 else b + 1) n (a >>> 8) s = s0
      rw [writeMemWord_succ, hr] at h ⊢
      simp only [assertState_mem]
      obtain ⟨hc, hf⟩ := not_failed_assertState h
      have hdom : s0.memDomain = s.memDomain := by
        rw [← hr]
        simpa using writeMemWord_mem_domain (valueWidth := valueWidth) n (if s.be then b - 1 else b + 1) (a >>> 8) s
      have hcs : decide (s.memDomain b) = true := by rw [← hdom]; exact hc
      have hb : s.memDomain b := of_decide_eq_true hcs
      rw [updMem_mem]
      by_cases hxb : x = b
      · subst hxb; exact absurd hb hx
      · rw [if_neg hxb]
        have ih1 := ih (if s.be then b - 1 else b + 1) (a >>> 8) s (by rw [hr]; simpa using hf) hx
        rw [hr] at ih1
        exact ih1

end Flapjack
