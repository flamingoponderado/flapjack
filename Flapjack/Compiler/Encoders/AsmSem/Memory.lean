import Flapjack.Compiler.Encoders.AsmSem.Arithmetic

/-!
# Exact asmSem memory accessors

Counterpart of `cakeml/compiler/encoders/asm/asmSemScript.sml`'s address
computation (`addr_def`, `:178-180`) and the recursive little/big-endian
word memory readers and writers (`read_mem_word_def` `:182-189`,
`write_mem_word_def` `:191-...`).

`'a word` is rendered as `BitVec width` with the reviewed `[NeZero width]`
discharge; `word8` is `BitVec 8`; memory domains are the predicate rendering
`BitVec width → Prop`.  Recursion is on the byte count (`0` returns the input
state, `SUC n` steps toward the next byte according to `s.be`).  Matching the
original HOL types, the address/state word dimension and the read-result (resp.
write-value) word dimension are INDEPENDENT: `read_mem_word : 'b word -> num ->
'b asm_state -> 'a word # 'b asm_state` and `write_mem_word : 'a word -> num ->
'b word -> 'a asm_state -> 'a asm_state`.  Helpers below are Flapjack-internal
infrastructure for the asmProps invariants and carry no tag.
-/

namespace Flapjack.Compiler.Encoders.AsmSem
open Flapjack Flapjack.Compiler.Encoders.Asm
open Classical

@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "addr_def" (words_as_type_indexed_bitvec)]
def addrHOL {width : Nat} [NeZero width] (address : HolAddr width) (s : AsmState width) : BitVec width :=
  match address with | .addr base offset => readReg base s + offset

@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "read_mem_word_def" (words_as_type_indexed_bitvec)]
noncomputable def readMemWord {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth]
    (a : BitVec width) : Nat → AsmState width → BitVec resultWidth × AsmState width
  | 0, s => (0, s)
  | n + 1, s =>
      let (w, s1) := readMemWord (resultWidth := resultWidth) (if s.be then a - 1 else a + 1) n s
      ((w <<< 8) ||| (BitVec.setWidth resultWidth (readMem a s1)), assertState (decide (s1.memDomain a)) s1)

@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "write_mem_word_def" (words_as_type_indexed_bitvec)]
noncomputable def writeMemWord {width : Nat} [NeZero width] {valueWidth : Nat} [NeZero valueWidth]
    (a : BitVec width) : Nat → BitVec valueWidth → AsmState width → AsmState width
  | 0, _, s => s
  | n + 1, w, s =>
      let s1 := writeMemWord (valueWidth := valueWidth) (if s.be then a - 1 else a + 1) n (w >>> 8) s
      assertState (decide (s1.memDomain a)) (updMem a (BitVec.setWidth 8 w) s1)

theorem readMemWord_succ {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth]
    (a : BitVec width) (n : Nat) (s : AsmState width) :
    readMemWord (resultWidth := resultWidth) a (n + 1) s =
      (let (w, s1) := readMemWord (resultWidth := resultWidth) (if s.be then a - 1 else a + 1) n s
       ((w <<< 8) ||| (BitVec.setWidth resultWidth (readMem a s1)), assertState (decide (s1.memDomain a)) s1)) := rfl

theorem writeMemWord_succ {width : Nat} [NeZero width] {valueWidth : Nat} [NeZero valueWidth]
    (a : BitVec width) (n : Nat) (w : BitVec valueWidth) (s : AsmState width) :
    writeMemWord (valueWidth := valueWidth) a (n + 1) w s =
      (let s1 := writeMemWord (valueWidth := valueWidth) (if s.be then a - 1 else a + 1) n (w >>> 8) s
       assertState (decide (s1.memDomain a)) (updMem a (BitVec.setWidth 8 w) s1)) := rfl

@[simp] theorem assertState_be {width : Nat} [NeZero width] (c : Bool) (s : AsmState width) : (assertState c s).be = s.be := rfl
@[simp] theorem assertState_lr {width : Nat} [NeZero width] (c : Bool) (s : AsmState width) : (assertState c s).lr = s.lr := rfl
@[simp] theorem assertState_align {width : Nat} [NeZero width] (c : Bool) (s : AsmState width) : (assertState c s).align = s.align := rfl
@[simp] theorem assertState_memDomain {width : Nat} [NeZero width] (c : Bool) (s : AsmState width) : (assertState c s).memDomain = s.memDomain := rfl
@[simp] theorem assertState_mem {width : Nat} [NeZero width] (c : Bool) (s : AsmState width) : (assertState c s).mem = s.mem := rfl
@[simp] theorem updMem_be {width : Nat} [NeZero width] (a : BitVec width) (v : BitVec 8) (s : AsmState width) : (updMem a v s).be = s.be := rfl
@[simp] theorem updMem_lr {width : Nat} [NeZero width] (a : BitVec width) (v : BitVec 8) (s : AsmState width) : (updMem a v s).lr = s.lr := rfl
@[simp] theorem updMem_align {width : Nat} [NeZero width] (a : BitVec width) (v : BitVec 8) (s : AsmState width) : (updMem a v s).align = s.align := rfl
@[simp] theorem updMem_memDomain {width : Nat} [NeZero width] (a : BitVec width) (v : BitVec 8) (s : AsmState width) : (updMem a v s).memDomain = s.memDomain := rfl
@[simp] theorem updMem_mem {width : Nat} [NeZero width] (a : BitVec width) (v : BitVec 8) (s : AsmState width) (x : BitVec width) : (updMem a v s).mem x = if x = a then v else s.mem x := rfl
@[simp] theorem updMem_failed {width : Nat} [NeZero width] (a : BitVec width) (v : BitVec 8) (s : AsmState width) : (updMem a v s).failed = s.failed := rfl

theorem not_failed_assertState {width : Nat} [NeZero width] {c : Bool} {t : AsmState width}
    (h : ¬ (assertState c t).failed) : c = true ∧ t.failed = false := by
  have h' : (!c || t.failed) = false := by
    simpa only [assertState, Bool.not_eq_true] using h
  rw [Bool.or_eq_false_iff] at h'
  refine ⟨?_, h'.2⟩
  have : (!c) = false := h'.1
  simpa using congrArg Bool.not this

set_option maxHeartbeats 1000000 in
theorem readMemWord_mem_eq_direct {width : Nat} [NeZero width] {resultWidth : Nat} [NeZero resultWidth]
    (a : BitVec width) (k : Nat) (s : AsmState width) :
    (readMemWord (resultWidth := resultWidth) a k s).2.mem = s.mem := by
  induction k generalizing a s with
  | zero => simp [readMemWord]
  | succ n ih =>
      rw [readMemWord_succ]
      generalize hr : readMemWord (resultWidth := resultWidth) (if s.be then a - 1 else a + 1) n s = r
      obtain ⟨w0, s0⟩ := r
      have ih1 := ih (if s.be then a - 1 else a + 1) s
      rw [hr] at ih1
      simpa using ih1

end Flapjack.Compiler.Encoders.AsmSem
