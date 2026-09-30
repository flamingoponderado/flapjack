import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! StackSem bitmap-copy prerequisites. Source: stackSemScript.sml:688-699.
The source word-sized stride is byteTheory bytes_in_word_def:193-195,
 n2w (dimindex DIV 8). Memory updates store Word cells, not byte chunks. -/
namespace Flapjack.StackSemStoreConsts

open StackSemStateOps

/-- HOL bitmap-pattern copy: zero fails; the sentinel one succeeds without
checking the domain or index. Each low bit controls relocation of one word. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_for_pattern_def"
  (words_as_type_indexed_bitvec)]
def copyWordsForPattern {width : Nat} [NeZero width]
    (pattern : BitVec width) (index : Nat) (address offset : BitVec width)
    (bitmaps : List (BitVec width)) (domain : BitVec width → Prop)
    [DecidablePred domain] (memory : BitVec width → WordLocW width) :
    Option (Nat × BitVec width × (BitVec width → WordLocW width)) :=
  if hzero : pattern = 0 then none else
  if pattern = 1 then some (index, address, memory) else
  if h : domain address ∧ index < bitmaps.length then
    let value := bitmaps[index]
    let nextMemory := fun key =>
      if key = address then .word (if pattern.getLsbD 0 then value + offset else value)
      else memory key
    copyWordsForPattern (pattern >>> (1 : Nat)) (index + 1)
      (address + BitVec.ofNat width (width / 8)) offset bitmaps domain nextMemory
  else none
termination_by pattern.toNat
decreasing_by
  have hp : 0 < pattern.toNat := by
    have : pattern.toNat ≠ 0 := by
      intro hz
      apply hzero
      apply BitVec.eq_of_toNat_eq
      simpa using hz
    omega
  change (pattern >>> (1 : Nat)).toNat < pattern.toNat
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self hp (by decide)

/-- Successful bitmap copying never decreases the input index. This is the
termination prerequisite for the outer copy_words recursion. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_for_pattern_LESS_EQ"
  (words_as_type_indexed_bitvec)]
theorem copyWordsForPattern_index_le {width : Nat} [NeZero width]
    (pattern : BitVec width) (index : Nat) (address offset : BitVec width)
    (bitmaps : List (BitVec width)) (domain : BitVec width → Prop)
    [DecidablePred domain] (memory : BitVec width → WordLocW width)
    (finalIndex : Nat)
    (finalState : BitVec width × (BitVec width → WordLocW width))
    (h : copyWordsForPattern pattern index address offset bitmaps domain memory =
      some (finalIndex, finalState)) : index ≤ finalIndex := by
  fun_induction copyWordsForPattern pattern index address offset bitmaps domain memory
  case case1 => contradiction
  case case2 => cases h; exact Nat.le_refl _
  case case3 pattern index address memory hzero hone hdom value nextMemory ih =>
    exact Nat.le_trans (Nat.le_succ index) (ih h)
  case case4 => contradiction

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- HOL `copy_words_def` (`cakeml/compiler/backend/semantics/stackSemScript.sml`):
the outer bitmap copy over the exact StackSem bitmap/memory carriers.  Reuses the
accepted tagged `copyWordsForPattern` and its index bound. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_def"
  (words_as_type_indexed_bitvec)]
def copyWordsExact {width : Nat} [NeZero width] (i : Nat) (a off : BitVec width)
    (bs : List (BitVec width)) (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → WordLocW width) :
    Option (BitVec width × (BitVec width → WordLocW width)) :=
  if _h : bs.length ≤ i then none
  else
    let pattern := bs[i]!
    match _hcp : copyWordsForPattern pattern (i + 1) a off bs domain memory with
    | none => none
    | some (i1, a1, m1) =>
        if pattern.msb then copyWordsExact i1 a1 off bs domain m1 else some (a1, m1)
termination_by bs.length - i
decreasing_by
  simp_wf
  have hle : i + 1 ≤ i1 :=
    copyWordsForPattern_index_le pattern (i + 1) a off bs domain memory i1 (a1, m1) _hcp
  omega

/-- Same-module re-export of the canonical finite-map codec witness for the
    owning `StackSemStateFiniteExact` carrier; Flapjack infrastructure, not a
    separate HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Flapjack-only helper for HOL `unset_var_def`
(`cakeml/compiler/backend/semantics/stackSemScript.sml:725-727`):
`s.regs \\ v` is HOL `FDOMSUB`, rendered with the reviewed `eraseEq`. The
support only shrinks, so the owning state's canonical witness still covers it.
This is not a separately tagged declaration; it is the `unset_var 0` operation
used by `store_const_sem`. -/
def unsetVarZero {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with regs := s.regs.eraseEq 0 }

/-- HOL `store_const_sem` (`cakeml/compiler/backend/semantics/stackSemScript.sml`):
if the six registers `[0;1;2;3;t1;t2]` are not all distinct it returns
`(SOME Error, s)`; otherwise it reads registers 1, 2, 3 as words `i`, `a`, `off`
(any non-word or missing operand is `(SOME Error, s)`), runs the exact
`copyWordsExact (w2n i) a off s.bitmaps s.mdomain s.memory` and propagates its
`NONE` as `(SOME Error, s)`. On success it stores `1` into `t1`, `t2` and
register `1`, stores the returned address into register `2`, installs the
returned memory, and, when `s.use_alloc`, removes register `0` (`unset_var 0`);
the result is `(NONE, ...)`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "store_const_sem_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def storeConstSem {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if ¬ [0, 1, 2, 3, t1, t2].Nodup then (some .error, s) else
    match getVar 1 s, getVar 2 s, getVar 3 s with
    | some (.word i), some (.word a), some (.word off) =>
        match copyWordsExact i.toNat a off s.bitmaps (fun x => s.mdomain x = true) s.memory with
        | none => (some .error, s)
        | some (a', m) =>
            (none, (if s.useAlloc then unsetVarZero else id)
              (setVar t1 (.word 1) (setVar t2 (.word 1)
                (setVar 1 (.word 1) (setVar 2 (.word a') { s with memory := m })))))
    | _, _, _ => (some .error, s)

end Flapjack.StackSemStoreConsts
