import Flapjack.HolRef
import Flapjack.RiscV.L3.Support
import Flapjack.HolArb
import Mathlib.Data.BitVec
import Mathlib.Data.List.Basic

/-!
# Library renderings for the L3 ARMv8 model

Flapjack library infrastructure required by the L3 ARMv8 definitions.  The
pinned HOL model states its bit-vector helpers over `bitstring` (`bool list`,
most-significant bit first) and `fcp` (`bool ** 'N`), and uses the HOL list,
set, word and integer libraries.  These helpers implement the corresponding
HOL equations; they are untagged infrastructure because they are total Lean
renderings of total HOL functions whose out-of-range cases (notably `HD []`
and `MOD 0`) are unspecified in HOL.  Every caller keeps its original bounds;
helper availability does not certify an unreviewed model equation.

The `fcp` carrier `bool ** 'N` is rendered as `BitVec N` by
`scripts/hol_terms_to_lean.py`; the conversions below are the only bridge
between the two representations.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack

/-- `bitstring$v2n_def`: the numeric value of a most-significant-bit-first
bit list (`l2n 2 (bitify [] l)`). -/
def holV2n (v : List Bool) : Nat :=
  v.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

/-- `list$PAD_LEFT`: prepend `n - LENGTH s` copies of `c`. -/
def holPadLeft (c : Bool) (n : Nat) (s : List Bool) : List Bool :=
  List.replicate (n - s.length) c ++ s

/-- `list$PAD_RIGHT`: append `n - LENGTH s` copies of `c`. -/
def holPadRight (c : Bool) (n : Nat) (s : List Bool) : List Bool :=
  s ++ List.replicate (n - s.length) c

/-- `list$HD`: head of a non-empty list.  HOL leaves `HD []` unspecified;
this rendering returns `false` there.  Every model call applies `HD` to a
non-empty list. -/
def holHd (l : List Bool) : Bool :=
  l.headD false

/-- `bitstring$fixwidth_def`: pad on the left when short, otherwise drop the
high bits. -/
def holFixwidth (n : Nat) (v : List Bool) : List Bool :=
  if v.length < n then holPadLeft false n v else v.drop (v.length - n)

/-- `bitstring$shiftr_def`: `TAKE (LENGTH v - m) v`. -/
def holShiftr (v : List Bool) (m : Nat) : List Bool :=
  v.take (v.length - m)

/-- `bitstring$shiftl_def`: `PAD_RIGHT F (LENGTH v + m) v`. -/
def holShiftl (v : List Bool) (m : Nat) : List Bool :=
  holPadRight false (v.length + m) v

/-- `bitstring$field_def`: `fixwidth (SUC h - l) (shiftr v l)`. -/
def holField (h l : Nat) (v : List Bool) : List Bool :=
  holFixwidth (h + 1 - l) (holShiftr v l)

/-- `bitstring$rotate_def`: rotate left by `m MOD LENGTH v`. -/
def holRotate (v : List Bool) (m : Nat) : List Bool :=
  let l := v.length
  let x := m % l
  if l = 0 ∨ x = 0 then v else holField (x - 1) 0 v ++ holField (l - 1) x v

/-- `bitstring$testbit_def`: `field b b v = [T]`. -/
def holTestbit (b : Nat) (v : List Bool) : Bool :=
  holField b b v = [true]

/-- `bitstring$w2v_def`: the most-significant-bit-first bit list of a word,
`GENLIST (λi. w ' (dimindex - 1 - i)) dimindex`. -/
def holW2v {width : Nat} [NeZero width] (w : BitVec width) : List Bool :=
  (List.range width).map (fun i => w.getLsbD (width - 1 - i))

/-- `bitstring$bitwise_def`: `MAP (UNCURRY f) (ZIP (fixwidth m v1, fixwidth m v2))`
at `m = MAX (LENGTH v1) (LENGTH v2)`. -/
def holBitwise (f : Bool → Bool → Bool) (v1 v2 : List Bool) : List Bool :=
  let m := max v1.length v2.length
  (holFixwidth m v1).zipWith f (holFixwidth m v2)

/-- `bitstring$bxor_def`: `bitwise (<>);` Boolean inequality. -/
def holBxor (v1 v2 : List Bool) : List Bool :=
  holBitwise (fun a b => a ≠ b) v1 v2

/-- `bitstring$replicate_def`: `FLAT (GENLIST (K v) n)`. -/
def holReplicate (v : List Bool) (n : Nat) : List Bool :=
  (List.replicate n v).flatten

/-- `words$word_log2_def`: `n2w (LOG2 (w2n w))`. -/
def holWordLog2 {width : Nat} (w : BitVec width) : BitVec width :=
  BitVec.ofNat width (Nat.log2 w.toNat)

/-- `words$word_hi_def`: unsigned greater-than (`c ∧ ¬z`). -/
def holWordHi {width : Nat} (a b : BitVec width) : Bool :=
  BitVec.ult b a

/-- The `CountTrailing` recursion guard fails only when the current word is
nonzero, so the shifted word is strictly smaller. -/
theorem holCountTrailing_pos {TN : Nat} (b : Bool) (w : BitVec TN)
    (h : ¬ ((w.getLsbD 0 == b) || (if b then w == 0 else w == -1))) :
    0 < w.toNat := by
  have hw : w ≠ 0 := by
    intro hw
    cases b
    · exact h (by simp [hw])
    · exact h (by simp [hw])
  exact Nat.pos_of_ne_zero (fun hz => hw (BitVec.eq_of_toNat_eq (by simpa using hz)))

/-- `bitstring$v2w_def` at an explicit width, shared with the RISC-V L3
rendering. -/
abbrev holV2w (a : Nat) (v : List Bool) : BitVec a :=
  Flapjack.RiscV.L3.holV2w a v

/-- `words$word_extract` at an explicit result width, shared with the RISC-V
L3 rendering. -/
abbrev holWordExtract (b : Nat) {a : Nat} (h l : Nat) (w : BitVec a) : BitVec b :=
  Flapjack.RiscV.L3.holWordExtract b h l w

/-- `words$bit_field_insert` for in-range calls, shared with the RISC-V L3
rendering. -/
abbrev holBitFieldInsert {m n : Nat} (h l : Nat) (a : BitVec m) (w : BitVec n) : BitVec n :=
  Flapjack.RiscV.L3.holBitFieldInsert h l a w

/-- HOL `combin$UPDATE a b f`, shared with the RISC-V L3 rendering. -/
abbrev holUpdate {α β : Type} [DecidableEq α] (a : α) (b : β) (f : α → β) : α → β :=
  Flapjack.RiscV.L3.holUpdate a b f

end Flapjack.Compiler.Encoders.Arm8.L3
