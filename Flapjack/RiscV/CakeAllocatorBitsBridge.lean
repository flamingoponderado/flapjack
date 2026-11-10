module

public import Flapjack.RiscV.CakeAllocatorCore
public import Flapjack.Compiler.Backend.WordToStack

@[expose] public section

/-!
# Executable Cake bitmap words vs the tagged HOL recursion (untagged bridge)

The executable CakeML-bitmap helpers in `Flapjack/RiscV/CakeAllocatorCore.lean`
(`bitsToWord`, `frameBitmapWordsAux`, `frameBitmapWords`, `writeBitmap`) are the
`Nat`-valued implementations used by the Cake allocator.  Their HOL originals
(`bits_to_word_def`/`word_list_def` in
`cakeml/compiler/backend/word_to_stackScript.sml`) are polymorphic over the word
carrier.  This module proves, for every input (no range restriction), that the
executable recursion maps onto the tagged width-indexed Lean recursion
`bitsToWordW`/`wordListW`:

* `bitsToWord_ofNat_eq` : `BitVec.ofNat width (bitsToWord bits) = bitsToWordW bits`
  for arbitrary `bits`.  `CakeAlloc.bitsToWord` is exactly the `Nat` value of the
  HOL recursion, and `BitVec.ofNat` performs the same `mod 2^width` truncation
  that HOL's fixed-width `'a word` arithmetic does.  In particular an input whose
  `LENGTH` exceeds `width` wraps: both sides keep only the low `width` bits.

* `frameBitmapWordsAux_map`/`frameBitmapWords_map` : mapping each `Nat` bitmap
  word through `BitVec.ofNat width` reproduces `wordListW` exactly.

* `writeBitmap_eq_writeBitmapHOL` : the whole executed `writeBitmap` (including
  its name-set construction) maps onto the HOL-shaped `writeBitmapHOL` at the
  faithful `wordBits = width` stride, so the executed bitmap builder is
  kernel-checked equal to the exact recursion for every input.

These lemmas are deliberately **untagged**.  HOL `write_bitmap` reads
`toAList live` only through `MEM`, so its value depends solely on the domain of
`live`; `writeBitmapHOL` takes that domain as a `List Nat` and its
`writeBitmapHOL_domain_insensitive` theorem records exactly that insensitivity.
`writeBitmap_eq_writeBitmapHOL` closes the previously-documented name-set gap:
the executable `List.contains` bitmap and the exact `decide (· ∈ names)` bitmap
produce the same words.
-/

namespace Flapjack.RiscV.CakeAlloc

open Flapjack.Compiler.Backend.WordToStack

/-- `(x <<< 1) &&& 1 = 0` for the core Nat-shift `BitVec` instance.  The explicit
`(1 : Nat)` shift amount is required because importing `Flapjack.RiscV.Model`
(via `RegisterMap`/`CakeAllocatorCore`) installs a competing `ShiftLeft` instance
whose shift amount is a `BitVec`, which is syntactically distinct from the core
lemma's form. -/
theorem and_one_shift {w : Nat} [NeZero w] (x : BitVec w) :
    (x <<< (1 : Nat)) &&& 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  have hw : 0 < w := Nat.pos_of_ne_zero (NeZero.ne w)
  cases i with
  | zero => simp [hw]
  | succ j => simp [Nat.succ_lt_succ_iff]

theorem shiftLeft_or_one {w : Nat} [NeZero w] (x : BitVec w) :
    x <<< (1 : Nat) ||| 1 = x <<< (1 : Nat) + 1 :=
  (BitVec.add_eq_or_of_and_eq_zero (x <<< (1 : Nat)) 1 (and_one_shift x)).symm

theorem ofNat_shift {w : Nat} [NeZero w] (n : Nat) :
    BitVec.ofNat w (n * 2) = (BitVec.ofNat w n) <<< (1 : Nat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.pow_one]
  rw [Nat.mod_mul_mod]

theorem ofNat_shift_or_one {w : Nat} [NeZero w] (n : Nat) :
    BitVec.ofNat w (n * 2 + 1) = (BitVec.ofNat w n) <<< (1 : Nat) ||| 1 := by
  rw [BitVec.ofNat_add (n * 2) 1, ofNat_shift n, shiftLeft_or_one]
  rfl

/-- Executable `List.contains` equals the decidable-membership bitmap test, the
form HOL `write_bitmap` uses (`MEM` over `toAList live`). -/
theorem contains_eq_decide_mem (names : List Nat) (slot : Nat) :
    names.contains slot = decide (slot ∈ names) := by
  unfold List.contains
  rw [List.elem_eq_mem]

end Flapjack.RiscV.CakeAlloc