module

public import Flapjack.Misc.Words.Formatting
public import Flapjack.Misc.Words.Replicate
public import Flapjack.Misc.StateTransformer
public import Flapjack.RiscV.L3.Types
public import Flapjack.Misc.Option
public import Flapjack.Misc.Alignment
public import Flapjack.HolArb

@[expose] public section

/-! Flapjack library-rendering infrastructure required by the complete L3 FP
section and source-reviewed MMU primitives. These helpers implement UPDATE and the guarded in-range word operations
used by the original equations. ARB uses the single canonical Flapjack constant; no
arbitrary record field is replaced with a chosen default. Each caller retains its original operation bounds; helper availability does not
certify unreviewed model equations. -/
namespace Flapjack.RiscV.L3
open Flapjack.Basis.Pure.MlString

/-- HOL `combin$UPDATE a b f` (`(a =+ b) f`). -/
def holUpdate {α β : Type} [DecidableEq α] (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c

/-- HOL `words$word_extract h l w : 'b word` at result width `b`. -/
def holWordExtract (b : Nat) {a : Nat} (h l : Nat) (w : BitVec a) : BitVec b :=
  BitVec.setWidth b (BitVec.ofNat a ((w.toNat >>> l) % 2 ^ (min h (a - 1) + 1 - l)))

/-- Rendering of HOL `words$bit_field_insert h l a w` for calls whose selected
input indices are in range (`h < l` or `h - l < m`). The translator checks this
bound at every model call. Raw HOL FCP indexing is unspecified outside the
input width; this helper's false result there is not an unconditional HOL port. -/
def holBitFieldInsert {m n : Nat} (h l : Nat) (a : BitVec m) (w : BitVec n) : BitVec n :=
  Flapjack.holFcpWord fun i => if l ≤ i ∧ i ≤ h then a.getLsbD (i - l) else w.getLsbD i

/-- Library rendering of `bitstring$v2w_def`: FCP of `testbit`, whose list
is most-significant-bit first. FCLASS uses singleton Boolean lists at width1.
This helper is untagged infrastructure, not a claim about the whole model. -/
def holV2w (a : Nat) (v : List Bool) : BitVec a :=
  Flapjack.holFcpWord fun i => decide (i < v.length) && v.getD (v.length - 1 - i) false

/-- Original `v2w_sing`: a singleton Boolean list is the word one or zero. -/
@[hol "cakeml/misc/miscScript.sml" "v2w_sing" (words_as_type_indexed_bitvec)]
theorem v2w_sing {w : Nat} [NeZero w] (b : Bool) :
    holV2w w [b] = if b then (1 : BitVec w) else (0 : BitVec w) := by
  cases b
  · rw [if_neg (by decide)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [holV2w, Flapjack.getLsbD_holFcpWord]
    simp
  · rw [if_pos rfl]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [holV2w, Flapjack.getLsbD_holFcpWord]
    by_cases hi0 : i = 0
    · simp [hi0, Nat.pos_of_ne_zero (NeZero.ne w)]
    · simp [hi0]

/-- Original `v2w_32_F`: the false singleton is the zero word. -/
@[hol "cakeml/misc/miscScript.sml" "v2w_32_F"]
theorem v2w_32_F : holV2w 32 [false] = 0#32 := by
  decide

/-- Original `v2w_32_T`: the true singleton is the one word. -/
@[hol "cakeml/misc/miscScript.sml" "v2w_32_T"]
theorem v2w_32_T : holV2w 32 [true] = 1#32 := by
  decide


end Flapjack.RiscV.L3
