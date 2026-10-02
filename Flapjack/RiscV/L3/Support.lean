import Flapjack.RiscV.L3.Types
import Flapjack.Misc.Option
import Flapjack.Misc.Alignment

/-!
# L3 RISC-V model: renderings of the HOL library constants it uses

The exported definitions of the L3 RISC-V model (`scripts/hol_terms_to_lean.py`) render most
HOL library constants directly as Lean operations (for example `word_add` as `+` on `BitVec`).
This module holds the remaining renderings, each following the cited HOL definition:
* `combin$UPDATE` (`combinScript.sml:32-33`): `UPDATE a b = λf c. if a = c then b else f c`.
* `words$word_extract` (`wordsScript.sml:243-255`): `w2w o word_bits h l`, where bit `i` of
  `word_bits h l w` is `i + l ≤ MIN h (dimindex - 1) ∧ w ' (i + l)`.
* `words$bit_field_insert` (`wordsScript.sml:265-283`): `word_modify (λi. COND (l ≤ i ∧
  i ≤ h) (a ' (i - l)))`.
* `words$word_replicate` (`wordsScript.sml:587-590`): bit `i` is
  `i < n * dimindex(:'a) ∧ w ' (i MOD dimindex(:'a))`.
* `bitstring$v2w` (`bitstringScript.sml:88-99`): bit `i` is `testbit i v`, the `i`-th bit
  from the end of the most-significant-first list `v` (false past its length).
* `state_transformer$FOR` (`state_transformerScript.sml:130-138`).
* `ASCIInumbers$num_to_dec_string` / `words$word_to_hex_string`
  (`ASCIInumbersScript.sml:18-85`, `wordsScript.sml:114`): `n2s b HEX`.
* `bool$ARB` as an uninterpreted constant.

As elsewhere in Flapjack, HOL's FCP index `w ' i` is `BitVec.getLsbD`, which is `false` for an
index past the width where HOL leaves the value unspecified. HOL's `x DIV 0`/`x MOD 0` and
`word_div`/`word_mod` by zero are likewise unspecified, and are Lean's `0`/`x`.
-/

namespace Flapjack.RiscV.L3

open Flapjack.Basis.Pure.MlString

/-- HOL `ARB : α`, an uninterpreted constant (the inhabitedness every HOL type has). -/
opaque holArb (α : Type) [Inhabited α] : α

/-- HOL `combin$UPDATE a b f` (`(a =+ b) f`). -/
def holUpdate {α β : Type} [DecidableEq α] (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c

/-- HOL `words$word_extract h l w : 'b word` at result width `b`. -/
def holWordExtract (b : Nat) {a : Nat} (h l : Nat) (w : BitVec a) : BitVec b :=
  BitVec.setWidth b (BitVec.ofNat a ((w.toNat >>> l) % 2 ^ (min h (a - 1) + 1 - l)))

/-- HOL `words$bit_field_insert h l a w`. -/
def holBitFieldInsert {m n : Nat} (h l : Nat) (a : BitVec m) (w : BitVec n) : BitVec n :=
  Flapjack.holFcpWord fun i => if l ≤ i ∧ i ≤ h then a.getLsbD (i - l) else w.getLsbD i

/-- HOL `words$word_replicate k w : 'b word` at result width `b`. -/
def holWordReplicate (b : Nat) {m : Nat} (k : Nat) (w : BitVec m) : BitVec b :=
  Flapjack.holFcpWord fun i => decide (i < k * m) && w.getLsbD (i % m)

/-- HOL `bitstring$v2w v : 'a word` at width `a`. -/
def holV2w (a : Nat) (v : List Bool) : BitVec a :=
  Flapjack.holFcpWord fun i => decide (i < v.length) && v.getD (v.length - 1 - i) false

/-- HOL `state_transformer$FOR (i, j, a)`. -/
def holFor {σ : Type} : Nat × Nat × (Nat → σ → Unit × σ) → σ → Unit × σ
  | (i, j, a) => fun s =>
      if h : i = j then a i s
      else
        let r := a i s
        holFor ((if i < j then i + 1 else i - 1), j, a) r.2
termination_by p => if p.1 < p.2.1 then p.2.1 - p.1 else p.1 - p.2.1
decreasing_by all_goals (simp_wf; split <;> split <;> omega)

/-- HOL `ASCIInumbers$HEX`. -/
def holHex (n : Nat) : HolChar :=
  if n < 10 then BitVec.ofNat 8 (48 + n) else if n < 16 then BitVec.ofNat 8 (65 + (n - 10))
  else 0

/-- HOL `numposrep$n2l b n`. -/
def holN2l (b n : Nat) : List Nat :=
  if n < b ∨ b < 2 then [n % b] else n % b :: holN2l b (n / b)
termination_by n
decreasing_by
  have _h : ¬ (n < b ∨ b < 2) := by assumption
  exact Nat.div_lt_self (by omega) (by omega)

/-- HOL `ASCIInumbers$n2s b f n = REVERSE (MAP f (n2l b n))`. -/
def holN2s (b : Nat) (f : Nat → HolChar) (n : Nat) : List HolChar :=
  ((holN2l b n).map f).reverse

/-- HOL `ASCIInumbers$num_to_dec_string = n2s 10 HEX`. -/
def holNumToDecString (n : Nat) : List HolChar := holN2s 10 holHex n

/-- HOL `words$word_to_hex_string = w2s 16 HEX`, with `w2s b f w = n2s b f (w2n w)`. -/
def holWordToHexString {a : Nat} (w : BitVec a) : List HolChar := holN2s 16 holHex w.toNat

end Flapjack.RiscV.L3
