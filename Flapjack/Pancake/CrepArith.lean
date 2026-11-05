import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.RiscV.Model

/-!
Executable arithmetic simplification for Crepe.

CakeML's `crep_arith` pass folds constant `Mul` nodes before the
Crepe-to-Loop boundary.  Keeping this pass separate makes its placement in
the pipeline explicit and leaves the transformation available to clients
that inspect intermediate artifacts.
-/

namespace Flapjack

/-- Exact port of CakeML's `crep_arith$dest_const_def`
    (`crep_arithScript.sml:10-12`) over `CrepExpHOL`. Its implicit `width`
    ranges over every positive HOL word dimension; `BitVec width` is the
    canonical `Fin width → Bool` representation, so any finite HOL word index
    of that cardinality is transported by reindexing. The generic executable
    helper above stays untagged because it accepts any value carrier. -/
@[hol "cakeml/pancake/crep_arithScript.sml" "dest_const_def"]
def crepDestConstHOL {width : Nat} [NeZero width] :
    CrepExpHOL width → Option (BitVec width)
  | .const value => some value
  | _ => none

/-! The following definitions are the source-shaped ports over the
width-indexed `CrepExpHOL` and `CrepProgHOL` carriers. -/

/-- Exact port of CakeML's `crep_arith$dest_2exp`
    (`crep_arithScript.sml:15-19`).  Recursion is well-founded on the word's
    value; each step is HOL `word_lsr w 1`. -/
@[hol "cakeml/pancake/crep_arithScript.sml" "dest_2exp_def" (words_as_type_indexed_bitvec)]
def crepDest2ExpHOL {width : Nat} [NeZero width] (exponent : Nat)
    (word : BitVec width) : Option Nat :=
  if word = 0 then none
  else if word = 1 then some exponent
  else if word &&& 1 ≠ 0 then none
  else crepDest2ExpHOL (exponent + 1) (BitVec.ushiftRight word 1)
termination_by word.toNat
decreasing_by
  simp_wf
  have hword : word.toNat ≠ 0 := by
    intro hzero
    have hEq : word = 0 := BitVec.eq_of_toNat_eq (by simpa using hzero)
    simp [hEq] at *
  change (BitVec.ushiftRight word 1).toNat < word.toNat
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hword) (by decide)

/-- Exact HOL `dest_2exp_lemma` (`crep_arithScript.sml:22-41`, a `[local]` theorem):
    `dest_2exp i w = SOME n ⇒ i ≤ n ∧ w = word_lsl 1w (n - i)`. -/
@[hol "cakeml/pancake/crep_arithScript.sml" "dest_2exp_lemma" (words_as_type_indexed_bitvec)]
theorem crepDest2ExpHOL_lemma {width : Nat} [NeZero width] :
    ∀ (i : Nat) (w : BitVec width) (n : Nat), crepDest2ExpHOL i w = some n →
      i ≤ n ∧ w = (1 : BitVec width) <<< (n - i) := by
  intro i w
  induction hk : w.toNat using Nat.strongRecOn generalizing i w with
  | ind k ih =>
  intro n h
  rw [crepDest2ExpHOL] at h
  by_cases h0 : w = 0
  · rw [if_pos h0] at h; cases h
  rw [if_neg h0] at h
  by_cases h1 : w = 1
  · rw [if_pos h1, Option.some.injEq] at h
    subst h; subst h1
    simp
  rw [if_neg h1] at h
  by_cases hb : w &&& 1 ≠ 0
  · rw [if_pos hb] at h; cases h
  rw [if_neg hb] at h
  have hwpos : 0 < w.toNat := by
    rcases Nat.eq_zero_or_pos w.toNat with hz | hz
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using hz)) h0
    · exact hz
  have hlt : (BitVec.ushiftRight w 1).toNat < k := by
    rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, ← hk]
    exact Nat.div_lt_self hwpos (by decide)
  obtain ⟨hle, hshift⟩ := ih _ hlt (i + 1) (BitVec.ushiftRight w 1) rfl n h
  have hb' : w &&& 1 = 0 := Classical.not_not.mp hb
  have heven : w.toNat % 2 = 0 := by
    have h2 := congrArg BitVec.toNat hb'
    have hw1 : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
    have hone : (1 : BitVec width).toNat = 1 := by
      show (BitVec.ofNat width 1).toNat = 1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw1]
    rw [BitVec.toNat_and, hone, Nat.and_one_is_mod] at h2
    simpa using h2
  refine ⟨by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have hw' : w.toNat = (BitVec.ushiftRight w 1).toNat * 2 := by
    rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  have hwlt : w.toNat < 2 ^ width := w.isLt
  have hw1 : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have hone : (1 : BitVec width).toNat = 1 := by
    show (BitVec.ofNat width 1).toNat = 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw1]
  rw [hw', hshift] at hwlt ⊢
  simp only [BitVec.toNat_shiftLeft, hone, Nat.shiftLeft_eq, Nat.one_mul] at hwlt ⊢
  have hsub : n - i = (n - (i + 1)) + 1 := by omega
  rw [hsub]
  generalize n - (i + 1) = m at hwlt ⊢
  rcases Nat.lt_or_ge m width with hm | hm
  · have hpm : 2 ^ m < 2 ^ width := Nat.pow_lt_pow_right (by decide) hm
    rw [Nat.mod_eq_of_lt hpm] at hwlt ⊢
    rw [Nat.pow_succ, Nat.mod_eq_of_lt (by rw [← Nat.pow_succ] at *; omega)]
  · have h1 : 2 ^ m % 2 ^ width = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hm)
    have h2 : 2 ^ (m + 1) % 2 ^ width = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
    rw [h1, h2]

/-- Exact HOL `dest_2exp_thm` (`crep_arithScript.sml:43-48`):
    `dest_2exp 0n w = SOME n2 ⇒ w = word_lsl 1w n2`. -/
@[hol "cakeml/pancake/crep_arithScript.sml" "dest_2exp_thm" (words_as_type_indexed_bitvec)]
theorem crepDest2ExpHOL_thm {width : Nat} [NeZero width] :
    ∀ (w : BitVec width) (n2 : Nat), crepDest2ExpHOL 0 w = some n2 →
      w = (1 : BitVec width) <<< n2 := by
  intro w n2 h
  simpa using (crepDest2ExpHOL_lemma 0 w n2 h).2

/-- Exact port of CakeML's `crep_arith$mul_const`
    (`crep_arithScript.sml:50-57`). -/
@[hol "cakeml/pancake/crep_arithScript.sml" "mul_const_def" (words_as_type_indexed_bitvec)]
def crepMulConstHOL {width : Nat} [NeZero width] (exp : CrepExpHOL width)
    (constant : BitVec width) : CrepExpHOL width :=
  if constant = 0 then .const 0
  else if constant = 1 then exp
  else match crepDest2ExpHOL 0 constant with
    | none => .crepOp .mul [exp, .const constant]
    | some exponent => .shift .lsl exp (.const (BitVec.ofNat width exponent))

/-- Exact port of CakeML's `crep_arith$simp_exp`
    (`crep_arithScript.sml:59-81`).  The expression tree is simplified
    bottom-up; only binary multiplication receives arithmetic-specific
    treatment, matching the HOL `dest_const` dispatch. -/
@[hol "cakeml/pancake/crep_arithScript.sml" "simp_exp_def" (words_as_type_indexed_bitvec)]
def crepSimpExpHOL {width : Nat} [NeZero width] : CrepExpHOL width → CrepExpHOL width
  | .crepOp operator expressions =>
      let expressions := expressions.map crepSimpExpHOL
      match operator, expressions with
      | .mul, [first, second] =>
          match crepDestConstHOL first, crepDestConstHOL second with
          | some left, some right => .const (left * right)
          | some constant, none => crepMulConstHOL second constant
          | none, some constant => crepMulConstHOL first constant
          | none, none => .crepOp operator expressions
      | _, _ => .crepOp operator expressions
  | .load address => .load (crepSimpExpHOL address)
  | .load32 address => .load32 (crepSimpExpHOL address)
  | .loadByte address => .loadByte (crepSimpExpHOL address)
  | .op operator expressions => .op operator (expressions.map crepSimpExpHOL)
  | .cmp operator left right => .cmp operator (crepSimpExpHOL left) (crepSimpExpHOL right)
  | .shift operator left right =>
      .shift operator (crepSimpExpHOL left) (crepSimpExpHOL right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

/-- Exact port of CakeML's `crep_arith$simp_prog`
    (`crep_arithScript.sml:83-105`).  Every embedded expression is simplified,
    including call handlers; the control structure is preserved. -/
@[hol "cakeml/pancake/crep_arithScript.sml" "simp_prog_def" (words_as_type_indexed_bitvec)]
def crepSimpProgHOL {width : Nat} [NeZero width] : CrepProgHOL width → CrepProgHOL width
  | .dec name value body => .dec name (crepSimpExpHOL value) (crepSimpProgHOL body)
  | .assign name value => .assign name (crepSimpExpHOL value)
  | .store address value => .store (crepSimpExpHOL address) (crepSimpExpHOL value)
  | .store32 address value => .store32 (crepSimpExpHOL address) (crepSimpExpHOL value)
  | .storeByte address value => .storeByte (crepSimpExpHOL address) (crepSimpExpHOL value)
  | .storeGlob address value => .storeGlob address (crepSimpExpHOL value)
  | .seq first second => .seq (crepSimpProgHOL first) (crepSimpProgHOL second)
  | .ite condition thenBranch elseBranch =>
      .ite (crepSimpExpHOL condition) (crepSimpProgHOL thenBranch)
        (crepSimpProgHOL elseBranch)
  | .while condition body => .while (crepSimpExpHOL condition) (crepSimpProgHOL body)
  | .call returnInfo name arguments =>
      let returnInfo :=
        match returnInfo with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (handler, body)) =>
            some (returns, some (handler, crepSimpProgHOL body))
      .call returnInfo name (arguments.map crepSimpExpHOL)
  | .return values => .return (values.map crepSimpExpHOL)
  | .shMem operator name address => .shMem operator name (crepSimpExpHOL address)
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

end Flapjack
