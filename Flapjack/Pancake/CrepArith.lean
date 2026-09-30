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

/-- Generic Flapjack helper for extracting a value from a Const node.
    This is not tagged as CakeML's `dest_const_def`: HOL's `crepLang$Const`
    stores an `'a word`, while this production helper accepts arbitrary `α`.
    The exact word-carrier definition below uses `CrepExpHOL`; this helper is
    retained for the executable simplifier. -/
def crepDestConst : CrepExp α → Option α
  | .const value => some value
  | _ => none

/-- Flapjack-only word-valued adapter over the generic production AST. It is
    not the HOL definition because its syntax carrier is generic `CrepExp`,
    rather than the exact width-indexed `CrepExpHOL`. -/
def crepDestConstHolWord {width : Nat} [NeZero width] :
    CrepExp (Fin width → Bool) → Option (Fin width → Bool)
  | .const value => some value
  | _ => none

/-- Flapjack-only reduction of the word-valued adapter to the generic helper. -/
theorem crepDestConstHolWord_eq_production {width : Nat} [NeZero width]
    (expression : CrepExp (Fin width → Bool)) :
    crepDestConstHolWord expression = crepDestConst expression := by
  cases expression <;> rfl

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

/-- Flapjack-only connection between the exact HOL carrier and the generic
    production syntax. This has no HOL counterpart because it crosses two
    different Lean expression carriers. -/
theorem crepDestConstHOL_eq_production {width : Nat} [NeZero width]
    (expression : CrepExpHOL width) :
    crepDestConstHOL expression = crepDestConst (crepExpOfHOL expression) := by
  cases expression <;> simp [crepDestConstHOL, crepDestConst, crepExpOfHOL]

def crepDest2ExpFuel [BEq α] [OfNat α 0] [OfNat α 1]
    [AndOp α] [ShiftRight α] : Nat → Nat → α → Option Nat
  | 0, _, _ => none
  | fuel + 1, exponent, word =>
      if word == 0 then none
      else if word == 1 then some exponent
      else if AndOp.and word 1 != 0 then none
      else crepDest2ExpFuel fuel (exponent + 1) (ShiftRight.shiftRight word 1)
termination_by fuel => fuel

/-! Fixed-width executable form of CakeML's `crep_arith$dest_2exp_def`
    (`crep_arithScript.sml:15`).  The word width supplies the finite bound
    needed by Lean's termination checker; each recursive step is the HOL
    logical right shift by one. -/
def crepDest2Exp [PanShiftWidth α] [BEq α] [OfNat α 0] [OfNat α 1]
    [AndOp α] [ShiftRight α] (n : Nat) (word : α) : Option Nat :=
  crepDest2ExpFuel (PanShiftWidth.width (α := α) + 1) n word

/-! A value-recursive specification support for `dest_2exp`. Unlike the
    executable recognizer above, this follows the source recursion until the
    word is zero, one, or odd. This Flapjack Boolean-test helper is untagged;
    the source-shaped positive-width port is `crepDest2ExpHOL` below. The
    unconditional equality `crepDest2ExpBitVecSpec_eq_HOL` in the proof
    counterpart relates this helper to that reviewed definition. -/
def crepDest2ExpBitVecSpec {width : Nat} [NeZero width] (exponent : Nat)
    (word : BitVec width) : Option Nat :=
  if word == 0 then none
  else if word == 1 then some exponent
  else if AndOp.and word 1 != 0 then none
  else crepDest2ExpBitVecSpec (exponent + 1)
    (BitVec.ushiftRight word 1)
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

/-! Fixed-width executable port of CakeML's `crep_arith$mul_const`.
    Constants zero and one are handled directly; powers of two become a left
    shift, while all other constants retain the original multiplication node.
    `fromNat` is the target word embedding (CakeML's `n2w`). -/
def crepMulConst [BEq α] [OfNat α 0] [OfNat α 1] [AndOp α] [ShiftRight α]
    [PanShiftWidth α] (fromNat : Nat → α)
    (expression : CrepExp α) (constant : α) : CrepExp α :=
  if constant == 0 then .const 0
  else if constant == 1 then expression
  else match crepDest2Exp 0 constant with
    | none => .crepOp .mul [expression, .const constant]
    | some exponent => .shift .lsl expression (.const (fromNat exponent))

/-! Fixed-width executable port of CakeML's `crep_arith$simp_exp`.
    The expression tree is simplified bottom-up.  Only binary multiplication
    receives arithmetic-specific treatment; all other constructors preserve
    their original shape after recursively simplifying their children. -/
def crepSimpExp [BEq α] [OfNat α 0] [OfNat α 1] [Mul α] [AndOp α]
    [ShiftRight α] [PanShiftWidth α] (fromNat : Nat → α) :
    CrepExp α → CrepExp α
  | .load address => .load (crepSimpExp fromNat address)
  | .load32 address => .load32 (crepSimpExp fromNat address)
  | .loadByte address => .loadByte (crepSimpExp fromNat address)
  | .op operator expressions => .op operator (expressions.map (crepSimpExp fromNat))
  | .crepOp operator expressions =>
      let expressions := expressions.map (crepSimpExp fromNat)
      match operator, expressions with
      | .mul, [.const left, .const right] =>
          match crepDestConst (.const left), crepDestConst (.const right) with
          | some leftConstant, some rightConstant =>
              .const (leftConstant * rightConstant)
          | _, _ => .crepOp operator expressions
      | .mul, [.const constant, expression] =>
          match crepDestConst (.const constant) with
          | some value => crepMulConst fromNat expression value
          | none => .crepOp operator expressions
      | .mul, [expression, .const constant] =>
          match crepDestConst (.const constant) with
          | some value => crepMulConst fromNat expression value
          | none => .crepOp operator expressions
      | _, _ => .crepOp operator expressions
  | .cmp operator left right =>
      .cmp operator (crepSimpExp fromNat left) (crepSimpExp fromNat right)
  | .shift operator left right =>
      .shift operator (crepSimpExp fromNat left) (crepSimpExp fromNat right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

/-! Fixed-width executable port of CakeML's `crep_arith$simp_prog`.
    Program nodes preserve their original sequencing and control structure;
    every embedded expression is simplified, including call handlers. -/
def crepSimpProg [BEq α] [OfNat α 0] [OfNat α 1] [Mul α] [AndOp α]
    [ShiftRight α] [PanShiftWidth α] (fromNat : Nat → α) :
    CrepProg α → CrepProg α
  | .skip => .skip
  | .dec name value body =>
      .dec name (crepSimpExp fromNat value) (crepSimpProg fromNat body)
  | .assign name value => .assign name (crepSimpExp fromNat value)
  | .primitive names operator arguments =>
      .primitive names operator arguments
  | .store address value =>
      .store (crepSimpExp fromNat address) (crepSimpExp fromNat value)
  | .store32 address value =>
      .store32 (crepSimpExp fromNat address) (crepSimpExp fromNat value)
  | .storeByte address value =>
      .storeByte (crepSimpExp fromNat address) (crepSimpExp fromNat value)
  | .storeGlob address value =>
      .storeGlob address (crepSimpExp fromNat value)
  | .seq first second =>
      .seq (crepSimpProg fromNat first) (crepSimpProg fromNat second)
  | .ite condition thenBranch elseBranch =>
      .ite (crepSimpExp fromNat condition) (crepSimpProg fromNat thenBranch)
        (crepSimpProg fromNat elseBranch)
  | .while condition body =>
      .while (crepSimpExp fromNat condition) (crepSimpProg fromNat body)
  | .break label => .break label
  | .continue label => .continue label
  | .call returnInfo name arguments =>
      let returnInfo :=
        match returnInfo with
        | none => none
        | some (names, none) => some (names, none)
        | some (names, some (handler, body)) =>
            some (names, some (handler, crepSimpProg fromNat body))
      .call returnInfo name (arguments.map (crepSimpExp fromNat))
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function configuration configurationLength array arrayLength
  | .raise exception => .raise exception
  | .return values => .return (values.map (crepSimpExp fromNat))
  | .shMem operator name address =>
      .shMem operator name (crepSimpExp fromNat address)
  | .tick => .tick
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

/-! `crep_arith$simp_prog` lifted over a compiled-function list, matching the
    per-body application in CakeML's `crep_to_loop$compile_prog`
    (`crep_to_loopScript.sml:264`). -/
def crepSimpFunctions [BEq α] [OfNat α 0] [OfNat α 1] [Mul α] [AndOp α]
    [ShiftRight α] [PanShiftWidth α] (fromNat : Nat → α) :
    List (CompiledFunction α) → List (CompiledFunction α)
  | [] => []
  | function :: functions =>
      { function with body := crepSimpProg fromNat function.body } ::
        crepSimpFunctions fromNat functions

/-! ## Exact-carrier ports of the `crep_arith` definitions

The definitions below are the source-shaped ports of `dest_2exp`, `mul_const`,
`simp_exp` and `simp_prog` over the exact width-indexed `CrepExpHOL` /
`CrepProgHOL` carriers.  They are separate from the generic executable
`crepSimpExp` / `crepSimpProg` above, which stay untagged because they accept
an arbitrary value carrier. -/

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

def crepArithExp [Mul α] : CrepExp α → CrepExp α
  | .load address => .load (crepArithExp address)
  | .load32 address => .load32 (crepArithExp address)
  | .loadByte address => .loadByte (crepArithExp address)
  | .op operator expressions => .op operator (expressions.map crepArithExp)
  | .crepOp operator expressions =>
      let expressions := expressions.map crepArithExp
      match operator, expressions with
      | .mul, [.const left, .const right] => .const (left * right)
      | _, _ => .crepOp operator expressions
  | .cmp operator left right =>
      .cmp operator (crepArithExp left) (crepArithExp right)
  | .shift operator left right =>
      .shift operator (crepArithExp left) (crepArithExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

def crepArithProg [Mul α] : CrepProg α → CrepProg α
  | .skip => .skip
  | .dec name value body =>
      .dec name (crepArithExp value) (crepArithProg body)
  | .assign name value => .assign name (crepArithExp value)
  | .primitive names operator arguments =>
      .primitive names operator arguments
  | .store address value =>
      .store (crepArithExp address) (crepArithExp value)
  | .store32 address value =>
      .store32 (crepArithExp address) (crepArithExp value)
  | .storeByte address value =>
      .storeByte (crepArithExp address) (crepArithExp value)
  | .storeGlob address value =>
      .storeGlob address (crepArithExp value)
  | .seq first second =>
      .seq (crepArithProg first) (crepArithProg second)
  | .ite condition thenBranch elseBranch =>
      .ite (crepArithExp condition) (crepArithProg thenBranch)
        (crepArithProg elseBranch)
  | .while condition body =>
      .while (crepArithExp condition) (crepArithProg body)
  | .break label => .break label
  | .continue label => .continue label
  | .call none name arguments =>
      .call none name (arguments.map crepArithExp)
  | .call (some (names, none)) name arguments =>
      .call (some (names, none)) name (arguments.map crepArithExp)
  | .call (some (names, some (handler, body))) name arguments =>
      .call (some (names, some (handler, crepArithProg body))) name
        (arguments.map crepArithExp)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function configuration configurationLength array arrayLength
  | .raise exception => .raise exception
  | .return values => .return (values.map crepArithExp)
  | .shMem operator name address =>
      .shMem operator name (crepArithExp address)
  | .tick => .tick
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

def crepArithFunctions [Mul α] : List (CompiledFunction α) →
    List (CompiledFunction α)
  | [] => []
  | function :: functions =>
      { function with body := crepArithProg function.body } ::
        crepArithFunctions functions

end Flapjack
