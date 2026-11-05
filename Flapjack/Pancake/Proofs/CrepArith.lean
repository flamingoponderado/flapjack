import Flapjack.HolRef
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect

/-! Theorem counterparts and Flapjack support for CakeML's
    `crep_arithProofScript.sml`. The tagged `dest_const_thm` uses the exact
    width-indexed `CrepExpHOL` carrier with `[NeZero width]`. -/

namespace Flapjack


/-- Exact port of CakeML's `dest_const_thm` (`crep_arithProofScript.sml:64`).
    `width` ranges over every positive HOL word dimension. `BitVec width` is
    the canonical `Fin width → Bool` representation; any HOL finite word
    index of cardinality `width` is related by reindexing, and this theorem
    only inverts the root constructor. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_const_thm"]
theorem crepDestConstHOL_eq_const {width : Nat} [NeZero width]
    (expression : CrepExpHOL width)
    (value : BitVec width)
    (h : crepDestConstHOL expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConstHOL]


/-- Exact generic list-success monotonicity helper from HOL's local
    `OPT_MMAP_EQ_SOME_MONO` (`crep_arithProofScript.sml:93`).  `List.mapM` with
    the `Option` monad is the Lean encoding of HOL's `OPT_MMAP`; this lemma is
    independent of the Crep evaluator and is used for pointwise successful
    result preservation in the arithmetic simplifier proof. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "OPT_MMAP_EQ_SOME_MONO" 93]
theorem optMmapEqSomeMono {α β : Type} (f g : α → Option β)
    (xs : List α) (ys : List β)
    (hf : xs.mapM f = some ys)
    (hmono : ∀ x z, x ∈ xs → f x = some z → g x = some z) :
    xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil =>
      simp_all
  | cons x xs ih =>
      simp only [List.mapM_cons] at hf ⊢
      cases hfx : f x with
      | none => simp [hfx] at hf
      | some z =>
          cases htail : xs.mapM f with
          | none => simp [hfx, htail] at hf
          | some tail =>
              have hys : z :: tail = ys := by
                simpa [hfx, htail] using hf
              have hgx : g x = some z :=
                hmono x z (by simp) hfx
              have hgtail : xs.mapM g = some tail :=
                ih tail htail (by
                  intro y value hy hvalue
                  exact hmono y value (by simp [hy]) hvalue)
              simp [hgx, hgtail, hys]




private theorem one_lt_pow_two {n : Nat} [NeZero n] : 1 < 2 ^ n := by
  cases n with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ n => simp

private theorem bitVec_one_toNat {n : Nat} [NeZero n] :
    (1 : BitVec n).toNat = 1 := by
  change (BitVec.ofNat n 1).toNat = 1
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt one_lt_pow_two

/-! This theorem connects the bounded production recognizer to the
    value-recursive BitVec specification. It isolates the finite-fuel
    implementation detail before relating either representation to HOL's
    implicit finite-index word carrier. -/
private theorem crepDest2ExpFuel_eq_bitVecSpec {n : Nat} [NeZero n]
    (fuel start : Nat) (word : RiscV.Word n)
    (hbound : word.toNat < 2 ^ fuel) :
    crepDest2ExpFuel fuel start word = crepDest2ExpBitVecSpec start word := by
  induction fuel generalizing start word with
  | zero =>
      have hzero : word.toNat = 0 := by simpa using hbound
      have hword : word = 0 := BitVec.eq_of_toNat_eq (by simpa using hzero)
      rw [crepDest2ExpFuel, crepDest2ExpBitVecSpec, hword]
      simp
  | succ fuel ih =>
      rw [crepDest2ExpFuel, crepDest2ExpBitVecSpec]
      have hshift :
          ShiftRight.shiftRight word (1 : RiscV.Word n) =
            BitVec.ushiftRight word 1 := by
        change BitVec.ushiftRight word
          (1 : RiscV.Word n).toNat = BitVec.ushiftRight word 1
        rw [bitVec_one_toNat]
      have hshiftBound : (BitVec.ushiftRight word 1).toNat < 2 ^ fuel := by
        rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow]
        have hbound' : word.toNat < 2 * 2 ^ fuel := by
          calc
            word.toNat < 2 ^ (fuel + 1) := hbound
            _ = 2 ^ fuel * 2 := by rw [Nat.pow_succ]
            _ = 2 * 2 ^ fuel := by omega
        omega
      by_cases hzero : word = 0
      · have hzeroB : (word == 0) = true := by
          cases hb : (word == 0) <;> simp_all
        simp only [hzeroB, if_true]
      · by_cases hone : word = 1
        · change word ≠ (0 : BitVec n) at hzero
          change word = (1 : BitVec n) at hone
          have hzeroB : (word == 0) = false := by
            cases hb : (word == 0) <;> simp_all
          have honeB : (word == 1) = true := by
            cases hb : (word == 1) <;> simp_all
          simp only [hzeroB, honeB, if_true]
        · by_cases hlow : AndOp.and word 1 = 0
          · change word ≠ (0 : BitVec n) at hzero
            change word ≠ (1 : BitVec n) at hone
            change AndOp.and word (1 : BitVec n) = (0 : BitVec n) at hlow
            have hzeroB : (word == 0) = false := by
              cases hb : (word == 0) <;> simp_all
            have honeB : (word == 1) = false := by
              cases hb : (word == 1) <;> simp_all
            simp only [hzeroB, honeB, hlow]
            rw [hshift]
            exact ih (start + 1) (BitVec.ushiftRight word 1) hshiftBound
          · change word ≠ (0 : BitVec n) at hzero
            change word ≠ (1 : BitVec n) at hone
            have hzeroB : (word == 0) = false := by
              cases hb : (word == 0) <;> simp_all
            have honeB : (word == 1) = false := by
              cases hb : (word == 1) <;> simp_all
            have hoddB : (AndOp.and word 1 != 0) = true := by
              cases hb : (AndOp.and word 1 != 0) <;> simp_all
            simp only [hzeroB, honeB, hoddB, if_true]

theorem crepDest2Exp_eq_bitVecSpec {n : Nat} [NeZero n]
    (start : Nat) (word : RiscV.Word n) :
    crepDest2Exp start word = crepDest2ExpBitVecSpec start word := by
  change crepDest2ExpFuel (n + 1) start word = _
  apply crepDest2ExpFuel_eq_bitVecSpec
  exact Nat.lt_trans word.isLt
    (Nat.pow_lt_pow_right (by decide) (by omega))

/-- Flapjack implementation correspondence between the Boolean-test recursive
specification and the reviewed HOL recursion. BitVec equality tests are lawful;
well-founded induction covers every input value, including zero and odd words.
No standalone HOL declaration is claimed for this factoring equality. -/
theorem crepDest2ExpBitVecSpec_eq_HOL {width : Nat} [NeZero width]
    (start : Nat) (word : BitVec width) :
    crepDest2ExpBitVecSpec start word = crepDest2ExpHOL start word := by
  induction word using (measure (fun w : BitVec width => w.toNat)).wf.induction generalizing start with
  | h word ih =>
    rw [crepDest2ExpBitVecSpec, crepDest2ExpHOL]
    by_cases hz : word = BitVec.ofNat width 0
    · simp [hz]
    · by_cases ho : word = BitVec.ofNat width 1
      · simp [ho]
      · by_cases hb : word &&& BitVec.ofNat width 1 = BitVec.ofNat width 0
        · have hnat : word.toNat ≠ 0 := by
            intro hzero
            exact hz (BitVec.eq_of_toNat_eq (by simpa using hzero))
          have hlt : (BitVec.ushiftRight word 1).toNat < word.toNat := by
            rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
            exact Nat.div_lt_self (Nat.pos_of_ne_zero hnat) (by decide)
          simpa [hz, ho, hb, AndOp.and] using ih (BitVec.ushiftRight word 1) hlt (start + 1)
        · simp [hz, ho, hb, AndOp.and]

/-- Unconditional correspondence of the actual width-bounded executable
recognizer with the reviewed HOL definition, for every positive word width,
starting exponent and input. This is a Flapjack implementation theorem, not
an additional HOL port. -/
theorem crepDest2Exp_eq_HOL {width : Nat} [NeZero width]
    (start : Nat) (word : BitVec width) :
    crepDest2Exp start word = crepDest2ExpHOL start word := by
  rw [crepDest2Exp_eq_bitVecSpec, crepDest2ExpBitVecSpec_eq_HOL]


/-- Update each code entry using its function name and previous body. -/
def crepArithHolMapCode {n : Nat} {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ) :
    CrepHolState (RiscV.Word n) σ :=
  { state with code := fun name =>
      (state.code name).map (fun entry => f (name, entry)) }

/-- Apply the Crep arithmetic simplifier to the body stored at every function
    name, preserving the declaration's parameter list. This is the Lean
    function-map form of the `FMAP_MAP2` code transformation used by the local
    `lookup_code` lemma in `crep_arithProofScript.sml`. -/
def crepArithSimpCodeMap {α : Type} [BEq α] [OfNat α 0] [OfNat α 1]
    [Mul α] [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (fromNat : Nat → α)
    (code : FunName → Option (List Nat × CrepProg α)) :
    FunName → Option (List Nat × CrepProg α) :=
  fun name => (code name).map fun (parameters, body) =>
    (parameters, crepSimpProg fromNat body)



end Flapjack
