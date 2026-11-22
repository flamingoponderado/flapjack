module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Post
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Arith
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Headers
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax

@[expose] public section

/-! `AnyArith_thm`: side facts for assembling the proof (Flapjack-only helpers
following the HOL proof). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Misc.Multiword

/-- The stack bound survives the bignum call (HOL: the `evaluate_stack_max`
step of `AnyArith_thm`). -/
theorem stackMax_after {width : Nat} [NeZero width] {C F : Type}
    {t9 F2 : WordSemStateFiniteExact width C F} {ret : WordLocW width}
    {P : WordLangProgHOL (BitVec width)} {res : Option (WordSemResult width)}
    (h : BackendProps.optionLe (Option.map₂ (· + ·) (wordSemStackSize t9.stack) t9.localsSize)
      t9.stackMax)
    (hev : WordSemStateFiniteExact.evaluate P (bignumCallState t9 ret) = (res, F2)) :
    BackendProps.optionLe (Option.map₂ (· + ·) (wordSemStackSize t9.stack) (some 0)) F2.stackMax := by
  have sm := WordSemStateFiniteExact.evaluate_stack_max _ _ _ _ hev
  have al : sptToAList (.ls ret) = [(0, ret)] := by simp [sptToAList, sptFoldi]
  simp only [bignumCallState, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
    envToList_ln, WordSemStateFiniteExact.decClock, al] at sm
  cases hs : wordSemStackSize t9.stack <;> cases hl : t9.localsSize <;> cases hm : t9.stackMax <;>
    cases hss : sptLookup bignumLocation t9.stackSize <;> cases hF : F2.stackMax <;>
    simp_all [BackendProps.optionLe, wordSemStackSize, wordSemOptionMax, wordSemOptionAdd,
      wordSemStackSizeFrame, miscThe]
  all_goals omega

theorem intSuccDiv (x y : Nat) :
    ((x : Int) + 1) / ((y : Int) + 1) = (x : Int) / ((y : Int) + 1) +
      if (x + 1) % (y + 1) = 0 then 1 else 0 := by
  have h : (((x + 1) / (y + 1) : Nat) : Int) =
      ((x / (y + 1) : Nat) : Int) + if (x + 1) % (y + 1) = 0 then 1 else 0 := by
    rw [Nat.succ_div]
    by_cases d : (x + 1) % (y + 1) = 0 <;> simp [d, Nat.dvd_iff_mod_eq_zero]
  push_cast at h
  exact h

/-- HOL's integer division is floor division. -/
theorem holIntDiv_eq_fdiv (i j : Int) (hj : j ≠ 0) : holIntDiv i j = Int.fdiv i j := by
  rcases Int.eq_nat_or_neg i with ⟨a, rfl | rfl⟩ <;>
    rcases Int.eq_nat_or_neg j with ⟨b, rfl | rfl⟩
  all_goals have hb : 0 < b := by omega
  all_goals obtain ⟨b, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  · rw [holIntDiv_ofNat_ofNat a _ hb]; cases a <;> simp [Int.fdiv]
  all_goals first
    | rw [holIntDiv_ofNat_neg a _ hb] | rw [holIntDiv_neg_ofNat a _ hb] | rw [holIntDiv_neg_neg a _ hb]
  all_goals try rw [show (-(((b + 1 : Nat)) : Int)) = Int.negSucc b from rfl]
  all_goals try rw [show (((b + 1 : Nat)) : Int) = Int.ofNat (b + 1) from rfl]
  all_goals rcases a with _ | n
  all_goals try rw [show (-(((n + 1 : Nat)) : Int)) = Int.negSucc n from rfl]
  all_goals try rw [show (((n + 1 : Nat)) : Int) = Int.ofNat (n + 1) from rfl]
  all_goals (simp only [Int.fdiv, Int.negSucc_eq]; push_cast; simp [intSuccDiv] <;> split_ifs <;> omega)

theorem holIntMod_eq_fmod (i j : Int) (hj : j ≠ 0) : holIntMod i j = Int.fmod i j := by
  rw [holIntMod_spec _ _ hj, holIntDiv_eq_fdiv _ _ hj, Int.fmod_def, Int.mul_comm]

/-- The stub index selects the matching multiword operation (HOL: the
`int_op (get_iop op_index) i j = v` step of `AnyArith_thm`). -/
theorem intOp_getIop {op : Nat} {i j v : Int} (h : intOp op i j = some v) :
    mwIntOp (getIop op) i j = v ∧ (getIop op = .div ∨ getIop op = .mod → j ≠ 0) ∧
      getIop op ≠ .lt ∧ getIop op ≠ .eq ∧ getIop op ≠ .dec ∧
      (op = 0 ∨ op = 1 ∨ op = 4 ∨ op = 5 ∨ op = 6) := by
  unfold intOp at h
  by_cases h0 : op = 0
  · subst h0; simp at h; subst h; simp [getIop, mwIntOp]
  by_cases h1 : op = 1
  · subst h1; simp at h; subst h; simp [getIop, mwIntOp]
  by_cases h4 : op = 4
  · subst h4; simp at h; subst h; simp [getIop, mwIntOp]
  by_cases h5 : op = 5 ∧ j ≠ 0
  · obtain ⟨rfl, hj⟩ := h5; simp [hj] at h; subst h
    simp [getIop, mwIntOp, hj, holIntDiv_eq_fdiv _ _ hj]
  by_cases h6 : op = 6 ∧ j ≠ 0
  · obtain ⟨rfl, hj⟩ := h6; simp [hj] at h; subst h
    simp [getIop, mwIntOp, hj, holIntMod_eq_fmod _ _ hj]
  simp [h0, h1, h4, h5, h6] at h

/-- The operation word handed to the bignum code (HOL: `n2w (4 * op_index) >>> 2`). -/
theorem opWord {width : Nat} [NeZero width] (good : goodDimindex width) {op : Nat}
    (hop : op = 0 ∨ op = 1 ∨ op = 4 ∨ op = 5 ∨ op = 6) :
    BitVec.ofNat width (4 * op) >>> (BitVec.ofNat width 2).toNat = intOpRep (getIop op) := by
  rcases good with h | h <;> subst h <;> rcases hop with rfl | rfl | rfl | rfl | rfl <;>
    simp only [getIop, intOpRep] <;> decide

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
