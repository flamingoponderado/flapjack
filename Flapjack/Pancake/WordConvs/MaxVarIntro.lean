import Flapjack.Pancake.WordLang.MaxVar
import Flapjack.Pancake.WordLang.OccurrencesExact
import Aesop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.Max3

namespace Flapjack.WordConvs

/-- Flapjack induction infrastructure: a natural maximum selects one of its
arguments, so an arbitrary predicate holding on both holds on the maximum.
This is not a separate HOL declaration port. -/
private theorem predicateMax (P : Nat → Bool) (a b : Nat)
    (ha : P a = true) (hb : P b = true) : P (max a b) = true := by
  rcases Nat.le_total a b with h | h
  · simpa [Nat.max_eq_right h] using hb
  · simpa [Nat.max_eq_left h] using ha

/-- Original generic expression maximum introduction. The zero premise covers
constant and lookup expressions and empty operator argument lists. The mutual
list motive follows the same expression traversal, without a numeric bound
or a restriction on the predicate. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "max_var_exp_IMP" (words_as_type_indexed_bitvec)]
theorem maxVarExpImp {width : Nat} [NeZero width]
    (P : Nat → Bool) (expression : WordLangExpHOL (BitVec width))
    (hyp : P 0 = true ∧ everyVarExpHOL P expression = true) :
    P (maxVarExpHOL expression) = true := by
  have result : ∀ e : WordLangExpHOL (BitVec width),
      P 0 = true → everyVarExpHOL P e = true → P (maxVarExpHOL e) = true := by
    refine WordLangExpHOL.rec
      (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
        P 0 = true → everyVarExpHOL P e = true → P (maxVarExpHOL e) = true)
      (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
        P 0 = true → everyVarExpsHOL P es = true →
          P (maxList (es.map maxVarExpHOL)) = true)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro value hzero _; simpa [maxVarExpHOL] using hzero
    · intro name _ h; simpa [maxVarExpHOL, everyVarExpHOL] using h
    · intro store hzero _; simpa [maxVarExpHOL] using hzero
    · intro address ih hzero h
      simpa only [maxVarExpHOL] using ih hzero (by simpa [everyVarExpHOL] using h)
    · intro operator arguments ih hzero h
      simpa only [maxVarExpHOL] using ih hzero (by simpa [everyVarExpHOL] using h)
    · intro operator left right ihLeft ihRight hzero h
      simp only [everyVarExpHOL, Bool.and_eq_true] at h
      simpa only [maxVarExpHOL] using predicateMax P _ _ (ihLeft hzero h.1) (ihRight hzero h.2)
    · intro hzero _; simpa [maxList] using hzero
    · intro head tail ihHead ihTail hzero h
      simp only [everyVarExpsHOL, Bool.and_eq_true] at h
      exact predicateMax P _ _ (ihHead hzero h.1) (ihTail hzero h.2)
  exact result expression hyp.1 hyp.2

/-- Flapjack induction infrastructure for the literal zero-based list maximum. -/
private theorem predicateMaxList (P : Nat → Bool) (values : List Nat)
    (hzero : P 0 = true) (h : values.all P = true) : P (maxList values) = true := by
  induction values with
  | nil => simpa [maxList] using hzero
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact predicateMax P _ _ h.1 (ih h.2)

/-- Flapjack induction infrastructure for exact instruction occurrences,
including dimension-dependent floating-point register transfers. No separate
HOL theorem is claimed: this is the Inst subproof of max_var_intro. -/
private theorem predicateMaxInst {width : Nat} [NeZero width]
    (P : Nat → Bool) (instruction : WordLangInst (BitVec width))
    (hzero : P 0 = true) (h : everyVarInstHOL P instruction = true) :
    P (maxVarInstHOL instruction) = true := by
  cases instruction with
  | skip => exact hzero
  | const r v => simpa [everyVarInstHOL, maxVarInstHOL] using h
  | arith operation =>
    cases operation with
    | binop op a b right | shift op a b right =>
      cases right <;>
        simp only [everyVarInstHOL, everyVarImmHOL, maxVarInstHOL,
          Flapjack.WordAlloc.max3Eq, Bool.and_eq_true] at h ⊢
      all_goals aesop (config := { enableSimp := false }) (add safe apply [predicateMax])
    | div a b c =>
      simp only [everyVarInstHOL, maxVarInstHOL, Flapjack.WordAlloc.max3Eq, Bool.and_eq_true] at h ⊢
      aesop (config := { enableSimp := false }) (add safe apply [predicateMax])
    | _ =>
      simp only [everyVarInstHOL, maxVarInstHOL, Bool.and_eq_true] at h ⊢
      aesop (config := { enableSimp := false }) (add safe apply [predicateMax])
  | mem operator r address =>
    cases operator <;> cases address <;>
      simp only [everyVarInstHOL, maxVarInstHOL, Bool.and_eq_true] at h ⊢
    all_goals aesop (config := { enableSimp := false }) (add safe apply [predicateMax])
  | fp operation =>
    cases operation <;> simp_all [everyVarInstHOL, maxVarInstHOL]
    all_goals split <;> simp_all
    all_goals exact predicateMax P _ _ h.1 h.2

/-- Flapjack induction infrastructure on the same two exact Spt key lists
used by the source cut-set occurrence predicate. -/
private theorem predicateMaxNames (P : Nat → Bool) (names : WordLangCutsetsHOL)
    (hzero : P 0 = true) (h : everyNameHOL P names = true) :
    P (cutsetsMaxHOL names) = true := by
  simp only [everyNameHOL, Bool.and_eq_true] at h
  exact predicateMax P _ _ (predicateMaxList P _ hzero h.1)
    (predicateMaxList P _ hzero h.2)

/-- Full original program maximum introduction, for any predicate P. Calls
traverse a handler only beneath SOME return, exactly as both source equations
specify; all operands, cut sets and recursive bodies retain the original scope. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "max_var_intro" (words_as_type_indexed_bitvec)]
theorem maxVarIntro {width : Nat} [NeZero width]
    (P : Nat → Bool) (program : WordLangProgHOL (BitVec width))
    (hyp : P 0 = true ∧ everyVarHOL P program = true) :
    P (maxVarHOL program) = true := by
  obtain ⟨hzero, h⟩ := hyp
  induction program using maxVarHOL.induct
  case case27 =>
    rename_i remaining
      excluded1 excluded2 excluded3 excluded4 excluded5 excluded6
      excluded7 excluded8 excluded9 excluded10 excluded11 excluded12
      excluded13 excluded14 excluded15 excluded16 excluded17 excluded18
      excluded19 excluded20 excluded21 excluded22 excluded23 excluded24
    cases remaining <;> try simpa only [maxVarHOL] using hzero
    all_goals exfalso
    all_goals solve_by_elim
  case case12 operator left right first second ihFirst ihSecond =>
    cases right <;>
      simp only [maxVarHOL, Flapjack.WordAlloc.max3Eq, everyVarHOL, everyVarImmHOL,
        Bool.and_eq_true] at h ⊢
    all_goals aesop (config := { enableSimp := false }) (add safe apply [predicateMax, ihFirst, ihSecond, True.intro])
  all_goals try
    rename_i ihFirst ihSecond
    have firstAt := ihFirst (by simp only [everyVarHOL, Bool.and_eq_true] at h; aesop)
    have secondAt := ihSecond (by simp only [everyVarHOL, Bool.and_eq_true] at h; aesop)
  all_goals try
    rename_i ih
    have bodyAt := ih (by simp only [everyVarHOL, Bool.and_eq_true] at h; aesop)
  all_goals simp only [maxVarHOL, Flapjack.WordAlloc.max3Eq, maxList_append,
    everyVarHOL, everyNameHOL, Bool.and_eq_true] at h ⊢
  all_goals aesop (config := { enableSimp := false }) (add safe apply [predicateMax, predicateMaxList, predicateMaxInst,
      predicateMaxNames, maxVarExpImp, True.intro])

end Flapjack.WordConvs
