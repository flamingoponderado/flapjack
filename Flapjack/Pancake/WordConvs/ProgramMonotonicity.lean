import Flapjack.Pancake.WordConvs.ExpressionMonotonicity
import Flapjack.Pancake.WordConvs.EveryVarInstMono
import Flapjack.Pancake.WordConvs.NameMonotonicity
import Aesop

namespace Flapjack

/-- Pointwise implication preserves the complete native program occurrence
predicate, including its return-dependent traversal of Call handlers. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "every_var_mono" (words_as_type_indexed_bitvec)]
theorem everyVarMono {width : Nat} [NeZero width] (P : Nat → Bool)
    (program : WordLangProgHOL (BitVec width)) (Q : Nat → Bool) :
    ((∀ x, P x = true → Q x = true) ∧ everyVarHOL P program = true) →
      everyVarHOL Q program = true := by
  rintro ⟨hmono, hP⟩
  have listMono (values : List Nat) : values.all P = true → values.all Q = true := by
    simp only [List.all_eq_true]
    exact fun h x hx => hmono x (h x hx)
  have expMono (expression : WordLangExpHOL (BitVec width)) :=
    fun h => everyVarExpMono P expression Q ⟨hmono, h⟩
  have instMono (instruction : WordLangInst (BitVec width)) :=
    fun h => everyVarInstMono P instruction Q ⟨hmono, h⟩
  have nameMono (names : WordLangCutsetsHOL) :=
    fun h => everyNameMono P names Q ⟨hmono, h⟩
  have immMono (immediate : WordRegImm (BitVec width)) :
      everyVarImmHOL P immediate = true → everyVarImmHOL Q immediate = true := by
    cases immediate <;> simp_all [everyVarImmHOL]
  revert hP
  induction program using everyVarHOL.induct
  case case13 returns target arguments handler ih =>
    cases returns with
    | none => simpa [everyVarHOL] using listMono arguments
    | some returns =>
      rcases returns with ⟨values, names, body, label, entry⟩
      cases handler with
      | none =>
        simp_all only [everyVarHOL, Bool.and_eq_true]
        aesop
      | some handler =>
        rcases handler with ⟨value, body, label, entry⟩
        simp_all only [everyVarHOL, Bool.and_eq_true]
        aesop
  all_goals
    try simp_all only [everyVarHOL, Bool.and_eq_true]
    aesop

end Flapjack
