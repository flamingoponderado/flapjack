import Flapjack.Pancake.WordLang.MaxVarExp

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack induction infrastructure: a larger numeric bound also bounds
every register. The list motive follows the actual mutually recursive traversal. -/
private theorem everyVarExpBound {width : Nat} [NeZero width]
    (expression : WordLangExpHOL (BitVec width)) :
    ∀ bound, maxVarExpHOL expression ≤ bound →
      everyVarExpHOL (fun x => decide (x ≤ bound)) expression = true := by
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) => ∀ b,
      maxVarExpHOL e ≤ b → everyVarExpHOL (fun x => decide (x ≤ b)) e = true)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) => ∀ b,
      maxList (es.map maxVarExpHOL) ≤ b →
      everyVarExpsHOL (fun x => decide (x ≤ b)) es = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro value; simp [everyVarExpHOL]
  · intro name; simp [everyVarExpHOL, maxVarExpHOL]
  · intro store; simp [everyVarExpHOL]
  · intro address ih; simpa [everyVarExpHOL, maxVarExpHOL] using ih
  · intro operator arguments ih; simpa [everyVarExpHOL, maxVarExpHOL] using ih
  · intro operator left right ihLeft ihRight bound h
    simp only [maxVarExpHOL, Nat.max_le] at h
    simp [everyVarExpHOL, ihLeft bound h.1, ihRight bound h.2]
  · simp [everyVarExpsHOL]
  · intro head tail ihHead ihTail bound h
    simp only [List.map_cons, maxList, Nat.max_le] at h
    simp [everyVarExpsHOL, ihHead bound h.1, ihTail bound h.2]

/-- Every register occurring in an expression is bounded by the literal
expression maximum, including nested and empty operator argument lists. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "max_var_exp_max" (words_as_type_indexed_bitvec)]
theorem maxVarExpMax {width : Nat} [NeZero width]
    (expression : WordLangExpHOL (BitVec width)) :
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL expression)) expression = true :=
  everyVarExpBound expression _ (Nat.le_refl _)

end Flapjack.Compiler.Backend.WordAlloc
