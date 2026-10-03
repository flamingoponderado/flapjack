import Flapjack.Compiler.Backend.WordAlloc.ProductionClashTree
import Flapjack.Compiler.Backend.WordAlloc.GetPrefs
import Flapjack.RiscV.SpillCosts

namespace Flapjack.WordAlloc
open RiscV Compiler.Encoders.Asm

/-! Actual heuristic input producer. Untagged implementation correspondence:
getPrefs already carries its reviewed HOL reference. The real accepted program
encoder supplies recursive native children; accumulator and move order remain
arbitrary, including exception-before-return handler traversal. -/

theorem preferences_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (accumulator : List (Nat × Nat × Nat)) :
    (wordProgPrioritizedMoves program).map wordMoveToTriple ++ accumulator =
      getPrefs native accumulator := by
  cases program
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction <;> simp [wordLangProgToHOL, hi] at encoded
    subst native
    simp only [wordProgPrioritizedMoves, getPrefs, List.map_nil, List.nil_append]
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simpa only [wordProgPrioritizedMoves, getPrefs] using preferences_production body _ hb accumulator
  case loop names body exits =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simpa only [wordProgPrioritizedMoves, getPrefs] using preferences_production body _ hb accumulator
  case seq first second =>
    cases hf : wordLangProgToHOL first <;> cases hs : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, hf, hs] at encoded
    subst native
    simp only [wordProgPrioritizedMoves, List.map_append, List.append_assoc, getPrefs,
      ← preferences_production first _ hf, ← preferences_production second _ hs]
  case ite cmp register right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    simp only [wordProgPrioritizedMoves, List.map_append, List.append_assoc, getPrefs,
      ← preferences_production yes _ hy, ← preferences_production no _ hn]
  case call returns destination arguments handler =>
    cases hReturns : returns with
    | none =>
      cases hHandler : handler with
      | none =>
          simp [wordLangProgToHOL, hReturns, hHandler] at encoded
          subst native
          simp only [wordProgPrioritizedMoves, getPrefs, List.map_nil, List.nil_append]
      | some h =>
          rcases h with ⟨exception, body, l1, l2⟩
          cases hb : wordLangProgToHOL body <;>
            simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simp only [wordProgPrioritizedMoves, getPrefs, List.map_nil, List.nil_append]
    | some r =>
      rcases r with ⟨values, sets, body, l1, l2⟩
      cases hb : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, hReturns, hb] at encoded
      | some nb =>
        cases hHandler : handler with
        | none =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simpa only [wordProgPrioritizedMoves, getPrefs] using preferences_production body nb hb accumulator
        | some h =>
          rcases h with ⟨exception, handlerBody, h1, h2⟩
          cases hh : wordLangProgToHOL handlerBody <;>
            simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
          subst native
          simp only [wordProgPrioritizedMoves, List.map_append, List.append_assoc, getPrefs,
            ← preferences_production body nb hb, ← preferences_production handlerBody _ hh]
  all_goals simp only [wordLangProgToHOL, Option.some.injEq] at encoded
  all_goals subst native
  all_goals simp [wordProgPrioritizedMoves, getPrefs, List.map_map, wordMoveToTriple]
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hReturns]
    try rw [hHandler]
    try simp
    all_goals omega

/-- The actual canonicalizer consumes exactly the native preference producer,
without a second normalization or ordering implementation. -/
theorem canonicalPreferences_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    (wordCanonicalizeMoves (wordProgPrioritizedMoves program)).map
      (fun move => (move.count, move.maxPriority, (move.left, move.right))) =
      canonizeMoves (getPrefs native []) := by
  rw [wordCanonicalizeMoves_eq_canonizeMoves]
  have same := preferences_production program native encoded []
  simp only [List.append_nil] at same
  rw [same]

end Flapjack.WordAlloc
