module

public import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
public import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties

@[expose] public section

/-! Global-write metadata used by the pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.FlatProps

/-- The operator global-write flag is set exactly when its initialization
bag is nonempty. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "op_sets_globals_gbag"]
theorem opSetsGlobals_gbag (op : FlatLang.Op) :
    opSetsGlobals op = true ↔ opGlobalBag op ≠ emptyGlobalBag := by
  cases op <;> simp [opSetsGlobals, opGlobalBag]
  case globalVarInit index =>
    intro same
    have atIndex := congrFun same index
    simp [emptyGlobalBag, Flapjack.emptyBag] at atIndex

/-- A union has a nonempty bag exactly when one input is nonempty. -/
theorem unionGlobalBag_ne_empty (left right : GlobalBag) :
    unionGlobalBag left right ≠ emptyGlobalBag ↔ left ≠ emptyGlobalBag ∨ right ≠ emptyGlobalBag := by
  classical
  by_cases h : left = emptyGlobalBag <;> simp [unionGlobalBag_eq_empty, h]

/-- The compiler's global-write metadata records exactly whether each
source expression, list, or pattern-row list initializes a global. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_set_globals_FST_SND"]
theorem compileExp_setGlobals_flag :
    (∀ cfg expression, (compileExp cfg expression).2.1 = true ↔ setGlobals expression ≠ emptyGlobalBag) ∧
    (∀ cfg expressions, (compileExps cfg expressions).2.1 = true ↔ elistGlobals expressions ≠ emptyGlobalBag) ∧
    (∀ cfg rows, (compileMatch cfg rows).2.1 = true ↔ elistGlobals (rows.map Prod.snd) ≠ emptyGlobalBag) := by
  have all (cfg : Config) :
      (∀ e, (compileExp cfg e).2.1 = true ↔ setGlobals e ≠ emptyGlobalBag) ∧
      (∀ fs, (compileFuns cfg fs).2.1 = true ↔ funGlobals fs ≠ emptyGlobalBag) ∧
      (∀ es, (compileExps cfg es).2.1 = true ↔ elistGlobals es ≠ emptyGlobalBag) ∧
      (∀ ps, (compileMatch cfg ps).2.1 = true ↔ rowGlobals ps ≠ emptyGlobalBag) := by
    apply compileExp.mutual_induct cfg
    all_goals intros
    all_goals simp_all [compileExp, compileFuns, compileExps, compileMatch, setGlobals,
      funGlobals, elistGlobals, rowGlobals, unionGlobalBag_ne_empty, opSetsGlobals_gbag, or_comm]
  refine ⟨fun cfg => (all cfg).1, fun cfg => (all cfg).2.2.1, ?_⟩
  intro cfg rows
  simpa [rowGlobals_eq_elistGlobals] using (all cfg).2.2.2 rows

/-- The tuple form of the pattern compiler's global-write metadata theorem. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_set_globals_tup"]
theorem compileExp_setGlobals_tuple :
    (∀ cfg expression index flag output, compileExp cfg expression = (index, flag, output) →
      (flag = true ↔ setGlobals expression ≠ emptyGlobalBag)) ∧
    (∀ cfg expressions index flag output, compileExps cfg expressions = (index, flag, output) →
      (flag = true ↔ elistGlobals expressions ≠ emptyGlobalBag)) ∧
    (∀ cfg rows index flag output, compileMatch cfg rows = (index, flag, output) →
      (flag = true ↔ elistGlobals (rows.map Prod.snd) ≠ emptyGlobalBag)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cfg expression index flag output compiled
    simpa [compiled] using compileExp_setGlobals_flag.1 cfg expression
  · intro cfg expressions index flag output compiled
    simpa [compiled] using compileExp_setGlobals_flag.2.1 cfg expressions
  · intro cfg rows index flag output compiled
    simpa [compiled] using compileExp_setGlobals_flag.2.2 cfg rows

end Flapjack.Compiler.Backend.FlatPattern
