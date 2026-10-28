import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties

/-! Global-write metadata used by the pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.FlatProps

/-- The operator global-write flag is set exactly when its initialization
bag is nonempty. The expression carriers remain pending HOL review. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "op_sets_globals_gbag"]
theorem opSetsGlobals_gbag (op : FlatLang.Op) :
    opSetsGlobals op = true ↔ opGlobalBag op ≠ emptyGlobalBag := by
  cases op <;> simp [opSetsGlobals, opGlobalBag]
  case globalVarInit index =>
    intro same
    have atIndex := congrFun same index
    simp [emptyGlobalBag] at atIndex

/-- A union has a nonempty bag exactly when one input is nonempty. -/
theorem unionGlobalBag_ne_empty (left right : GlobalBag) :
    unionGlobalBag left right ≠ emptyGlobalBag ↔ left ≠ emptyGlobalBag ∨ right ≠ emptyGlobalBag := by
  classical
  by_cases h : left = emptyGlobalBag <;> simp [unionGlobalBag_eq_empty, h]

mutual
/-- The expression compiler's global-write flag agrees with the source
expression's global bag. This Flapjack helper is proved mutually with its
list, row, and recursive-function traversals. -/
theorem compileExp_globalFlag (cfg : Config) (expression : FlatLang.Exp) :
    (compileExp cfg expression).2.1 = true ↔ setGlobals expression ≠ emptyGlobalBag := by
  cases expression with
  | lit tra literal => simp [compileExp, setGlobals]
  | varLocal tra name => simp [compileExp, setGlobals]
  | raise tra body =>
    have ih := compileExp_globalFlag cfg body
    cases h : compileExp cfg body with
    | mk i tail =>
      obtain ⟨flag, output⟩ := tail
      simpa [compileExp, setGlobals, h] using ih
  | fn name arg body =>
    have ih := compileExp_globalFlag cfg body
    cases h : compileExp cfg body with
    | mk i tail =>
      obtain ⟨flag, output⟩ := tail
      simpa [compileExp, setGlobals, h] using ih
  | con tra constructor args =>
    have ih := compileExps_globalFlag cfg args
    cases h : compileExps cfg args with
    | mk i tail =>
      obtain ⟨flag, output⟩ := tail
      simpa [compileExp, setGlobals, h] using ih
  | app tra op args =>
    have ih := compileExps_globalFlag cfg args
    have opIH := opSetsGlobals_gbag op
    cases h : compileExps cfg args with
    | mk i tail =>
      obtain ⟨flag, output⟩ := tail
      simp [compileExp, setGlobals, h, unionGlobalBag_ne_empty] at ih ⊢
      simp [ih, opIH]
  | let_ tra name first body =>
    have ihFirst := compileExp_globalFlag cfg first
    have ihBody := compileExp_globalFlag cfg body
    cases hFirst : compileExp cfg first with
    | mk i tail =>
      obtain ⟨firstFlag, firstOutput⟩ := tail
      cases hBody : compileExp cfg body with
      | mk j tail =>
        obtain ⟨bodyFlag, bodyOutput⟩ := tail
        simp [hFirst] at ihFirst
        simp [hBody] at ihBody
        simp [compileExp, setGlobals, hFirst, hBody, unionGlobalBag_ne_empty, ihFirst, ihBody]
  | if_ tra cond yes no =>
    have ihCond := compileExp_globalFlag cfg cond
    have ihYes := compileExp_globalFlag cfg yes
    have ihNo := compileExp_globalFlag cfg no
    cases hCond : compileExp cfg cond with
    | mk i tail =>
      obtain ⟨condFlag, condOutput⟩ := tail
      cases hYes : compileExp cfg yes with
      | mk j tail =>
        obtain ⟨yesFlag, yesOutput⟩ := tail
        cases hNo : compileExp cfg no with
        | mk k tail =>
          obtain ⟨noFlag, noOutput⟩ := tail
          simp [hCond] at ihCond
          simp [hYes] at ihYes
          simp [hNo] at ihNo
          simp [compileExp, setGlobals, hCond, hYes, hNo, unionGlobalBag_ne_empty, ihCond, ihYes, ihNo]
  | handle tra body rows =>
    have ihBody := compileExp_globalFlag cfg body
    have ihRows := compileMatch_globalFlag cfg rows
    cases hBody : compileExp cfg body with
    | mk i tail =>
      obtain ⟨bodyFlag, bodyOutput⟩ := tail
      cases hRows : compileMatch cfg rows with
      | mk j tail =>
        obtain ⟨rowsFlag, rowsOutput⟩ := tail
        simp [hBody] at ihBody
        simp [hRows] at ihRows
        simp [compileExp, setGlobals, hBody, hRows, unionGlobalBag_ne_empty, ihBody, ihRows]
  | mat tra body rows =>
    have ihBody := compileExp_globalFlag cfg body
    have ihRows := compileMatch_globalFlag cfg rows
    cases hBody : compileExp cfg body with
    | mk i tail =>
      obtain ⟨bodyFlag, bodyOutput⟩ := tail
      cases hRows : compileMatch cfg rows with
      | mk j tail =>
        obtain ⟨rowsFlag, rowsOutput⟩ := tail
        simp [hBody] at ihBody
        simp [hRows] at ihRows
        simp [compileExp, setGlobals, hBody, hRows, unionGlobalBag_ne_empty, ihBody, ihRows]
  | letrec name funs body =>
    have ihBody := compileExp_globalFlag cfg body
    have ihFuns := compileFuns_globalFlag cfg funs
    cases hFuns : compileFuns cfg funs with
    | mk j tail =>
      obtain ⟨funsFlag, funsOutput⟩ := tail
      cases hBody : compileExp cfg body with
      | mk i tail =>
        obtain ⟨bodyFlag, bodyOutput⟩ := tail
        simp [hBody] at ihBody
        simp [hFuns] at ihFuns
        simp [compileExp, setGlobals, hBody, hFuns, unionGlobalBag_ne_empty, ihBody, ihFuns, or_comm]
termination_by sizeOf expression

/-- Flapjack list component of the global-write flag induction. -/
theorem compileExps_globalFlag (cfg : Config) (expressions : List FlatLang.Exp) :
    (compileExps cfg expressions).2.1 = true ↔ elistGlobals expressions ≠ emptyGlobalBag := by
  cases expressions with
  | nil => simp [compileExps, elistGlobals]
  | cons expression rest =>
    have ihHead := compileExp_globalFlag cfg expression
    have ihTail := compileExps_globalFlag cfg rest
    cases hHead : compileExp cfg expression with
    | mk i tail =>
      obtain ⟨headFlag, headOutput⟩ := tail
      cases hTail : compileExps cfg rest with
      | mk j tail =>
        obtain ⟨tailFlag, tailOutput⟩ := tail
        simp [hHead] at ihHead
        simp [hTail] at ihTail
        simp [compileExps, elistGlobals, hHead, hTail, unionGlobalBag_ne_empty, ihHead, ihTail]
termination_by sizeOf expressions

/-- Flapjack row component of the global-write flag induction. -/
theorem compileMatch_globalFlag (cfg : Config) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    (compileMatch cfg rows).2.1 = true ↔ rowGlobals rows ≠ emptyGlobalBag := by
  cases rows with
  | nil => simp [compileMatch, rowGlobals]
  | cons row rest =>
    obtain ⟨pattern, body⟩ := row
    have ihHead := compileExp_globalFlag cfg body
    have ihTail := compileMatch_globalFlag cfg rest
    cases hHead : compileExp cfg body with
    | mk i tail =>
      obtain ⟨headFlag, headOutput⟩ := tail
      cases hTail : compileMatch cfg rest with
      | mk j tail =>
        obtain ⟨tailFlag, tailOutput⟩ := tail
        simp [hHead] at ihHead
        simp [hTail] at ihTail
        simp [compileMatch, rowGlobals, hHead, hTail, unionGlobalBag_ne_empty, ihHead, ihTail]
termination_by sizeOf rows

/-- Flapjack recursive-function component of the global-write flag induction. -/
theorem compileFuns_globalFlag (cfg : Config) (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    (compileFuns cfg funs).2.1 = true ↔ funGlobals funs ≠ emptyGlobalBag := by
  cases funs with
  | nil => simp [compileFuns, funGlobals]
  | cons entry rest =>
    obtain ⟨name, arg, body⟩ := entry
    have ihHead := compileExp_globalFlag cfg body
    have ihTail := compileFuns_globalFlag cfg rest
    cases hHead : compileExp cfg body with
    | mk i tail =>
      obtain ⟨headFlag, headOutput⟩ := tail
      cases hTail : compileFuns cfg rest with
      | mk j tail =>
        obtain ⟨tailFlag, tailOutput⟩ := tail
        simp [hHead] at ihHead
        simp [hTail] at ihTail
        simp [compileFuns, funGlobals, hHead, hTail, unionGlobalBag_ne_empty, ihHead, ihTail]
termination_by sizeOf funs
end

/-- The row traversal is the original list traversal over row bodies. -/
theorem rowGlobals_eq_elistGlobals (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    rowGlobals rows = elistGlobals (rows.map Prod.snd) := by
  induction rows with
  | nil => simp [rowGlobals, elistGlobals]
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    simp [rowGlobals, elistGlobals, ih]

/-- The compiler's global-write metadata records exactly whether each
source expression, list, or pattern-row list initializes a global. The
compiler and expression carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_exp_set_globals_FST_SND"]
theorem compileExp_setGlobals_flag :
    (∀ cfg expression, (compileExp cfg expression).2.1 = true ↔ setGlobals expression ≠ emptyGlobalBag) ∧
    (∀ cfg expressions, (compileExps cfg expressions).2.1 = true ↔ elistGlobals expressions ≠ emptyGlobalBag) ∧
    (∀ cfg rows, (compileMatch cfg rows).2.1 = true ↔ elistGlobals (rows.map Prod.snd) ≠ emptyGlobalBag) := by
  refine ⟨compileExp_globalFlag, compileExps_globalFlag, ?_⟩
  intro cfg rows
  simpa [rowGlobals_eq_elistGlobals] using compileMatch_globalFlag cfg rows

/-- The tuple form of the pattern compiler's global-write metadata theorem.
The compiler and expression carriers remain pending HOL review. -/
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
