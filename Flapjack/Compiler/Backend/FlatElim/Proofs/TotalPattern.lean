import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateSpecialization

/-! Total-pattern properties used by the pure-declaration simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

mutual
/-- A total pattern cannot return no-match. This Flapjack helper is proved
mutually with the corresponding list property. -/
theorem totalPat_notNoMatch {C F : Type} (state : FlatSem.State C F) (pattern : FlatLang.Pat)
    (value : FlatSem.Value) (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value))
    (total : totalPat pattern = true) : FlatSem.pmatch state pattern value bindings ≠ .noMatch := by
  cases pattern with
  | pany => simp [FlatSem.pmatch]
  | pvar name => simp [FlatSem.pmatch]
  | plit literal => simp [totalPat] at total
  | pref pattern => simp [totalPat] at total
  | pas pattern name =>
    simpa [FlatSem.pmatch] using totalPat_notNoMatch state pattern value ((name, value) :: bindings) (by simpa [totalPat] using total)
  | pcon stamp patterns =>
    cases stamp with
    | some stamp => simp [totalPat] at total
    | none =>
      have patternsTotal : totalPatList patterns = true := by simpa [totalPat] using total
      cases value <;> simp only [FlatSem.pmatch] <;> try simp
      case conv actual values =>
        cases actual with
        | some stamp => simp [← FlatSem.pmatchStampsOk_iff, FlatSem.pmatchStampsOk]
        | none =>
          by_cases sameLength : patterns.length = values.length
          · simpa [sameLength, ← FlatSem.pmatchStampsOk_iff, FlatSem.pmatchStampsOk] using
              totalPatList_notNoMatch state patterns values bindings sameLength patternsTotal
          · simp [sameLength, ← FlatSem.pmatchStampsOk_iff, FlatSem.pmatchStampsOk]
termination_by sizeOf pattern

/-- A total pattern list of the correct length cannot return no-match. This
Flapjack helper is proved mutually with the individual-pattern property. -/
theorem totalPatList_notNoMatch {C F : Type} (state : FlatSem.State C F) (patterns : List FlatLang.Pat)
    (values : List FlatSem.Value) (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value))
    (sameLength : patterns.length = values.length) (total : totalPatList patterns = true) :
    FlatSem.pmatchList state patterns values bindings ≠ .noMatch := by
  cases patterns with
  | nil =>
    cases values <;> simp_all [FlatSem.pmatchList]
  | cons pattern rest =>
    cases values with
    | nil => simp at sameLength
    | cons value values =>
      simp [totalPatList] at total
      simp only [List.length_cons, Nat.succ.injEq] at sameLength
      cases head : FlatSem.pmatch state pattern value bindings with
      | typeError => simp [FlatSem.pmatchList, head]
      | noMatch => exact (totalPat_notNoMatch state pattern value bindings total.1 head).elim
      | «match» next =>
        simpa [FlatSem.pmatchList, head] using totalPatList_notNoMatch state rest values next sameLength total.2
termination_by sizeOf patterns
end

/-- Total patterns cannot produce a no-match result, including in lists of
equal length. The evaluator and carriers remain pending HOL review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "total_pat_IMP"]
theorem totalPat_imp {C F : Type} :
    (∀ (state : FlatSem.State C F) (pattern : FlatLang.Pat) (value : FlatSem.Value)
      (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) (result : MatchResult (List (Flapjack.AstHOL.VarN × FlatSem.Value))),
      FlatSem.pmatch state pattern value bindings = result → totalPat pattern = true → result ≠ .noMatch) ∧
    (∀ (state : FlatSem.State C F) (patterns : List FlatLang.Pat) (values : List FlatSem.Value)
      (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) (result : MatchResult (List (Flapjack.AstHOL.VarN × FlatSem.Value))),
      patterns.length = values.length → FlatSem.pmatchList state patterns values bindings = result →
      totalPatList patterns = true → result ≠ .noMatch) := by
  constructor
  · intro state pattern value bindings result matched total
    rw [← matched]
    exact totalPat_notNoMatch state pattern value bindings total
  · intro state patterns values bindings result sameLength matched total
    rw [← matched]
    exact totalPatList_notNoMatch state patterns values bindings sameLength total

/-- A row list containing a total pattern cannot produce no-match. The
evaluator and carriers remain pending HOL review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "EXISTS_total_pat"]
theorem exists_totalPat {C F E : Type} (rows : List (FlatLang.Pat × E))
    (state : FlatSem.State C F) (value : FlatSem.Value) (total : rows.any (fun row => totalPat row.1) = true) :
    FlatSem.pmatchRows rows state value ≠ .noMatch := by
  induction rows with
  | nil => simp at total
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    simp at total
    cases head : FlatSem.pmatch state pattern value [] with
    | typeError => simp [FlatSem.pmatchRows, head]
    | noMatch =>
      have tailTotal : rest.any (fun row => totalPat row.1) = true := by
        rcases total with headTotal | tailTotal
        · exact (totalPat_notNoMatch state pattern value [] headTotal head).elim
        · simpa using tailTotal
      simpa [FlatSem.pmatchRows, head] using ih tailTotal
    | «match» bindings =>
      cases tail : FlatSem.pmatchRows rest state value <;> simp [FlatSem.pmatchRows, head, tail]

end Flapjack.Compiler.Backend.FlatElim
