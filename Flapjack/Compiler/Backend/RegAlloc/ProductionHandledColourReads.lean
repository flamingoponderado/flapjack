import Flapjack.Compiler.Backend.RegAlloc.ProductionStempReads

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem tagRead_outside {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (node : Nat)
    (bound : ¬node < native.node_tag.length) : production.nodeTag.get node = none := by
  have size := related.tags.2.1
  simp only [List.length_map] at size
  simp [CakeNodeMap.get, size, bound, related.tags.1, cakeMapLookup]
  rfl

private def queryOutcome (result : Option (Option Nat)) : Exc (Option Nat) StateException :=
  match result with
  | none => .failure .Subscript
  | some value => .success value

private theorem firstMatchOutcome (colours nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    ∃ outcome : Option (Option Nat),
      firstMatchCol colours nodes native = (queryOutcome outcome, native) ∧
      outcome.join = cakeFirstMatchCol production colours nodes := by
  induction nodes with
  | nil => exact ⟨some none, rfl, rfl⟩
  | cons node rest ih =>
    obtain ⟨outcome, tailRun, decoded⟩ := ih
    by_cases bound : node < native.node_tag.length
    · have read := related.tag_read node bound
      cases tag : native.node_tag[node] with
      | Fixed colour =>
        by_cases member : colour ∈ colours
        · refine ⟨some (some colour), ?_, ?_⟩
          · simp [firstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
              bound, holEl_eq_getElem node native.node_tag bound, tag, member, ret, queryOutcome]
          · simp [cakeFirstMatchCol, read, tag, Tag.toProduction, member]
        · refine ⟨outcome, ?_, ?_⟩
          · simp [firstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
              bound, holEl_eq_getElem node native.node_tag bound, tag, member, tailRun]
          · simpa [cakeFirstMatchCol, read, tag, Tag.toProduction, member] using decoded
      | Atemp | Stemp =>
        refine ⟨outcome, ?_, ?_⟩
        · simp [firstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
            bound, holEl_eq_getElem node native.node_tag bound, tag, tailRun]
        · simpa [cakeFirstMatchCol, read, tag, Tag.toProduction] using decoded
    · refine ⟨none, ?_, ?_⟩
      · simp [firstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, bound, queryOutcome]
      · simp [cakeFirstMatchCol, tagRead_outside related node bound]

/-- The positive preference's handled first-match query agrees with the
executed scan for arbitrary partner lists, including an invalid partner
before a later matching colour. Missing reads stop at the original Subscript
handler; no partner-bound or desired-result premise is introduced. This is
actual/native infrastructure, not a new HOL first_match_col port. -/
theorem handledFirstMatchCol_production (colours nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    handleSubscript (firstMatchCol colours nodes) (ret none) native =
      (.success (cakeFirstMatchCol production colours nodes), native) := by
  obtain ⟨outcome, run, decoded⟩ := firstMatchOutcome colours nodes related
  rw [← decoded]
  cases outcome <;> simp [handleSubscript, run, queryOutcome, ret]

private theorem negFirstMatchOutcome (limit : Nat) (bads nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    ∃ outcome : Option (Option Nat),
      negFirstMatchCol limit bads nodes native = (queryOutcome outcome, native) ∧
      outcome.join = cakeNegFirstMatchCol production limit bads nodes := by
  induction nodes with
  | nil => exact ⟨some none, rfl, rfl⟩
  | cons node rest ih =>
    obtain ⟨outcome, tailRun, decoded⟩ := ih
    by_cases bound : node < native.node_tag.length
    · have read := related.tag_read node bound
      cases tag : native.node_tag[node] with
      | Fixed colour =>
        by_cases rejected : colour ∈ bads ∨ colour < limit
        · refine ⟨outcome, ?_, ?_⟩
          · simp [negFirstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
              bound, holEl_eq_getElem node native.node_tag bound, tag, rejected, tailRun]
          · simpa [cakeNegFirstMatchCol, read, tag, Tag.toProduction, rejected] using decoded
        · refine ⟨some (some colour), ?_, ?_⟩
          · simp [negFirstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
              bound, holEl_eq_getElem node native.node_tag bound, tag, rejected, ret, queryOutcome]
          · simp [cakeNegFirstMatchCol, read, tag, Tag.toProduction, rejected]
      | Atemp | Stemp =>
        refine ⟨outcome, ?_, ?_⟩
        · simp [negFirstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
            bound, holEl_eq_getElem node native.node_tag bound, tag, tailRun]
        · simpa [cakeNegFirstMatchCol, read, tag, Tag.toProduction] using decoded
    · refine ⟨none, ?_, ?_⟩
      · simp [negFirstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, bound, queryOutcome]
      · simp [cakeNegFirstMatchCol, tagRead_outside related node bound]

/-- The negative preference's handled scan corresponds for all partner lists,
including invalid partners. The native Subscript result and actual immediate
none branch are derived from the canonical map domain. No all-partner bound
is required. This is actual/native infrastructure without a HOL original. -/
theorem handledNegFirstMatchCol_production (limit : Nat) (bads nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) :
    handleSubscript (negFirstMatchCol limit bads nodes) (ret none) native =
      (.success (cakeNegFirstMatchCol production limit bads nodes), native) := by
  obtain ⟨outcome, run, decoded⟩ := negFirstMatchOutcome limit bads nodes related
  rw [← decoded]
  cases outcome <;> simp [handleSubscript, run, queryOutcome, ret]

end Flapjack.RegAlloc
