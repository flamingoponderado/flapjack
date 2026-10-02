import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileLookupProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeMovesCorrectRight

namespace Flapjack.Compiler.Backend.WordAlloc

namespace ReconcileEmptyWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end ReconcileEmptyWitnesses

/-- Flapjack-specific proof factoring of the empty-moves branch inside the
original reconciliation proof. There is no independent HOL declaration: the
extra empty-moves guard is derived by the full evaluateSSAReconcile theorem's
case analysis, so this helper carries no HOL theorem tag. It retains the full
relation and injection inputs for that assembly and proves the total Skip run
and both output relations. The imported evaluator inherits the
reals_as_rational_cuts assumption (SOUNDNESS item 8). -/
theorem evaluateSSAReconcileEmpty {width : Nat} [NeZero width] {C F β : Type}
    (next : Nat) (curSSA tgtSSA : Spt Nat) (names : Spt β)
    (sourceLocals : Spt (WordLocW width))
    (target : WordSemStateFiniteExact width C F)
    (related : ssaLocalsRel next curSSA sourceLocals target.locals)
    (_injective : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup tgtSSA x = optionLookup tgtSSA y → x = y)
    (empty : ((((sptToAList names).map Prod.fst).map fun v =>
      match sptLookup v curSSA with
      | none => []
      | some cv => [(optionLookup tgtSSA v, cv)]).flatten).filter
        (fun pair => decide (pair.1 ≠ pair.2)) = []) :
    ∃ after, WordSemStateFiniteExact.evaluate (ssaReconcile curSSA tgtSSA names) target =
      (none, after) ∧ Flapjack.WordAlloc.wordStateEqRel target after ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup tgtSSA) (sptDomain names)
        sourceLocals after.locals := by
  have filtered : (((sptToAList names).map Prod.fst).filter fun v =>
      match sptLookup v curSSA with
      | none => false
      | some cv => decide (optionLookup tgtSSA v ≠ cv)) = [] := by
    have rewriteMoves := ssaReconcileMovesEq curSSA (optionLookup tgtSSA)
      ((sptToAList names).map Prod.fst)
    have canonicalEmpty : _ := empty
    have sameMoves : ((((sptToAList names).map Prod.fst).map fun v =>
        match sptLookup v curSSA with
        | none => []
        | some cv => [(optionLookup tgtSSA v, cv)]).flatten).filter
          (fun (a, b) => decide (a ≠ b)) = [] := by
      convert canonicalEmpty using 1
    have mapped := rewriteMoves.symm.trans (show _ = ([] : List (Nat × Nat)) from by
      convert sameMoves using 1
      congr 3
      funext v
      cases sptLookup v curSSA <;> rfl)
    have hf := List.map_eq_nil_iff.mp mapped
    convert hf using 1
    congr 1
    funext v
    cases sptLookup v curSSA <;> rfl
  refine ⟨target, ?_, ?_, ?_⟩
  · dsimp only [ssaReconcile]
    split
    · simp [WordSemStateFiniteExact.evaluate]
    · rename_i notEmpty
      exfalso
      apply notEmpty
      convert empty using 1
      congr 2
  · simp [Flapjack.WordAlloc.wordStateEqRel]
  · intro n value hn
    obtain ⟨domain, lookup, _⟩ := related.2 n value hn.2
    obtain ⟨register, found⟩ := (sptMem_iff_lookup n curSSA).mp domain
    have member := (sptMemMapFstToAList names n).mpr hn.1
    have same : optionLookup tgtSSA n = register := by
      by_contra different
      have mem : n ∈ (((sptToAList names).map Prod.fst).filter fun v =>
          match sptLookup v curSSA with
          | none => false
          | some cv => decide (optionLookup tgtSSA v ≠ cv)) := by
        simp [List.mem_filter, member, found, different]
      rw [filtered] at mem
      exact List.not_mem_nil mem
    simpa [same, found] using lookup

end Flapjack.Compiler.Backend.WordAlloc
