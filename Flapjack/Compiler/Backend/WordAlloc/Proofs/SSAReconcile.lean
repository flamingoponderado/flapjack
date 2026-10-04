import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileEmpty
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileGetVars

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof infrastructure: domain-restricted injection preserves the
distinctness of a list contained in that domain. No separate HOL original. -/
private theorem mapDistinctOn {α β : Type} (f : α → β) (domain : α → Prop)
    (inj : ∀ x y, domain x → domain y → f x = f y → x = y) :
    ∀ ls : List α, ls.Nodup → (∀ x, x ∈ ls → domain x) → (ls.map f).Nodup := by
  intro ls
  induction ls with
  | nil => simp
  | cons x xs ih =>
      intro distinct subset
      refine List.nodup_cons.mpr ⟨?_, ih distinct.tail (fun y hy =>
        subset y (List.mem_cons_of_mem x hy))⟩
      intro hm
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
      have same := inj y x (subset y (by simp [hy])) (subset x (by simp)) he
      exact (List.nodup_cons.mp distinct).1 (same ▸ hy)

namespace ReconcileWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end ReconcileWitnesses

/-- Full original native SSA reconciliation evaluator theorem. The original
SSA-locals relation and domain-restricted target-map injection prove existence
of the total pair result, complete frame relation and renamed local values.
No target execution, successful reads, output list, or post-state relation is
assumed. Both original move-list branches are covered. Native name-set payload,
configuration and FFI carriers remain arbitrary. The full evaluator inherits
reals_as_rational_cuts (SOUNDNESS item 8), although only Skip/Move run here.
The original indexed observations (word_allocProof:6660-6704) use EL only under
`i < LENGTH filtered_vars` and equal value-list lengths. Here membership supplies
that bound, `holEl_eq_getElem` connects the selected key, and the indexed getVars
and zip-lookup facts use the same derived bounds. The inherited total holEl/holHd
rendering retains shared opaque holHdNil/holArb outside the list; no public
bounds premise or concrete out-of-range value is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateSSAReconcile {width : Nat} [NeZero width] {C F β : Type}
    (next : Nat) (curSSA tgtSSA : Spt Nat) (names : Spt β)
    (sourceLocals : Spt (WordLocW width))
    (target : WordSemStateFiniteExact width C F)
    (h : ssaLocalsRel next curSSA sourceLocals target.locals ∧
      (∀ x y, sptDomain names x → sptDomain names y →
        optionLookup tgtSSA x = optionLookup tgtSSA y → x = y)) :
    ∃ after, WordSemStateFiniteExact.evaluate (ssaReconcile curSSA tgtSSA names) target =
      (none, after) ∧ Flapjack.WordAlloc.wordStateEqRel target after ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup tgtSSA) (sptDomain names)
        sourceLocals after.locals := by
  let vars := (sptToAList names).map Prod.fst
  let filtered := vars.filter fun v => match sptLookup v curSSA with
    | none => false
    | some cv => decide (optionLookup tgtSSA v ≠ cv)
  let moves := ((vars.map fun v => match sptLookup v curSSA with
    | none => []
    | some cv => [(optionLookup tgtSSA v, cv)]).flatten).filter
      (fun pair => decide (pair.1 ≠ pair.2))
  have movesEq : moves = filtered.map
      (fun v => (optionLookup tgtSSA v, holThe (sptLookup v curSSA))) := by
    have orig := ssaReconcileMovesEq curSSA (optionLookup tgtSSA) vars
    dsimp only [moves, filtered]
    convert orig using 1
    · congr 3
      funext v
      cases sptLookup v curSSA <;> rfl
    · congr 2
      funext v
      cases sptLookup v curSSA <;> rfl
  by_cases empty : moves = []
  · apply evaluateSSAReconcileEmpty next curSSA tgtSSA names sourceLocals target h.1 h.2
    exact empty
  have props : ∀ v, v ∈ filtered → sptDomain names v ∧
      ∃ cv, sptLookup v curSSA = some cv ∧ optionLookup tgtSSA v ≠ cv := by
    intro v hv
    obtain ⟨member, condition⟩ := List.mem_filter.mp hv
    have domain := (sptMemMapFstToAList names v).mp member
    cases found : sptLookup v curSSA with
    | none => simp [found] at condition
    | some cv => exact ⟨domain, cv, rfl, by simpa [found] using condition⟩
  have distinct : filtered.Nodup := ssaReconcileFilteredAllDistinct curSSA tgtSSA names
  have mappedDistinct : (filtered.map (optionLookup tgtSSA)).Nodup :=
    mapDistinctOn _ _ h.2 filtered distinct (fun v hv => (props v hv).1)
  obtain ⟨values, reads, length, indexed⟩ := ssaReconcileGetVarsLemma filtered curSSA target
    ⟨distinct, by
      intro v hv
      obtain ⟨_, cv, found, _⟩ := props v hv
      obtain ⟨value, lookup⟩ := (sptMem_iff_lookup cv target.locals).mp (h.1.1 v cv found)
      exact ⟨value, by simpa [found, holThe] using lookup⟩⟩
  let after := WordSemStateFiniteExact.setVars (filtered.map (optionLookup tgtSSA)) values target
  have compiled : ssaReconcile (width := width) curSSA tgtSSA names =
      .move 1 (filtered.map fun v => (optionLookup tgtSSA v, holThe (sptLookup v curSSA))) := by
    dsimp only [ssaReconcile]
    split
    · rename_i hempty
      exfalso
      apply empty
      convert hempty using 1
      congr 2
    · congr 1
  refine ⟨after, ?_, ?_, ?_⟩
  · rw [compiled]
    simp only [WordSemStateFiniteExact.evaluate, List.map_map]
    simp [Function.comp_def, mappedDistinct, reads, after]
  · simp [after, WordSemStateFiniteExact.setVars, Flapjack.WordAlloc.wordStateEqRel]
  · intro n value hn
    obtain ⟨domain, lookup, _⟩ := h.1.2 n value hn.2
    obtain ⟨cv, found⟩ := (sptMem_iff_lookup n curSSA).mp domain
    have oldLookup : sptLookup cv target.locals = some value := by
      simpa [found] using lookup
    dsimp only [after, WordSemStateFiniteExact.setVars]
    rw [lookup_alist_insert_any]
    by_cases same : optionLookup tgtSSA n = cv
    · have absent : n ∉ filtered := by
        intro member
        obtain ⟨_, cv', found', different⟩ := props n member
        have eq : cv' = cv := Option.some.inj (found'.symm.trans found)
        exact different (eq ▸ same)
      have lookupNone := alookupZipMapOptionLookupNone filtered values n names
        (optionLookup tgtSSA) ⟨h.2, hn.1, absent, (fun v hv => (props v hv).1), length⟩
      rw [lookupNone]
      simpa only [same] using oldLookup
    · have member : n ∈ filtered := by
        apply List.mem_filter.mpr
        exact ⟨(sptMemMapFstToAList names n).mpr hn.1, by simp [found, same]⟩
      obtain ⟨i, bound, entry⟩ := List.mem_iff_getElem.mp member
      have element : holEl i filtered = n := (holEl_eq_getElem i filtered bound).trans entry
      have lookupSome := alookupZipMapSome filtered values i (optionLookup tgtSSA)
        ⟨mappedDistinct, bound, length⟩
      rw [element] at lookupSome
      have valueLookup := indexed i bound
      rw [element, found] at valueLookup
      have valueEq : holEl i values = value := by
        apply Option.some.inj
        exact (by simpa [holThe] using valueLookup.symm.trans oldLookup)
      simp only [lookupSome, valueEq]

end Flapjack.Compiler.Backend.WordAlloc
