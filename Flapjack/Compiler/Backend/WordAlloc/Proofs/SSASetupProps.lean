import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMovePreserve
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.EvenListDistinct

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof infrastructure: every original prologue argument is a
physical register. This helper is not an independently claimed HOL port. -/
theorem setupArgumentPhysical (count key : Nat) (member : key ∈ evenList count) :
    isPhyVar key := by
  unfold evenList at member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  simp [isPhyVar]

/-- Flapjack proof infrastructure: the initial native empty SSA map satisfies
the reviewed map invariant at any starting counter. No HOL tag is claimed. -/
theorem setupEmptyMapOK (next : Nat) : ssaMapOK next .ln := by
  intro key register found
  simp [sptLookup] at found



/-- Flapjack infrastructure establishing the complete initial locals relation
from the original source-domain equality and actual native renaming result.
It is not a separately tagged HOL theorem. -/
theorem setupLocalsRelation {α : Type} [Nonempty α] (count next : Nat)
    (source : Spt α) (outputs : List Nat) (ssaOut : Spt Nat) (nextOut : Nat)
    (renamed : listNextVarRename (evenList count) .ln next = (outputs, ssaOut, nextOut))
    (domain : sptDomain source = (fun key => key ∈ evenList count)) :
    ssaLocalsRel nextOut ssaOut source
      (LoopSemStateFiniteExact.sptAlistInsert outputs
        ((evenList count).map (fun key => holThe (sptLookup key source))) source) := by
  have arithmetic := listNextVarRenameLemma1 (evenList count) .ln next
    outputs ssaOut nextOut renamed
  have lookup := listNextVarRenameLemma2Prime (evenList count) .ln next
    outputs ssaOut nextOut renamed (evenListNodup count)
  let f := fun key => (sptLookup key ssaOut).getD 0
  let g := fun key => holThe (sptLookup key source)
  have hd : ((evenList count).map f).Nodup := by
    rw [← lookup.1]
    exact arithmetic.1
  have written := renameMoveWrittenLookup (evenList count) f g source hd
  have mapDomain : ∀ key, sptMem key ssaOut ↔ key ∈ evenList count := by
    intro key
    change sptDomain ssaOut key ↔ _
    rw [congrFun lookup.2.1 key]
    simp [sptDomain, sptLookup]
  refine ⟨?_, ?_⟩
  · intro key register found
    have member := (mapDomain key).mp ((sptMem_iff_lookup key _).mpr ⟨register, found⟩)
    have same : f key = register := by simp [f, found]
    apply (sptMem_iff_lookup register _).mpr
    refine ⟨g key, ?_⟩
    rw [lookup.1]
    simpa only [same] using written key member
  · intro key value found
    have member : key ∈ evenList count := by
      rw [← congrFun domain key]
      exact (sptMem_iff_lookup key _).mpr ⟨value, found⟩
    refine ⟨(mapDomain key).mpr member, ?_, ?_⟩
    · rw [lookup.1]
      change sptLookup (f key)
        (LoopSemStateFiniteExact.sptAlistInsert ((evenList count).map f)
          ((evenList count).map g) source) = some value
      rw [written key member]
      simp only [g, found, holThe]
    · intro allocated
      have physical := setupArgumentPhysical count key member
      exact False.elim (((conventionPartitions key).2.2.mp allocated).1 physical)

namespace SetupPropsWitnesses

/-- Checked canonical full-state map carrier roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SetupPropsWitnesses

/-- Full original setup-SSA theorem. Fresh literal HOL proof/types confirm that
state, input program and generated Move share the same word dimension. The
original allocation-class and source-domain premises prove all six actual
native evaluator conclusions. No successful target evaluation or post-state
relation is assumed. The evaluator inherits `reals_as_rational_cuts` under
SOUNDNESS item 8; this prologue reads/writes only locals. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "setup_ssa_props"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem setupSSAProps {width : Nat} [NeZero width] {C F : Type}
    (limit count : Nat) (state : WordSemStateFiniteExact width C F)
    (program : WordLangProgHOL (BitVec width))
    (h : isAllocVar limit ∧
      sptDomain state.locals = (fun key => key ∈ evenList count)) :
    let (move, ssa, next) := setupSSA (outputWidth := width) count limit program
    let (result, target) := WordSemStateFiniteExact.evaluate move state
    result = none ∧ Flapjack.WordAlloc.wordStateEqRel state target ∧
      ssaMapOK next ssa ∧ ssaLocalsRel next ssa state.locals target.locals ∧
      isAllocVar next ∧ limit ≤ next := by
  generalize renamed : listNextVarRename (evenList count) .ln limit = output
  rcases output with ⟨outputs, ssaOut, nextOut⟩
  have arithmetic := listNextVarRenameLemma1 (evenList count) .ln limit
    outputs ssaOut nextOut renamed
  have properties := listNextVarRenameProps (evenList count) .ln limit
    outputs ssaOut nextOut renamed ⟨Or.inl h.1, setupEmptyMapOK limit⟩
  obtain ⟨values, read, valuesEq⟩ := Flapjack.WordAlloc.getVarsEq (evenList count) state (by
    intro key member
    rw [congrFun h.2 key]
    exact member)
  have related := setupLocalsRelation count limit state.locals outputs ssaOut nextOut renamed h.2
  have lengths : outputs.length = (evenList count).length := by
    rw [arithmetic.2.1]
    simp
  simp only [setupSSA, renamed, WordSemStateFiniteExact.evaluate]
  rw [List.map_fst_zip (Nat.le_of_eq lengths),
    List.map_snd_zip (Nat.le_of_eq lengths.symm)]
  simp only [arithmetic.1, if_true, read]
  refine ⟨True.intro, ?_, properties.2.2.2, ?_, properties.2.1 h.1, properties.1⟩
  · simp [WordSemStateFiniteExact.setVars, Flapjack.WordAlloc.wordStateEqRel]
  · change ssaLocalsRel nextOut ssaOut state.locals
      (LoopSemStateFiniteExact.sptAlistInsert outputs values state.locals)
    rw [valuesEq]
    exact related

end Flapjack.Compiler.Backend.WordAlloc
