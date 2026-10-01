import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAOptionLookupSubset
import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectRight
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameLookup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof infrastructure for the actual parallel move input read.
The original locals relation and input-domain premise supply every source
register. This is an intermediate lemma, not a port of the complete
`list_next_var_rename_move_preserve_weak` theorem. -/
theorem renameMoveInputs {width : Nat} [NeZero width] {C F : Type}
    (next : Nat) (ssa : Spt Nat) (source : Spt (WordLocW width))
    (target : WordSemStateFiniteExact width C F) (names : List Nat)
    (related : ssaLocalsRel next ssa source target.locals)
    (present : ∀ key ∈ names, sptDomain ssa key) :
    ∃ values, WordSemStateFiniteExact.getVars (names.map (optionLookup ssa)) target =
      some values ∧
      values = (names.map (optionLookup ssa)).map
        (fun register => holThe (sptLookup register target.locals)) := by
  apply Flapjack.WordAlloc.getVarsEq
  exact optionLookupSubsetHelper ssa target.locals names ⟨related.1, present⟩



/-- Flapjack infrastructure: a duplicate-free parallel write returns the
corresponding value at each written register. No HOL theorem tag is claimed. -/
theorem renameMoveWrittenLookup {α : Type} (names : List Nat) (f : Nat → Nat)
    (g : Nat → α) (target : Spt α) (distinct : (names.map f).Nodup) :
    ∀ key ∈ names, sptLookup (f key)
      (LoopSemStateFiniteExact.sptAlistInsert (names.map f) (names.map g) target) =
        some (g key) := by
  induction names with
  | nil => simp
  | cons name names ih =>
    have hd := List.nodup_cons.mp distinct
    intro key member
    simp only [List.map_cons, LoopSemStateFiniteExact.sptAlistInsert]
    rcases List.mem_cons.mp member with equal | member
    · subst key
      exact sptLookup_sptInsert_same _ _ _
    · have different : f key ≠ f name := by
        intro equal
        apply hd.1
        exact equal ▸ List.mem_map.mpr ⟨key, member, rfl⟩
      rw [sptLookup_sptInsert_ne _ _ _ _ different]
      exact ih hd.2 key member



/-- Flapjack infrastructure proving the complete locals update for the actual
native renaming result. It uses only the original premises; it is not yet the
full evaluator theorem and therefore has no HOL tag. -/
theorem renameMoveLocals {α : Type} [Nonempty α]
    (names : List Nat) (ssa : Spt Nat) (next : Nat) (source target : Spt α)
    (outputs : List Nat) (ssaOut : Spt Nat) (nextOut : Nat)
    (renamed : listNextVarRename names ssa next = (outputs, ssaOut, nextOut))
    (distinct : names.Nodup) (valid : ssaMapOK next ssa)
    (related : ssaLocalsRel next ssa source target) :
    ssaLocalsRel nextOut ssaOut source
      (LoopSemStateFiniteExact.sptAlistInsert outputs
        (names.map (fun key => holThe (sptLookup (optionLookup ssa key) target))) target) := by
  have arithmetic := listNextVarRenameLemma1 names ssa next outputs ssaOut nextOut renamed
  have lookup := listNextVarRenameLemma2Prime names ssa next outputs ssaOut nextOut renamed distinct
  let f := fun key => (sptLookup key ssaOut).getD 0
  let g := fun key => holThe (sptLookup (optionLookup ssa key) target)
  have hd : (names.map f).Nodup := by rw [← lookup.1]; exact arithmetic.1
  have written := renameMoveWrittenLookup names f g target hd
  have fresh : ∀ register ∈ outputs, next ≤ register := by
    intro register member
    rw [arithmetic.2.1] at member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    omega
  have preserved : ∀ register, register < next →
      sptLookup register (LoopSemStateFiniteExact.sptAlistInsert outputs
        (names.map g) target) = sptLookup register target := by
    intro register below
    apply Flapjack.WordAlloc.sptLookup_sptAlistInsert_notMem
    intro member
    have := fresh register member
    omega
  refine ⟨?_, ?_⟩
  · intro key register found
    apply (sptMem_iff_lookup register _).mpr
    by_cases member : key ∈ names
    · have same : f key = register := by simp [f, found]
      refine ⟨g key, ?_⟩
      rw [lookup.1]
      simpa only [same] using written key member
    · have original : sptLookup key ssa = some register :=
        (lookup.2.2.1 key member).symm.trans found
      rcases (sptMem_iff_lookup register target).mp (related.1 key register original) with
        ⟨value, valueFound⟩
      refine ⟨value, ?_⟩
      rw [preserved register (valid key register original).2]
      exact valueFound
  · intro key value valueFound
    rcases related.2 key value valueFound with ⟨domain, matchValue, bound⟩
    have outputDomain : sptMem key ssaOut := by
      have domains := congrFun lookup.2.1 key
      change sptDomain ssaOut key
      rw [domains]
      exact Or.inl domain
    refine ⟨outputDomain, ?_, ?_⟩
    · by_cases member : key ∈ names
      · rw [lookup.1]
        change sptLookup (f key)
          (LoopSemStateFiniteExact.sptAlistInsert (names.map f) (names.map g) target) = some value
        rw [written key member]
        rcases (sptMem_iff_lookup key ssa).mp domain with ⟨register, found⟩
        simp only [found, Option.getD_some] at matchValue
        have read : sptLookup (optionLookup ssa key) target = some value := by
          simpa only [optionLookup, found] using matchValue
        simp only [g, read, holThe]
      · rw [lookup.2.2.1 key member]
        rcases (sptMem_iff_lookup key ssa).mp domain with ⟨register, found⟩
        simp only [found, Option.getD_some] at matchValue ⊢
        rw [preserved register (valid key register found).2]
        exact matchValue
    · intro allocated
      have := bound allocated
      rw [arithmetic.2.2]
      omega



namespace RenameMoveWitnesses

/-- Canonical carrier roundtrip for the full evaluator state maps. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end RenameMoveWitnesses

/-- Full original move-renaming preservation theorem: arbitrary native trees,
all five original premises, and the actual evaluator NONE/locals/whole-state
conclusions. Fresh literal HOL replay confirms the shared source/target word,
code and FFI dimensions. The full evaluator inherits the documented
`reals_as_rational_cuts` boundary (SOUNDNESS item 8); this Move path only reads
and writes locals. No allocation-class or successful-evaluation premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "list_next_var_rename_move_preserve_weak"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem listNextVarRenameMovePreserveWeak {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (next : Nat) (names : List Nat) (target : WordSemStateFiniteExact width C F)
    (h : ssaLocalsRel next ssa source.locals target.locals ∧
      (∀ key ∈ names, sptDomain ssa key) ∧ names.Nodup ∧
      ssaMapOK next ssa ∧ Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move, ssaOut, nextOut) := listNextVarRenameMove (width := width) ssa next names
    let (result, targetOut) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel nextOut ssaOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut := by
  generalize renamed : listNextVarRename names ssa next = output
  rcases output with ⟨outputs, ssaOut, nextOut⟩
  have arithmetic := listNextVarRenameLemma1 names ssa next outputs ssaOut nextOut renamed
  have lengths : outputs.length = names.length := by
    rw [arithmetic.2.1]
    simp
  obtain ⟨values, read, valuesEq⟩ := renameMoveInputs next ssa source.locals target names h.1 h.2.1
  have update := renameMoveLocals names ssa next source.locals target.locals
    outputs ssaOut nextOut renamed h.2.2.1 h.2.2.2.1 h.1
  simp only [listNextVarRenameMove, renamed]
  simp only [WordSemStateFiniteExact.evaluate]
  have zipLength : outputs.length = (names.map (optionLookup ssa)).length := by
    simpa only [List.length_map] using lengths
  rw [List.map_fst_zip (Nat.le_of_eq zipLength), List.map_snd_zip (Nat.le_of_eq zipLength.symm)]
  simp only [arithmetic.1, if_true, read]
  refine ⟨True.intro, ?_, ?_⟩
  · change ssaLocalsRel nextOut ssaOut source.locals
      (LoopSemStateFiniteExact.sptAlistInsert outputs values target.locals)
    rw [valuesEq]
    simpa only [List.map_map, Function.comp_def] using update
  · exact h.2.2.2.2


/-- Full strong native move preservation statement under source-domain premises.
Fresh literal HOL replay confirms the complete five-conclusion statement and
shared word/code/FFI dimensions. Canonical fpRegs/store and positive-width
word carriers retain the inherited reals_as_rational_cuts assumption of
SOUNDNESS item 8; this Move branch only reads/writes locals. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "list_next_var_rename_move_preserve"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem listNextVarRenameMovePreserve {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (next : Nat) (names : List Nat) (target : WordSemStateFiniteExact width C F)
    (h : ssaLocalsRel next ssa source.locals target.locals ∧
      (∀ key ∈ names, sptDomain source.locals key) ∧ names.Nodup ∧
      ssaMapOK next ssa ∧ Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move, ssaOut, nextOut) := listNextVarRenameMove (width := width) ssa next names
    let (result, targetOut) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel nextOut ssaOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut ∧
      (¬ isPhyVar next → ∀ register, isPhyVar register →
        sptLookup register targetOut.locals = sptLookup register target.locals) ∧
      (∀ key value, sptLookup key source.locals = some value →
        sptLookup (holThe (sptLookup key ssa)) targetOut.locals = some value) := by
  have present : ∀ key ∈ names, sptDomain ssa key := by
    intro key member
    obtain ⟨value, found⟩ := (sptMem_iff_lookup key source.locals).mp (h.2.1 key member)
    exact (h.1.2 key value found).1
  generalize renamed : listNextVarRename names ssa next = output
  rcases output with ⟨outputs, ssaOut, nextOut⟩
  have arithmetic := listNextVarRenameLemma1 names ssa next outputs ssaOut nextOut renamed
  have lengths : outputs.length = (names.map (optionLookup ssa)).length := by
    rw [arithmetic.2.1]
    simp
  obtain ⟨values, read, valuesEq⟩ := renameMoveInputs next ssa source.locals target names h.1 present
  have weak := listNextVarRenameMovePreserveWeak source ssa next names target
    ⟨h.1, present, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  simp only [listNextVarRenameMove, renamed, WordSemStateFiniteExact.evaluate,
    List.map_fst_zip (Nat.le_of_eq lengths),
    List.map_snd_zip (Nat.le_of_eq lengths.symm), arithmetic.1, if_true, read] at weak ⊢
  refine ⟨weak.1, weak.2.1, weak.2.2, ?_, ?_⟩
  · intro nonphysical register physical
    change sptLookup register (LoopSemStateFiniteExact.sptAlistInsert outputs values target.locals) = sptLookup register target.locals
    apply Flapjack.WordAlloc.sptLookup_sptAlistInsert_notMem
    intro member
    rw [arithmetic.2.1] at member
    obtain ⟨index, _, equal⟩ := List.mem_map.mp member
    simp only [isPhyVar, decide_eq_true_eq] at nonphysical physical
    omega
  · intro key value found
    obtain ⟨domain, matchValue, _⟩ := h.1.2 key value found
    obtain ⟨register, mapped⟩ := (sptMem_iff_lookup key ssa).mp domain
    have below := (h.2.2.2.1 key register mapped).2
    have absent : register ∉ outputs := by
      intro member
      rw [arithmetic.2.1] at member
      obtain ⟨index, _, equal⟩ := List.mem_map.mp member
      omega
    simp only [mapped, holThe]
    change sptLookup register (LoopSemStateFiniteExact.sptAlistInsert outputs values target.locals) = some value
    rw [Flapjack.WordAlloc.sptLookup_sptAlistInsert_notMem _ _ _ _ absent]
    simpa only [mapped, Option.getD_some] using matchValue

end Flapjack.Compiler.Backend.WordAlloc
