import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF
import Flapjack.Compiler.Backend.RegAlloc.ProductionNumSet

namespace Flapjack.WordAlloc

/-! Actual/native cutset and loop-context input equations. These are untagged
implementation infrastructure with no independent HOL declarations. They
derive the inputs used by original getClashTree from the real production
encoders, including duplicate names and missing context indices. -/

theorem toNumSet_production (names : List Nat) :
    LoopToWord.toNumSetHOL names =
      sptFromAList (names.map (fun name => (name, ()))) := by
  induction names with
  | nil => rfl
  | cons name names ih => simp only [LoopToWord.toNumSetHOL, List.map_cons, sptFromAList, ih]

private theorem unitLookup (names : List Nat) (key : Nat) :
    sptLookup key (sptFromAList (names.map (fun name => (name, ())))) =
      if key ∈ names then some () else none := by
  rw [sptLookup_sptFromAList]
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [List.map_cons, sptAListLookup, List.mem_cons]
      by_cases equal : key = name
      · simp only [equal, if_true, true_or]
      · simp only [equal, if_false, false_or, ih]

private theorem unitMap_eq_of_membership (left right : List Nat)
    (same : ∀ key, key ∈ left ↔ key ∈ right) :
    sptFromAList (left.map (fun key => (key, ()))) =
      sptFromAList (right.map (fun key => (key, ()))) := by
  apply (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr
  intro key
  simp only [unitLookup, same key]

private theorem insertFold_production (names : List Nat) :
    RegAlloc.productionNumSetToNative
      (names.foldr (fun key tree => NumSet.insert key tree) .empty) =
      sptFromAList (names.map (fun key => (key, ()))) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [List.foldr_cons, RegAlloc.numSetInsert_production, ih,
        List.map_cons, sptFromAList]

private theorem mem_toSet (names : List Nat) (key : Nat) :
    key ∈ NumSet.toSet names ↔ key ∈ names := by
  induction names generalizing key with
  | nil => rfl
  | cons name names ih =>
      simp only [NumSet.toSet, NumSet.insertList]
      split <;> simp_all

/-- Full executed list-to-set reconstruction retains precisely the canonical
native input map, with no distinctness or supplied output premise. -/
theorem numSetFromList_production (names : List Nat) :
    sptFromAList ((NumSet.fromList names).map (fun key => (key, ()))) =
      sptFromAList (names.map (fun key => (key, ()))) := by
  have enumeration := RegAlloc.numSetToAList_production
    ((NumSet.toSet names).foldr (fun key tree => NumSet.insert key tree) .empty) 0 []
  simp only [List.map_nil, insertFold_production] at enumeration
  change sptToAList (sptFromAList ((NumSet.toSet names).map (fun key => (key, ())))) =
    (NumSet.fromList names).map (fun key => (key, ())) at enumeration
  rw [← enumeration]
  have roundtrip : ∀ tree : Spt Unit, sptWf tree = true →
      sptFromAList (sptToAList tree) = tree := by
    intro tree wellFormed
    exact (sptEqThm _ _ ⟨sptWfFromAList _, wellFormed⟩).mpr
      (fun key => sptLookup_sptFromAList_sptToAList key tree)
  rw [roundtrip _ (sptWfFromAList _)]
  exact unitMap_eq_of_membership _ _ (mem_toSet names)

/-- Production cutset union equals the original sparse-tree union, retaining
both halves and arbitrary repeated names. -/
theorem callSet_production (left right : List Nat) :
    sptFromAList ((wordClashTreeCallSet left right).map (fun key => (key, ()))) =
      sptUnion (LoopToWord.toNumSetHOL left) (LoopToWord.toNumSetHOL right) := by
  rw [wordClashTreeCallSet, numSetFromList_production]
  apply (sptEqThm _ _ ⟨sptWfFromAList _, sptWfUnion _ _
    ⟨by rw [toNumSet_production]; exact sptWfFromAList _,
     by rw [toNumSet_production]; exact sptWfFromAList _⟩⟩).mpr
  intro key
  simp only [sptLookup_sptUnion, toNumSet_production, unitLookup,
    List.mem_eraseDups, List.mem_append]
  by_cases leftMember : key ∈ left <;> by_cases rightMember : key ∈ right <;>
    simp [leftMember, rightMember]

/-- Exact context lookup after the real cutset codec, including out-of-range
indices and both loop entry/exit sets. -/
theorem loopFrame_production (index : Nat) (frames : List (List Nat × List Nat)) :
    (wordClashTreeFindLoopFrame index frames).map wordCutsetsToHOL =
      (frames.map wordCutsetsToHOL)[index]? := by
  induction frames generalizing index with
  | nil => cases index <;> rfl
  | cons frame frames ih =>
      cases index with
      | zero => rfl
      | succ index => simpa only [wordClashTreeFindLoopFrame, Nat.add_sub_cancel,
          List.map_cons, List.getElem?_cons_succ] using ih index

end Flapjack.WordAlloc
