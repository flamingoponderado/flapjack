import Flapjack.RiscV.Allocator
import Flapjack.RiscV.Backend
import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.CorrectnessBackend

/-!
Semantic foundations for the SSA and colouring stages of the Word allocator.
The register correspondence is deliberately expressed as an `Option`-valued
equation: it covers both valid RISC-V register names and the evaluator's
failure result for out-of-range virtual names.
-/

namespace Flapjack

open RiscV

theorem wordListRemap_lookup_preserves
    (sources : List Nat) (bijection : WordBijection)
    (source node : Nat)
    (hlookup : lookupNatInfo source bijection.toNode = some node) :
    lookupNatInfo source (wordListRemap sources bijection).toNode = some node := by
  induction sources generalizing bijection with
  | nil =>
      simpa [wordListRemap] using hlookup
  | cons head tail ih =>
      simp only [wordListRemap]
      split <;> rename_i hhead
      · exact ih bijection hlookup
      · by_cases heq : head = source
        · subst head
          simp [hlookup] at hhead
        · apply ih
          simp [lookupNatInfo, heq, hlookup]

theorem wordListRemap_lookup_of_mem
    (sources : List Nat) (bijection : WordBijection)
    (source : Nat) (hsource : source ∈ sources) :
    ∃ node, lookupNatInfo source (wordListRemap sources bijection).toNode = some node := by
  induction sources generalizing bijection with
  | nil =>
      cases hsource
  | cons head tail ih =>
      rcases List.mem_cons.mp hsource with hsource_head | htail
      · simp only [wordListRemap]
        have hsource_eq : source = head := hsource_head
        subst source
        split <;> rename_i hhead
        · exact ⟨_, wordListRemap_lookup_preserves tail bijection head _ hhead⟩
        · have hinsert : lookupNatInfo head
              ((head, bijection.next) :: bijection.toNode) = some bijection.next := by
            simp [lookupNatInfo]
          exact ⟨_, wordListRemap_lookup_preserves tail
            { toNode := (head, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, head) :: bijection.fromNode
              next := bijection.next + 1 } head bijection.next hinsert⟩
      · simp only [wordListRemap]
        split <;> rename_i hhead
        · exact ih bijection htail
        · exact ih
            { toNode := (head, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, head) :: bijection.fromNode
              next := bijection.next + 1 } htail

def wordBijectionWellFormed (bijection : WordBijection) : Prop :=
  (∀ source node,
    lookupNatInfo source bijection.toNode = some node →
      lookupNatInfo node bijection.fromNode = some source) ∧
  (∀ source node,
    lookupNatInfo source bijection.toNode = some node →
      node < bijection.next)

theorem wordListRemap_wellFormed
    (sources : List Nat) (bijection : WordBijection)
    (hform : wordBijectionWellFormed bijection) :
    wordBijectionWellFormed (wordListRemap sources bijection) := by
  induction sources generalizing bijection with
  | nil =>
      simpa [wordListRemap] using hform
  | cons head tail ih =>
      simp only [wordListRemap]
      split <;> rename_i hhead
      · exact ih bijection hform
      · let extended : WordBijection :=
          { toNode := (head, bijection.next) :: bijection.toNode
            fromNode := (bijection.next, head) :: bijection.fromNode
            next := bijection.next + 1 }
        have hformExtended : wordBijectionWellFormed extended := by
          constructor
          · intro source node hlookup
            by_cases hsource : source = head
            · subst source
              have hnode : node = bijection.next := by
                simpa [extended, lookupNatInfo] using hlookup.symm
              subst node
              simp [extended, lookupNatInfo]
            · have hlookupOld : lookupNatInfo source bijection.toNode = some node := by
                by_cases hnode : node = bijection.next
                · subst node
                  have hold : lookupNatInfo source bijection.toNode =
                      some bijection.next := by
                    simpa [extended, lookupNatInfo, hsource, Ne.symm hsource] using hlookup
                  have hbound := hform.2 source bijection.next hold
                  exact False.elim (Nat.lt_irrefl _ hbound)
                · simpa [extended, lookupNatInfo, hsource, Ne.symm hsource,
                    hnode, Ne.symm hnode] using hlookup
              have hnodeBound : node < bijection.next := hform.2 source node hlookupOld
              have hnodeFresh : node ≠ bijection.next := Nat.ne_of_lt hnodeBound
              have hfromOld := hform.1 source node hlookupOld
              simpa [extended, lookupNatInfo, hsource, Ne.symm hsource,
                hnodeFresh, Ne.symm hnodeFresh] using hfromOld
          · intro source node hlookup
            by_cases hsource : source = head
            · subst source
              have hnode : node = bijection.next := by
                simpa [extended, lookupNatInfo] using hlookup.symm
              subst node
              simp [extended]
            · have hlookupOld : lookupNatInfo source bijection.toNode = some node := by
                by_cases hnode : node = bijection.next
                · subst node
                  have hold : lookupNatInfo source bijection.toNode =
                      some bijection.next := by
                    simpa [extended, lookupNatInfo, hsource, Ne.symm hsource] using hlookup
                  have hbound := hform.2 source bijection.next hold
                  exact False.elim (Nat.lt_irrefl _ hbound)
                · simpa [extended, lookupNatInfo, hsource, Ne.symm hsource,
                    hnode, Ne.symm hnode] using hlookup
              have hnodeBound := hform.2 source node hlookupOld
              exact Nat.lt_trans hnodeBound (Nat.lt_succ_self _)
        exact ih extended hformExtended

theorem wordListRemap_lookup_inverse
    (sources : List Nat) (bijection : WordBijection)
    (hform : wordBijectionWellFormed bijection) :
    ∀ source node,
      lookupNatInfo source (wordListRemap sources bijection).toNode = some node →
      lookupNatInfo node (wordListRemap sources bijection).fromNode = some source := by
  have hresult := wordListRemap_wellFormed sources bijection hform
  exact hresult.1

theorem wordMkBijection_wellFormed (tree : WordClashTree) :
    wordBijectionWellFormed (wordMkBijection tree) := by
  have hbase : wordBijectionWellFormed
      ({ toNode := [], fromNode := [], next := 0 } : WordBijection) := by
    constructor <;> simp [lookupNatInfo]
  have go : ∀ (tree : WordClashTree) (bijection : WordBijection),
      wordBijectionWellFormed bijection →
        wordBijectionWellFormed (wordClashTreeBijection tree bijection) := by
    intro tree
    induction tree with
    | delta writes reads =>
        intro bijection hform
        have hreads := wordListRemap_wellFormed reads bijection hform
        simpa [wordClashTreeBijection] using
          wordListRemap_wellFormed writes (wordListRemap reads bijection) hreads
    | set names =>
        intro bijection hform
        simpa [wordClashTreeBijection] using
          wordListRemap_wellFormed names bijection hform
    | branch live thenBranch elseBranch ihThen ihElse =>
        intro bijection hform
        have hthen := ihThen bijection hform
        have helse := ihElse (wordClashTreeBijection thenBranch bijection) hthen
        cases live with
        | none => simpa [wordClashTreeBijection] using helse
        | some names =>
            simpa [wordClashTreeBijection] using
              wordListRemap_wellFormed names
                (wordClashTreeBijection elseBranch
                  (wordClashTreeBijection thenBranch bijection)) helse
    | seq first second ihFirst ihSecond =>
        intro bijection hform
        have hsecond := ihSecond bijection hform
        simpa [wordClashTreeBijection] using
          ihFirst (wordClashTreeBijection second bijection) hsecond
  exact go tree { toNode := [], fromNode := [], next := 0 } hbase

theorem wordMkBijection_lookup_inverse (tree : WordClashTree) :
    ∀ source node,
      lookupNatInfo source (wordMkBijection tree).toNode = some node →
      lookupNatInfo node (wordMkBijection tree).fromNode = some source := by
  exact (wordMkBijection_wellFormed tree).1

theorem wordAllocateGraphFunctionWithStackOnlyRenamed_maps_parameters [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithStackOnlyRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  simp [wordAllocateGraphFunctionWithStackOnlyRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  simp [wordAllocateGraph] at hgraph
  rcases hgraph with ⟨_, rfl⟩
  intro name hname
  have hnode := wordListRemap_lookup_of_mem
    (wordSsaRenameFunction parameters program).2.fst
    (wordClashTreeBijection
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
      { toNode := [], fromNode := [], next := 0 }) name hname
  simpa [wordInitRegAlloc, wordMkBijection,
    wordAllocateGraphFunctionWithStackOnlyRenamed, wordClashTreeBijection] using hnode

theorem wordAllocateGraphFunctionWithStackOnlyRenamed_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithStackOnlyRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithStackOnlyRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  simp [wordAllocateGraph] at hgraph
  rcases hgraph with ⟨hchecks, heq⟩
  cases heq
  rcases hchecks with ⟨⟨hfixed, hedges⟩, htree⟩
  exact ⟨hfixed, hedges, htree⟩

/-! The full-SSA entry variant has the same graph witness, but its clash tree
    starts with the explicit fresh-parameter setup.  Keep this theorem next to
    the ordinary graph contract so downstream callers can use either function
    boundary without unfolding the allocator. -/

theorem wordAllocateGraphFunctionWithEntryRenamed_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntryRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithEntryRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  exact wordAllocateGraph_sound
    (WordClashTree.seq
      (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
    (wordProgForcedClashes (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    fixedSources
    (wordProgPreferenceEdges (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    colours stackStart allocation' hgraph

theorem wordAllocateGraphFunctionWithEntryRenamed_maps_parameters [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntryRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  simp [wordAllocateGraphFunctionWithEntryRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  simp [wordAllocateGraph] at hgraph
  rcases hgraph with ⟨_, rfl⟩
  intro name hname
  have hnode := wordListRemap_lookup_of_mem
    (wordSsaRenameFunctionWithEntry parameters program).2.fst
    (wordClashTreeBijection
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
      { toNode := [], fromNode := [], next := 0 }) name hname
  simpa [wordInitRegAlloc, wordMkBijection,
    wordAllocateGraphFunctionWithEntryRenamed, wordClashTreeBijection] using hnode

/-! The coloured full-SSA entry variant exposes the same allocator witness as
    the renamed variant.  Keeping this theorem at the coloured boundary is
    useful for the RISC-V correctness theorem: clients can obtain the graph
    checks directly from the exact result whose body they execute, without
    unfolding the allocator and re-proving the entry clash-tree equation. -/

theorem wordAllocateGraphFunctionWithEntry_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (colouredProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntry parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, colouredProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateGraphFunctionWithEntry] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  exact wordAllocateGraph_sound
    (WordClashTree.seq
      (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
    (wordProgForcedClashes (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    fixedSources
    (wordProgPreferenceEdges (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    colours stackStart allocation' hgraph

theorem wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences parameters
        program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunction parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
        allocation.locations = true := by
  simp [wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rename_i x inner hinner
  rcases halloc with ⟨⟨hspecial, htreeChecked⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst state
  subst renamedParameters
  subst renamedProgram
  subst allocation
  have hclash := wordAllocateVarsWithSpillsAndPreferences_sound _ _ _
    inner hinner
  exact ⟨hclash, hspecial, htreeChecked⟩

theorem wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences_maps_variables [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences parameters
        program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences] at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithSpillsAndPreferences_maps_slots
    ((wordSsaRenameFunction parameters program).2.fst ++
      (wordProgVariables (wordSsaRenameFunction parameters program).2.snd ++
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd [])
          []).fst))
    (wordClashTreeAnalyze
      (wordClashTree (wordSsaRenameFunction parameters program).2.snd []) []).snd
    (wordProgPreferenceEdges (wordSsaRenameFunction parameters program).2.snd)
    alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed]
    at halloc
  split at halloc <;> simp_all
  rename_i x inner hinner
  rcases halloc with ⟨⟨hspecial, htreeChecked⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst state
  subst renamedParameters
  subst renamedProgram
  subst allocation
  have hclashAll := wordAllocateVarsWithFixedSources_sound _ _ _ _ inner hinner
  have hclash := wordSpillAllocationRespectsClashes_append_left _ _ _ hclashAll
  exact ⟨hclash, hspecial, htreeChecked⟩

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_maps_variables [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithFixedSources_maps_slots
    _ _ _ _ alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences]
    at halloc
  split at halloc <;> simp_all
  rename_i x inner hinner
  rcases halloc with ⟨⟨hspecial, htreeChecked⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst state
  subst renamedParameters
  subst renamedProgram
  subst allocation
  have hclash := wordAllocateVarsWithSpillsAndPreferences_sound _ _ _
    inner hinner
  exact ⟨hclash, hspecial, htreeChecked⟩

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences_maps_variables [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithSpillsAndPreferences_maps_slots
    ((wordSsaRenameFunctionWithEntry parameters program).2.fst ++
      (wordProgVariables (wordSsaRenameFunctionWithEntry parameters program).2.snd ++
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).fst))
    (wordClashTreeAnalyze
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
      []).snd
    (wordProgPreferenceEdges
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast]
    at halloc
  split at halloc <;> simp_all
  rename_i x inner hinner
  rcases halloc with ⟨⟨hspecial, htreeChecked⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst state
  subst renamedParameters
  subst renamedProgram
  subst allocation
  have hclashAll := wordAllocateVarsWithFixedSourcesFast_sound _ _ _ _ inner hinner
  have hclash := wordSpillAllocationRespectsClashes_append_left _ _ _ hclashAll
  exact ⟨hclash, hspecial, htreeChecked⟩

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast_maps_variables [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithFixedSourcesFast_maps_slots
    _ _ _ _ alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast_preserves_parameters [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ parameters →
      lookupNatInfo name allocation.locations = some (.register name) := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  intro name hname
  apply wordAllocateVarsWithFixedSourcesFast_preserves_fixed_source _ _ _ _ alloc
    hallocation name
  exact List.mem_append_left _ hname

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast_witness [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true ∧
      (∀ name, name ∈ wordProgVariables renamedProgram →
        ∃ location, lookupNatInfo name allocation.locations = some location) ∧
      (∀ name, name ∈ parameters →
        lookupNatInfo name allocation.locations = some (.register name)) := by
  have hsound :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast_sound
      parameters program state renamedParameters renamedProgram allocation halloc
  have hvariables :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast_maps_variables
      parameters program state renamedParameters renamedProgram allocation halloc
  have hparameters :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedFast_preserves_parameters
      parameters program state renamedParameters renamedProgram allocation halloc
  exact ⟨hsound.1, hsound.2.1, hsound.2.2, hvariables, hparameters⟩

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast_sound [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast]
    at halloc
  split at halloc <;> simp_all
  rename_i x inner hinner
  rcases halloc with ⟨⟨hspecial, htreeChecked⟩, hstate, hparameters,
    hprogram, hallocation⟩
  subst state
  subst renamedParameters
  subst renamedProgram
  subst allocation
  have hclashAll := wordAllocateVarsWithFixedSourcesClashFast_sound _ _ _ _ inner hinner
  have hclash := wordSpillAllocationRespectsClashes_append_left _ _ _ hclashAll
  exact ⟨hclash, hspecial, htreeChecked⟩

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast_maps_variables [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ wordProgVariables renamedProgram →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  have hslots := wordAllocateVarsWithFixedSourcesClashFast_maps_slots
    _ _ _ _ alloc hallocation
  intro name hname
  apply hslots name
  simp [hname]

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast_preserves_parameters [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    ∀ name, name ∈ parameters →
      lookupNatInfo name allocation.locations = some (.register name) := by
  simp [wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast]
    at halloc
  split at halloc <;> simp_all
  rcases halloc with ⟨_, rfl, rfl, rfl, rfl⟩
  rename_i _ alloc _ hallocation
  intro name hname
  apply wordAllocateVarsWithFixedSourcesClashFast_preserves_fixed_source _ _ _ _ alloc
    hallocation name
  exact List.mem_append_left _ hname

theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast_witness [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true ∧
      (∀ name, name ∈ wordProgVariables renamedProgram →
        ∃ location, lookupNatInfo name allocation.locations = some location) ∧
      (∀ name, name ∈ parameters →
        lookupNatInfo name allocation.locations = some (.register name)) := by
  have hsound :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast_sound
      parameters program state renamedParameters renamedProgram allocation halloc
  have hvariables :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast_maps_variables
      parameters program state renamedParameters renamedProgram allocation halloc
  have hparameters :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast_preserves_parameters
      parameters program state renamedParameters renamedProgram allocation halloc
  exact ⟨hsound.1, hsound.2.1, hsound.2.2, hvariables, hparameters⟩

/-!
Package the entry-inclusive spill allocator's independent obligations into the
single witness consumed by the location-aware Word-to-Stack boundary.  This
keeps callers from unfolding the allocator merely to recover its safety,
coverage, and ABI-entry facts.
-/
theorem wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences_witness [OfNat α 0]
    (parameters : List Nat) (program : WordProg α)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α) (allocation : WordSpillState)
    (halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program =
        some (state, renamedParameters, renamedProgram, allocation)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true ∧
      (∀ name, name ∈ wordProgVariables renamedProgram →
        ∃ location, lookupNatInfo name allocation.locations = some location) ∧
      (∀ name, name ∈ parameters →
        lookupNatInfo name allocation.locations = some (.register name)) := by
  have hsound :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_sound
      parameters program state renamedParameters renamedProgram allocation halloc
  have hvariables :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_maps_variables
      parameters program state renamedParameters renamedProgram allocation halloc
  have hparameters :=
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_preserves_parameters
      parameters program state renamedParameters renamedProgram allocation halloc
  exact ⟨hsound.1, hsound.2.1, hsound.2.2, hvariables, hparameters⟩

end Flapjack
