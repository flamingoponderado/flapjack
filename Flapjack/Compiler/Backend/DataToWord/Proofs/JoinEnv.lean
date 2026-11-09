module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! Environment-cut properties needed by data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- A successful environment cut never changes a retained lookup. -/
theorem cutEnv_lookup_retained {α : Type} (names : NumSet) (source target : Spt α)
    (run : DataSem.cutEnv names source = some target) (key : Nat) (value : α)
    (found : sptLookup key target = some value) : sptLookup key source = some value := by
  unfold DataSem.cutEnv at run
  split at run
  · simp only [Option.some.injEq] at run
    subst target
    rw [sptLookup_mkWf, sptLookup_sptInterCases] at found
    cases h : sptLookup key source <;> cases hn : sptLookup key names <;> simp_all
  · contradiction

/-- Cutting an environment retains each pair formed from its live word
variables. This generalized helper permits arbitrary word-side payloads. -/
theorem joinEnv_cutEnv_mem_general {α β : Type} [Nonempty α]
    (pair : α × β) (word : Spt β) (names : NumSet) (source target : Spt α)
    (member : pair ∈ joinEnv target (sptToAList (sptInter word (adjustSet target))))
    (run : DataSem.cutEnv names source = some target) :
    pair ∈ joinEnv source (sptToAList (sptInter word (adjustSet source))) := by
  simp only [joinEnv, List.mem_map, List.mem_filter] at member ⊢
  obtain ⟨⟨key, value⟩, ⟨inList, live⟩, equal⟩ := member
  have intersection := (sptMemToAList _ key value).mp inList
  rw [sptLookup_sptInterCases] at intersection
  cases wordLookup : sptLookup key word with
  | none => simp [wordLookup] at intersection
  | some wordValue =>
    cases adjustedLookup : sptLookup key (adjustSet target) with
    | none => simp [wordLookup, adjustedLookup] at intersection
    | some unitValue =>
      have inAdjusted : sptDomain (adjustSet target) key := by simp [sptDomain, adjustedLookup]
      obtain ⟨n, keyEq, targetMember⟩ := (adjustSet_domain target key).mp inAdjusted
      obtain ⟨sourceValue, targetLookup⟩ := (sptMem_iff_lookup n target).mp targetMember
      have sourceLookup := cutEnv_lookup_retained names source target run n sourceValue targetLookup
      have sourceMember : sptDomain source n := (sptMem_iff_lookup n source).mpr ⟨sourceValue, sourceLookup⟩
      have inSourceAdjusted : sptDomain (adjustSet source) key :=
        (adjustSet_domain source key).mpr ⟨n, keyEq, sourceMember⟩
      obtain ⟨u, sourceAdjustedLookup⟩ := (sptMem_iff_lookup key (adjustSet source)).mp inSourceAdjusted
      have sourceList : (key, value) ∈ sptToAList (sptInter word (adjustSet source)) := by
        apply (sptMemToAList _ key value).mpr
        rw [sptLookup_sptInterCases, wordLookup, sourceAdjustedLookup]
        simpa [wordLookup, adjustedLookup] using intersection
      have index : (key - 2) / 2 = n := by
        rw [keyEq]
        simp [adjustVar]
      refine ⟨(key, value), ⟨sourceList, live⟩, ?_⟩
      simpa [index, targetLookup, sourceLookup] using equal

/-- Every environment pair retained after cutting also occurs in the join
over the original source environment. The source value carrier and word width
are independent, as in the typed HOL replay. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "MEM_join_env_cut_env"
  (words_as_type_indexed_bitvec)]
theorem mem_joinEnv_cutEnv {width : Nat} [NeZero width] {α : Type} [Nonempty α]
    (target : Spt α) (pair : α × WordLocW width) (word : Spt (WordLocW width))
    (names : NumSet) (source : Spt α)
    (premises : pair ∈ joinEnv target (sptToAList (sptInter word (adjustSet target))) ∧
      DataSem.cutEnv names source = some target) :
    pair ∈ joinEnv source (sptToAList (sptInter word (adjustSet source))) :=
  joinEnv_cutEnv_mem_general pair word names source target premises.1 premises.2

end Flapjack.Compiler.Backend.DataToWord.Proofs
