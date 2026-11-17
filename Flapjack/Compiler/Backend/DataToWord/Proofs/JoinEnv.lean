module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.JoinEnv

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

/-- Every environment pair retained after cutting also occurs in the join
over the original source environment. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "MEM_join_env_cut_env"
  (words_as_type_indexed_bitvec)]
theorem mem_joinEnv_cutEnv {width : Nat} [NeZero width]
    (target : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (pair : Flapjack.Compiler.Backend.DataSem.Value × WordLocW width) (word : Spt (WordLocW width))
    (names : NumSet) (source : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (premises : pair ∈ joinEnv target (sptToAList (sptInter word (adjustSet target))) ∧
      DataSem.cutEnv names source = some target) :
    pair ∈ joinEnv source (sptToAList (sptInter word (adjustSet source))) := by
  apply Assign.joinEnv_submap_mem target source word word pair
  exact ⟨fun key value found => cutEnv_lookup_retained names source target premises.2 key value found,
    fun _ _ found => found, premises.1⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs
