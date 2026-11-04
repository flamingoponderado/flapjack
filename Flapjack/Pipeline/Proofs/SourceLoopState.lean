import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileDeclsCorrespondence
import Flapjack.Pancake.PanSimpByteRanged
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
import Flapjack.Pancake.PanToCrep.CompileProgCorrespondence
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Lab
import Flapjack.Display
import Flapjack.Pancake.CrepToLoop.Proofs.LocValueFree
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-! Proof-only exact/source Loop-state bridges. -/

namespace Flapjack

/-! ### Exact Spt code-table bridge for the non-executed routed alternative

The routed Loop compilation emits an association list, while the exact Loop
state uses an `Spt` code field. The declarations here build that Spt table from
the faithful, structurally rebased `compile_prog` rows and prove both lookup
directions needed by `LoopSemStateFiniteExact.prodRel`. They are Flapjack-only
bridges: HOL `compile_prog_def` returns a list and does not state a theorem
about the parser-backed production code carrier. -/

private theorem sptLookup_sptFromAList_mem_of_nodup {α : Type}
    (entries : List (Nat × α)) (hnodup : (entries.map Prod.fst).Nodup)
    {key : Nat} {value : α}
    (hlookup : sptLookup key (sptFromAList entries) = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [sptFromAList] at hlookup
  | cons entry entries ih =>
      obtain ⟨headKey, headValue⟩ := entry
      rcases List.nodup_cons.mp hnodup with ⟨hheadNot, htailNodup⟩
      by_cases hkey : headKey = key
      · subst key
        have hhead := sptLookup_sptInsert_same headKey headValue (sptFromAList entries)
        rw [sptFromAList, hhead] at hlookup
        injection hlookup with hvalue
        subst value
        exact List.mem_cons_self
      · rw [sptFromAList,
          sptLookup_sptInsert_ne headKey key headValue (sptFromAList entries)
            (Ne.symm hkey)] at hlookup
        exact List.mem_cons_of_mem _ (ih htailNodup hlookup)

private theorem sptFromAList_lookup_mem_of_nodup {α : Type}
    (entries : List (Nat × α)) (hnodup : (entries.map Prod.fst).Nodup)
    {key : Nat} {value : α}
    (hmem : (key, value) ∈ entries) :
    sptLookup key (sptFromAList entries) = some value :=
  memLookupFromAListSomeExact hnodup hmem

end Flapjack
