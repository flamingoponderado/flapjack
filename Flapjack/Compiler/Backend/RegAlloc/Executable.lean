import Flapjack.Compiler.Backend.RegAlloc.ProductionWrapper
import Flapjack.Compiler.Backend.RegAlloc.ProductionInputGuard

/-! Executable realization of the native allocator through its checked array
implementation. The original declaration and its literal list-state body are
unchanged. Runtime input checks discharge the existing implementation theorem;
arbitrary inputs retain the original computation. No new HOL port is claimed. -/
namespace Flapjack.RegAlloc
open Flapjack RiscV RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem roundtripSpt {α : Type} (tree : Spt α) (wellFormed : sptWf tree = true) :
    sptFromAList (sptToAList tree) = tree := by
  exact (sptEqThm _ _ ⟨sptWfFromAList _, wellFormed⟩).mpr
    (fun key => sptLookup_sptFromAList_sptToAList key tree)

private theorem unitAssociations (entries : List (Nat × Unit)) :
    (entries.map Prod.fst).map (fun key => (key, ())) = entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨key, payload⟩ := entry
      cases payload
      simp only [List.map_cons, ih]

private theorem roundtripUnit (tree : NumSet) (wellFormed : sptWf tree = true) :
    sptFromAList (((sptToAList tree).map Prod.fst).map (fun key => (key, ()))) = tree := by
  rw [unitAssociations]
  exact roundtripSpt tree wellFormed

/-- Exact fast computation on the checked native input fragment. The fallback
uses the original auxiliary call directly, so compiler rewriting of regAlloc
cannot turn the fallback into a recursive call to this interface. -/
def regAllocExecutable (algorithm : Algorithm) (costs : Option (Spt Nat)) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) (tree : ClashTree) (forced : List (Nat × Nat))
    (stackOnly : NumSet) : Exc (Spt Nat) StateException :=
  let rendered := nativeClashTreeToProduction tree
  if nativeRegAllocInputGuard costs tree forced stackOnly then
    match cakeDoRegAlloc algorithm.toProduction
        (costs.map fun costs => cakeSpillCostMap (cakeMkBij rendered).nextNode (sptToAList costs))
        limit moves rendered forced ((sptToAList stackOnly).map Prod.fst) with
    | some colours => .success (sptFromAList colours)
    | none => regAllocAux algorithm costs limit moves tree forced stackOnly (mkBij tree)
  else regAllocAux algorithm costs limit moves tree forced stackOnly (mkBij tree)

/-- Whole native result equality, including arbitrary inputs that fail the
runtime checks. The efficient implementation is not assumed to succeed. -/
theorem regAllocExecutable_eq (algorithm : Algorithm) (costs : Option (Spt Nat)) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) (tree : ClashTree) (forced : List (Nat × Nat))
    (stackOnly : NumSet) :
    regAllocExecutable algorithm costs limit moves tree forced stackOnly =
      regAlloc algorithm costs limit moves tree forced stackOnly := by
  unfold regAllocExecutable
  dsimp only
  split
  · rename_i checked
    have parts := (nativeRegAllocInputGuard_iff costs tree forced stackOnly).mp checked
    have bounds := parts.2.2.2
    have costsRoundtrip : (costs.map sptToAList).map sptFromAList = costs := by
      cases costs with
      | none => rfl
      | some costs =>
          simp only [Option.map_some, roundtripSpt costs (parts.2.1 costs rfl)]
    obtain ⟨colours, nativeRun, actualRun⟩ := regAlloc_production algorithm
      (costs.map sptToAList) limit moves (nativeClashTreeToProduction tree)
      forced ((sptToAList stackOnly).map Prod.fst) bounds
    rw [costsRoundtrip, clashTreeCodec_roundtrip tree parts.1,
      roundtripUnit stackOnly parts.2.2.1] at nativeRun
    simp only [Option.map_map, Function.comp_def] at actualRun
    rw [actualRun]
    exact nativeRun.symm
  · rfl

/-- Kernel-checked compiler replacement of the unchanged native declaration. -/
@[csimp] theorem regAlloc_eq_executable : @regAlloc = @regAllocExecutable := by
  funext algorithm costs limit moves tree forced stackOnly
  exact (regAllocExecutable_eq algorithm costs limit moves tree forced stackOnly).symm

end Flapjack.RegAlloc
