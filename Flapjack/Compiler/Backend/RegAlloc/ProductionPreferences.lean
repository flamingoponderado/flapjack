import Flapjack.Compiler.Backend.RegAlloc.ProductionHandledColourReads

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Actual/native move-table carrier relation, including absent and outside
keys. This is Flapjack infrastructure, not a separate HOL declaration. -/
def ProductionMoveTableRel (native : Spt (List Nat))
    (production : CakeNodeMap (List Nat)) : Prop :=
  ∀ key, production.get key = sptLookup key native

private theorem moveLookup_first (key : Nat) (entries : NatInfoMap (List Nat)) :
    lookupNatInfo key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    simp only [lookupNatInfo, sptAListLookup, Bool.beq_eq_decide_eq]
    by_cases equal : key = other
    · subst other
      simp
    · simp [equal, Ne.symm equal, ih]

/-- The same association input constructs both table carriers, including
duplicate first-binding behavior. The executed moves-to-table and resorting
producer still requires its own correspondence proof. -/
theorem moveTableCodec_production (dimension : Nat) (entries : NatInfoMap (List Nat)) :
    ProductionMoveTableRel (sptFromAList entries)
      (CakeNodeMap.ofNatInfoMap dimension entries) := by
  intro key
  rw [CakeNodeMap.get_ofNatInfoMap, sptLookup_sptFromAList]
  exact moveLookup_first key entries

/-- Read-only root traversal agrees completely. Parent and tag bounds follow
from the original invariant, and recursion follows its strictly smaller node.
This relates the executed helper to the native definition without a HOL tag. -/
theorem coalesceRoot_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    coalesceRoot node native = (.success (cakeCoalesceRoot production node), native) := by
  induction node using Nat.strongRecOn with
  | ind node ih =>
    have parentBound : node < native.coalesced.length := by rwa [good.2.2.2.1]
    let parent := native.coalesced[node]
    have read := related.parent_read node parentBound
    have parentNodeBound : parent < native.dim :=
      good.2.2.2.2.2.1 parent (List.getElem_mem parentBound)
    have fixedRun := isFixed_production parent related good parentNodeBound
    dsimp only [parent] at fixedRun
    rw [coalesceRoot, cakeCoalesceRoot]
    simp only [Translator.Monadic.MonadBase.bind, coalescedSubEqn, parentBound,
      holEl_eq_getElem node native.coalesced parentBound, read, Option.getD_some, ↓reduceIte]
    rw [fixedRun]
    by_cases fixed : cakeIsFixed production native.coalesced[node]
    · simp [fixed, ret]
    · by_cases forward : node ≤ native.coalesced[node]
      · simp [fixed, forward, ret]
      · have recurse := ih parent (by omega) parentNodeBound
        simpa [fixed, forward, parent] using recurse

/-- Concrete positive preference callback, including missing partner failures.
Only the original state invariant and a genuine input-table relation are used;
the native returned value and unchanged state are proved. Flapjack-only
cross-implementation infrastructure without a separate HOL original. -/
theorem biasedPref_production (table : Spt (List Nat))
    (actualTable : CakeNodeMap (List Nat)) (node : Nat) (colours : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (tables : ProductionMoveTableRel table actualTable) :
    biasedPref table node colours native =
      (.success (cakeBiasedPref production actualTable node colours), native) := by
  simp only [biasedPref, Translator.Monadic.MonadBase.bind, getDim, cakeBiasedPref,
    related.dimension]
  by_cases bound : node < native.dim
  · simp only [bound, ↓reduceIte]
    simp only [Translator.Monadic.MonadBase.bind]
    rw [coalesceRoot_production node related good bound]
    simp only [tables node]
    cases lookup : sptLookup node table with
    | none =>
      simpa only [lookup, Option.getD_none] using
        handledFirstMatchCol_production colours [cakeCoalesceRoot production node] related
    | some partners =>
      simpa only [lookup, Option.getD_some] using
        handledFirstMatchCol_production colours (cakeCoalesceRoot production node :: partners) related
  · simp [bound, ret]

/-- Concrete negative callback for arbitrary move-partner lists, with its
source immediate Subscript handler and unchanged state. This is untagged
actual/native infrastructure rather than a duplicate HOL definition port. -/
theorem negBiasedPref_production (limit : Nat) (table : Spt (List Nat))
    (actualTable : CakeNodeMap (List Nat)) (node : Nat) (bads : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production)
    (tables : ProductionMoveTableRel table actualTable) :
    negBiasedPref limit table node bads native =
      (.success (cakeNegBiasedPref production limit actualTable node bads), native) := by
  simp only [negBiasedPref, Translator.Monadic.MonadBase.bind, getDim,
    cakeNegBiasedPref, related.dimension]
  by_cases bound : node < native.dim
  · simp only [bound, ↓reduceIte, tables node]
    cases lookup : sptLookup node table with
    | none =>
      simpa only [lookup, cakeNegFirstMatchCol] using
        handledNegFirstMatchCol_production limit bads [] related
    | some partners =>
      simpa only [lookup] using handledNegFirstMatchCol_production limit bads partners related
  · simp [bound, ret]

end Flapjack.RegAlloc
