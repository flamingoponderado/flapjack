import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.Pancake.WordLang.CutsetsMax

namespace Flapjack

/-- Flapjack-only key-enumeration correspondence on the existing exact Spt
carrier. No tree well-formedness or ordering premise is needed. -/
private theorem sptUnitKey_mem (tree : Spt Unit) (key : Nat) :
    key ∈ (sptToAList tree).map Prod.fst ↔ sptLookup key tree = some () := by
  constructor
  · intro h
    obtain ⟨⟨found, value⟩, hmem, hkey⟩ := List.mem_map.mp h
    cases value
    change found = key at hkey
    subst found
    have hfold : (key, ()) ∈ sptFoldi (fun k v entries => (k, v) :: entries) 0 [] tree :=
      hmem
    rcases sptFoldi_mem_address tree 0 [] key () hfold with hnil | ⟨localKey, haddr, hlookup⟩
    · simp at hnil
    · have same : key = localKey := by simpa [sptAcc_eq, lrNext] using haddr
      simpa only [same] using hlookup
  · intro h
    have hfold := sptFoldi_lookup_mem tree 0 [] key () h
    have hmem : (key, ()) ∈ sptToAList tree := by
      simpa only [sptAcc_eq, lrNext, Nat.zero_add, Nat.one_mul, sptToAList] using hfold
    exact List.mem_map.mpr ⟨(key, ()), hmem, rfl⟩

/-- Flapjack-only maximum bound for any list, independent of its order or
duplicate entries. There is no separate HOL theorem being ported here. -/
private theorem maxList_le_of_members (values : List Nat) (bound : Nat)
    (h : ∀ value ∈ values, value ≤ bound) : maxList values ≤ bound := by
  induction values with
  | nil => simp [maxList]
  | cons head tail ih =>
      simp only [maxList, Nat.max_le]
      exact ⟨h head (by simp), ih (fun value hv => h value (by simp [hv]))⟩

/-- Full maximum correspondence through the actual list-to-Spt codec,
including arbitrary duplicates and unbounded natural names. This connects
Flapjack carriers and has no HOL declaration of its own. -/
theorem maxList_toNumSetHOL (values : List Nat) :
    maxList ((sptToAList (LoopToWord.toNumSetHOL values)).map Prod.fst) = maxList values := by
  have mem (key : Nat) :
      key ∈ (sptToAList (LoopToWord.toNumSetHOL values)).map Prod.fst ↔ key ∈ values :=
    (sptUnitKey_mem _ key).trans (sptLookup_toNumSetHOL_iff_mem key values)
  apply Nat.le_antisymm
  · apply maxList_le_of_members
    intro key hkey
    exact maxList_ge_of_mem values key ((mem key).mp hkey)
  · apply maxList_le_of_members
    intro key hkey
    exact maxList_ge_of_mem _ key ((mem key).mpr hkey)

/-- Production's accumulator scan and the reviewed source maximum have the
same value for all lists and initial maxima. Flapjack-only fold packaging. -/
private theorem foldMaximum (values : List Nat) (initial : Nat) :
    values.foldl max initial = max initial (maxList values) := by
  induction values generalizing initial with
  | nil => simp [maxList]
  | cons head tail ih =>
      simp only [List.foldl_cons, maxList, ih, Nat.max_assoc]

/-- The full production cutset-pair maximum equals the native maximum of its
existing Spt codec. No success, desired-maximum, uniqueness, bounds or tree
well-formedness premise is assumed. This is Flapjack carrier correspondence;
the complete Word-to-Stack frame and executed route remain separate. -/
theorem wordCutsetsCakeMaxVar_eq_cutsetsMaxHOL (sets : List Nat × List Nat) :
    wordCutsetsCakeMaxVar sets = cutsetsMaxHOL (wordCutsetsToHOL sets) := by
  simp only [wordCutsetsCakeMaxVar, cutsetsMaxHOL, wordCutsetsToHOL,
    maxList_toNumSetHOL, foldMaximum, Nat.zero_max]

end Flapjack
