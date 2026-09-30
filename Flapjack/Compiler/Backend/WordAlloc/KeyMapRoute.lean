import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyMaps

namespace Flapjack.WordAlloc

/-- Flapjack list codec for unit-valued numeric trees. Lists at the compiler
boundary describe keys; the exact tree owns traversal and collision behavior.
This representation codec has no independent HOL declaration. -/
def numSetToExact (names : List Nat) : Spt Unit :=
  sptFromAList (names.map (fun name => (name, ())))

/-- Decode exact numeric-tree keys in HOL's mixed traversal order. This is
Flapjack boundary infrastructure, not a separately tagged HOL definition. -/
def numSetFromExact (names : Spt Unit) : List Nat :=
  (sptToAList names).map Prod.fst

/-- Executable key renaming uses the reviewed HOL operation. Unit payloads
make collisions ordinary set collisions; no injectivity premise is needed. -/
def applyNummapKeyExecutable (f : Nat → Nat) (names : List Nat) : List Nat :=
  numSetFromExact (applyNummapKey f (numSetToExact names))

private theorem toAList_mem (tree : Spt Unit) (key : Nat) :
    (key, ()) ∈ sptToAList tree ↔ sptLookup key tree = some () := by
  constructor
  · intro h
    rcases sptFoldi_mem_address tree 0 [] key () h with h | ⟨localKey, heq, hlookup⟩
    · simp at h
    · have : key = localKey := by simpa [sptAcc_eq, lrNext] using heq
      simpa [this] using hlookup
  · intro h
    simpa [sptToAList, sptAcc_eq, lrNext] using sptFoldi_lookup_mem tree 0 [] key () h

/-- The decoder exposes precisely the exact tree domain, on unrestricted
trees. Cross-carrier infrastructure; no standalone HOL original. -/
theorem mem_numSetFromExact (tree : Spt Unit) (key : Nat) :
    key ∈ numSetFromExact tree ↔ sptDomain tree key := by
  simp only [numSetFromExact, List.mem_map]
  constructor
  · rintro ⟨⟨source, value⟩, hmem, heq⟩
    cases value
    change source = key at heq
    subst source
    simp [sptDomain, (toAList_mem tree key).mp hmem]
  · intro h
    obtain ⟨value, hlookup⟩ := (sptMem_iff_lookup key tree).mp h
    cases value
    exact ⟨(key, ()), (toAList_mem tree key).mpr hlookup, rfl⟩

/-- Encoding preserves membership even for duplicate input keys. This is a
Flapjack codec law, not a theorem declared in the HOL source. -/
theorem domain_numSetToExact (names : List Nat) (key : Nat) :
    sptDomain (numSetToExact names) key ↔ key ∈ names := by
  induction names with
  | nil => simp [numSetToExact, sptFromAList, sptDomain]
  | cons name names ih =>
      by_cases h : key = name
      · subst key
        simp [numSetToExact, sptFromAList, sptDomain, sptLookup_sptInsert_same]
      · simpa [numSetToExact, sptFromAList, sptDomain,
          sptLookup_sptInsert_ne name key () _ h, h] using ih

/-- The executed list boundary has the full image-domain behavior, including
collisions. This transports the reviewed HOL theorem through Flapjack codecs
and therefore has no separate HOL original. -/
theorem mem_applyNummapKeyExecutable (f : Nat → Nat) (names : List Nat) (key : Nat) :
    key ∈ applyNummapKeyExecutable f names ↔
      ∃ source, source ∈ names ∧ f source = key := by
  rw [applyNummapKeyExecutable, mem_numSetFromExact, applyNummapKeyDomain]
  simp only [domain_numSetToExact]

/-- Executed list-pair codec for the exact paired operation. Flapjack boundary
infrastructure; the compiler uses this for return, allocation and FFI cutsets. -/
def applyNummapsKeyExecutable (f : Nat → Nat) (names : List Nat × List Nat) :
    List Nat × List Nat :=
  let mapped := applyNummapsKey f (numSetToExact names.1, numSetToExact names.2)
  (numSetFromExact mapped.1, numSetFromExact mapped.2)

/-- Unconditional whole-result equivalence with the two reviewed single-tree
routes. This Flapjack codec law has no separate HOL original. -/
theorem applyNummapsKeyExecutable_eq (f : Nat → Nat) (names : List Nat × List Nat) :
    applyNummapsKeyExecutable f names =
      (applyNummapKeyExecutable f names.1, applyNummapKeyExecutable f names.2) := rfl

end Flapjack.WordAlloc
