import Flapjack.Misc.Sptree.Enumeration
import Flapjack.Compiler.Backend.WordAlloc.SSASetup
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Executed first-match list codec for the reviewed native fresh-name operation.
The native tree owns updates and its traversal owns output order. This API
codec is Flapjack infrastructure with no separate HOL declaration. -/
def ssaNextVarRenameExecutable (name : Nat) (entries : List (Nat × Nat)) (next : Nat) :
    Nat × List (Nat × Nat) × Nat :=
  let (name,tree,next) := nextVarRename name (sptFromAList entries) next
  (name,sptToAList tree,next)

/-- Executed forced renaming uses the reviewed native operation, including
repeated keys and arbitrary first-match input lists. No separate HOL original. -/
def ssaForceRenameExecutable (renamings entries : List (Nat × Nat)) : List (Nat × Nat) :=
  sptToAList (forceRename renamings (sptFromAList entries))

/-- Enumerate the actual native map in its traversal order, rather than the
association list's insertion order. Flapjack codec infrastructure only. -/
def ssaMapKeysExecutable (entries : List (Nat × Nat)) : List Nat :=
  (sptToAList (sptFromAList entries)).map Prod.fst

/-- The whole fresh-name output, counter and every map lookup agree with the
native producer, without an input uniqueness or success premise. -/
theorem ssaNextVarRenameExecutableCorresponds (name : Nat)
    (entries : List (Nat × Nat)) (next : Nat) :
    let native := nextVarRename name (sptFromAList entries) next
    let executed := ssaNextVarRenameExecutable name entries next
    executed.1 = native.1 ∧ executed.2.2 = native.2.2 ∧
    executed.2.1 = sptToAList native.2.1 ∧
    ∀ key, sptAListLookup key executed.2.1 = sptLookup key native.2.1 := by
  simp only [ssaNextVarRenameExecutable,nextVarRename]
  refine ⟨True.intro,True.intro,True.intro,?_⟩
  intro key
  simpa only [sptLookup_sptFromAList] using
    sptLookup_sptFromAList_sptToAList key (sptInsert name next (sptFromAList entries))

/-- Full forced-map lookup and exact ordered decoder correspondence. -/
theorem ssaForceRenameExecutableCorresponds (renamings entries : List (Nat × Nat)) :
    ssaForceRenameExecutable renamings entries =
      sptToAList (forceRename renamings (sptFromAList entries)) ∧
    ∀ key, sptAListLookup key (ssaForceRenameExecutable renamings entries) =
      sptLookup key (forceRename renamings (sptFromAList entries)) := by
  refine ⟨rfl,?_⟩
  intro key
  simpa only [ssaForceRenameExecutable,sptLookup_sptFromAList] using
    sptLookup_sptFromAList_sptToAList key (forceRename renamings (sptFromAList entries))

end Flapjack.Compiler.Backend.WordAlloc
