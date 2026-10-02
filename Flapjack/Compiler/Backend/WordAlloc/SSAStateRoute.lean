import Flapjack.Misc.Sptree.Enumeration
import Flapjack.Compiler.Backend.WordAlloc.SSASetup
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Compiler.Backend.WordAlloc.KeyMapRoute

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

/-- Native cutset restriction for the production list facade. The right tree
contains only unit values; native intersection retains the left map values.
This is Flapjack API infrastructure with no independent HOL declaration. -/
def ssaRestrictExecutable (entries : List (Nat × Nat)) (names : List Nat) :
    List (Nat × Nat) :=
  sptToAList (sptInter (sptFromAList entries)
    (sptFromAList (names.map (fun name => (name, ())))) )

/-- The cutset list codec records precisely membership, including repetitions.
Flapjack codec infrastructure rather than a separate HOL port. -/
theorem ssaCutsetLookup (names : List Nat) (key : Nat) :
    sptLookup key (sptFromAList (names.map (fun name => (name, ())))) =
      if key ∈ names then some () else none := by
  rw [sptLookup_sptFromAList]
  induction names with
  | nil => simp [sptAListLookup]
  | cons name names ih =>
    by_cases same : key = name
    · subst key; simp [sptAListLookup]
    · simp [sptAListLookup, same, ih]

/-- Native restriction preserves exactly the first-match input value on cutset
keys and removes every other key, without any input-map validity premise. -/
theorem ssaRestrictExecutableLookup (entries : List (Nat × Nat))
    (names : List Nat) (key : Nat) :
    sptAListLookup key (ssaRestrictExecutable entries names) =
      if key ∈ names then sptAListLookup key entries else none := by
  have decoded := sptLookup_sptFromAList_sptToAList key
    (sptInter (sptFromAList entries)
      (sptFromAList (names.map (fun name => (name, ())))))
  rw [sptLookup_sptFromAList] at decoded
  rw [ssaRestrictExecutable, decoded, sptLookup_sptInterCases,
    ssaCutsetLookup, sptLookup_sptFromAList]
  by_cases member : key ∈ names
  · simp only [if_pos member]
    cases sptAListLookup key entries <;> rfl
  · simp only [if_neg member]
    cases sptAListLookup key entries <;> rfl

/-- Execute the reviewed reconciliation producer and decode its parallel moves.
The producer has only Skip/Move1 outputs, carrying no words. Width one supplies
its positive word index at this generic production API boundary; the theorem
below proves full result reconstruction at every positive width. This codec is
Flapjack infrastructure, not a separately tagged HOL declaration. -/
def ssaReconcileMovesExecutable (source target : List (Nat × Nat)) (names : List Nat) :
    List (Nat × Nat) :=
  match ssaReconcile (width := 1) (sptFromAList source) (sptFromAList target)
      (WordAlloc.numSetToExact names) with
  | .move _ moves => moves
  | _ => []

/-- Complete native reconciliation result is recovered from the executed codec
uniformly at every positive word width. No successful-result premise or assumed
output relation is needed. The native producer returns only Skip/Move1. -/
theorem ssaReconcileMovesExecutableCorresponds {width : Nat} [NeZero width]
    (source target : List (Nat × Nat)) (names : List Nat) :
    ssaReconcile (width := width) (sptFromAList source) (sptFromAList target)
        (WordAlloc.numSetToExact names) =
      let moves := ssaReconcileMovesExecutable source target names
      if moves = [] then .skip else .move 1 moves := by
  unfold ssaReconcileMovesExecutable ssaReconcile
  dsimp only
  split <;> simp_all

/-- Execute native list renaming and its complete Move0 producer in one map
codec boundary. The word-free Move payload permits a width-one API instance;
full reconstruction at every positive width is proved below. Original source
reads occur before the sequential renaming, including repeated names.
Flapjack production codec infrastructure, with no independent HOL declaration. -/
def ssaListNextVarRenameMoveExecutable (entries : List (Nat × Nat)) (next : Nat)
    (names : List Nat) : List (Nat × Nat) × List (Nat × Nat) × Nat :=
  let (program, tree, next) :=
    listNextVarRenameMove (width := 1) (sptFromAList entries) next names
  let moves := match program with
    | .move _ moves => moves
    | _ => []
  (moves, sptToAList tree, next)

/-- Complete native list-renaming output reconstruction, independent of word
width and unrestricted in keys, counters and duplicate input bindings. The
full ordered decoder and every lookup are established without assumed output
relations. This theorem is Flapjack codec infrastructure. -/
theorem ssaListNextVarRenameMoveExecutableCorresponds {width : Nat} [NeZero width]
    (entries : List (Nat × Nat)) (next : Nat) (names : List Nat) :
    let native := listNextVarRenameMove (width := width) (sptFromAList entries) next names
    let executed := ssaListNextVarRenameMoveExecutable entries next names
    native.1 = .move 0 executed.1 ∧ executed.2.2 = native.2.2 ∧
    executed.2.1 = sptToAList native.2.1 ∧
    ∀ key, sptAListLookup key executed.2.1 = sptLookup key native.2.1 := by
  unfold ssaListNextVarRenameMoveExecutable listNextVarRenameMove
  obtain ⟨registers, tree, counter⟩ := listNextVarRename names (sptFromAList entries) next
  simp only
  refine ⟨True.intro, True.intro, True.intro, ?_⟩
  intro key
  simpa only [sptLookup_sptFromAList] using
    sptLookup_sptFromAList_sptToAList key tree

end Flapjack.Compiler.Backend.WordAlloc
