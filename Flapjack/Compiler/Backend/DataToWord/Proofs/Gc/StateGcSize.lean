import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateGcExecution
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordGcSize
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FrameRoots

/-! Heap limits and source sizing at the collector state boundary. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Flapjack infrastructure: the source and abstract heap limits agree when
their word-store encodings agree and both fit the supported word width. -/
theorem limitsInv_heapLimit_eq {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (heapLength : Option (WordLocW width))
    (stackLimit lengthSize limit : Nat) (hasFpOps hasFpTern : Bool)
    (good : goodDimindex width)
    (inv : limitsInv limits heapLength stackLimit lengthSize hasFpOps hasFpTern)
    (stored : heapLength = some (.word (StackRemove.bytesInWord width * BitVec.ofNat width limit)))
    (limitBound : (limit + 3) * (width / 8) + 1 < 2 ^ width) :
    limits.heapLimit = limit := by
  have same : BitVec.ofNat width (width / 8) * BitVec.ofNat width limits.heapLimit =
      BitVec.ofNat width (width / 8) * BitVec.ofNat width limit := by
    have eq := inv.2.2.2.1.symm.trans stored
    simpa [StackRemove.bytesInWord] using eq
  have words := congrArg BitVec.toNat same
  have sourceBound := inv.2.2.2.2.1
  rcases good with rfl | rfl <;>
    norm_num [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd] at words sourceBound limitBound ⊢ <;>
    omega

/-- Flapjack infrastructure: collection from the candidate 64-bit state
relation preserves that relation, and a failed request exceeds the source
heap limit for the actual input roots. The remaining source-level step is the
permutation relating flattened paired frames to extracted source frames. -/
theorem stateRel64_gc_preserved_size {C F : Type} (conf : Config) (l1 l2 requested : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (emptyLocals : source.locals = .ln) :
    ∃ moved memory store stack,
      target.gcFun (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) =
        some (moved, memory, store) ∧
      wordSemDecStack moved target.stack = some stack ∧
      store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      store.lookup .allocSize = target.store.lookup .allocSize ∧
      stateRel64 conf l1 l2 { source with space := 0 }
        { target with stack := stack, store := store, memory := memory } none locs ∧
      (target.store.lookup .allocSize = some (.word (gcAllocSize requested)) ∧
        WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested))
          { target with store := store } = some false ∧ conf.gcKind ≠ .none ∧
        DataSem.noThunksInRefs source.refs →
        ∀ roots2 dups,
          roots2.Perm (dups ++ (theGlobal source.global :: (flatStack source.stack target.stack).map Prod.fst)) →
          (∀ v, v ∈ dups → v ∈ theGlobal source.global :: (flatStack source.stack target.stack).map Prod.fst) →
          source.limits.heapLimit < (DataSem.sizeOfValues source.limits roots2 source.refs .ln).1 + requested) := by
  have gcEq := related.2.2.2.1
  have good := related.2.2.2.2.2.2.1
  have stackRel := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have limitsInv' := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have memoryRel := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, inv, limitBound, spaceBound⟩ := memoryRel
  have emptyInter : sptInter target.locals (adjustSet source.locals) = .ln := by
    rw [emptyLocals]
    cases target.locals <;> simp [adjustSet, sptFromAList, sptInter]
  have normalized : Memory.wordMlInv (heap, target.be, a, sp, sp1, gens) limit (holThe source.tstamps)
      conf source.refs ((theGlobal source.global, holFapply target.store .globals) :: flatStack source.stack target.stack) := by
    simpa [emptyInter, joinEnv] using inv
  have stored : target.store.lookup .heapLength =
      some (.word (StackRemove.bytesInWord 64 * BitVec.ofNat 64 limit)) := by
    obtain ⟨_, _, _, _, _, _, _, curr, other, _, _, _, _, _, _, _, stored, _⟩ := heapMem
    exact stored
  have limitEq := limitsInv_heapLimit_eq source.limits (target.store.lookup .heapLength)
    target.stackLimit conf.lenSize limit conf.hasFpOps conf.hasFpTern good limitsInv' stored limitBound
  obtain ⟨moved, memory, store, stack, run, decoded, temp, alloc, preserved⟩ :=
    stateRel64_gc_preserved conf l1 l2 source target locs related emptyLocals
  refine ⟨moved, memory, store, stack, run, decoded, temp, alloc, preserved, ?_⟩
  rintro ⟨allocated, failed, active, noThunks⟩
  obtain ⟨moved1, memory1, store1, wordRun, sizeBound⟩ :=
    wordGcFun_failed_sourceSize source.limits conf (theGlobal source.global) (flatStack source.stack target.stack)
      source.refs heap target.be a sp sp1 limit (holThe source.tstamps) requested gens target.store target.memory
      target.mdomain target good limitsInv'.2.2.1 limitEq noThunks heapMem normalized
  have run1 : target.gcFun (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) =
      some (moved1, memory1, store1) := by
    rw [gcEq, ← flatStack_values_eq_encStack source.stack target.stack stackRel]
    exact wordRun
  rw [run] at run1
  cases run1
  exact sizeBound ⟨allocated, failed, active⟩


/-- Flapjack infrastructure: collection from the candidate state relation
preserves that relation and, after failed allocation, bounds source sizing of
the actual extracted stack and global roots, including duplicate roots. This
uses Flapjack's candidate code/oracle relation and is not yet a HOL port. -/
theorem stateRel64_gc_gen {C F : Type} (conf : Config) (l1 l2 requested : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (emptyLocals : source.locals = .ln) :
    ∃ moved memory store stack,
      target.gcFun (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) =
        some (moved, memory, store) ∧
      wordSemDecStack moved target.stack = some stack ∧
      store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      store.lookup .allocSize = target.store.lookup .allocSize ∧
      stateRel64 conf l1 l2 { source with space := 0 }
        { target with stack := stack, store := store, memory := memory } none locs ∧
      (target.store.lookup .allocSize = some (.word (gcAllocSize requested)) ∧
        WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested))
          { target with store := store } = some false ∧ conf.gcKind ≠ .none ∧
        DataSem.noThunksInRefs source.refs →
        ∀ roots2 dups,
          roots2.Perm (dups ++ (source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global])) →
          (∀ v, v ∈ dups → v ∈ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) →
          source.limits.heapLimit < (DataSem.sizeOfValues source.limits roots2 source.refs .ln).1 + requested) := by
  obtain ⟨moved, memory, store, stack, run, decoded, temp, alloc, preserved, bound⟩ :=
    stateRel64_gc_preserved_size conf l1 l2 requested source target locs related emptyLocals
  refine ⟨moved, memory, store, stack, run, decoded, temp, alloc, preserved, ?_⟩
  intro failed roots2 dups perm duplicates
  have framePerm := flatStack_values_perm source.stack target.stack related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have rootsPerm : (theGlobal source.global :: (flatStack source.stack target.stack).map Prod.fst).Perm
      (source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) :=
    (framePerm.cons _).trans (List.perm_append_singleton _ _).symm
  apply bound failed roots2 dups
  · exact perm.trans (rootsPerm.symm.append_left dups)
  · intro value member
    exact rootsPerm.mem_iff.mpr (duplicates value member)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
