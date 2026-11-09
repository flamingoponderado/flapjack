import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorRoots
import Flapjack.FiniteMap.MapKeys

/-! Store fields preserved by the actual garbage collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions Flapjack.Pancake

open Classical in
/-- Collection preserves allocation size, runtime buffer boundaries, the
handler, temporary 29, and heap length; it also leaves Globals present. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_IMP"
  (fmap_as_finite_support_relation := [store, store']) (words_as_type_indexed_bitvec)]
theorem wordGcFun_store_invariants {width : Nat} [NeZero width] (conf : Config)
    (roots moved : List (WordLocW width)) (memory memory' : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (store' : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (run : wordGcFun conf (roots, memory, domain, store) = some (moved, memory', store')) :
    store'.lookup .allocSize = store.lookup .allocSize ∧
    store'.lookup .handler = store.lookup .handler ∧
    store'.lookup .codeBuffer = store.lookup .codeBuffer ∧
    store'.lookup .codeBufferEnd = store.lookup .codeBufferEnd ∧
    store'.lookup .bitmapBuffer = store.lookup .bitmapBuffer ∧
    store'.lookup .bitmapBufferEnd = store.lookup .bitmapBufferEnd ∧
    store'.lookup (.temp 29) = store.lookup (.temp 29) ∧
    store'.lookup .heapLength = store.lookup .heapLength ∧
    (store'.lookup .globals).isSome = true := by
  have assum := wordGcFun_assum_of_success conf roots moved memory memory' domain store store' run
  have global : (store.lookup .globals).isSome = true := assum.1 .globals (by simp)
  simp only [wordGcFun] at run
  cases kind : conf.gcKind <;> simp only [kind] at run <;> (repeat' split at run)
  all_goals try { contradiction }
  all_goals simp only [Option.some.injEq, Prod.mk.injEq] at run
  all_goals obtain ⟨_, _, rfl⟩ := run
  all_goals simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL, global]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
