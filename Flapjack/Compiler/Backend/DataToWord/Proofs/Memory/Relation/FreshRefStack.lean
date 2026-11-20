module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshRefGc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshByteStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Submap

@[expose] public section

/-! Stack and reference invariants for HOL fresh reference allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- Old reference cells reachable after fresh array insertion were reachable before it; this supports HOL `new_ref_thm`. -/
theorem reachableRefs_freshValueArray_old (refs : Spt (BvlSem.Ref Value)) (values stack : List Value)
    (ptr n : Nat) (fresh : sptLookup ptr refs = none) (different : n ≠ ptr)
    (reachable : reachableRefs (values ++ .refPtr true ptr :: stack)
      (sptInsert ptr (.valueArray values) refs) n) :
    reachableRefs (values ++ stack) refs n := by
  have reach := reachableRefs_updateValueArray refs values stack ptr true n reachable
  obtain ⟨value, start, member, reference, path⟩ := reach
  rcases List.mem_append.mp member with inValues | inTail
  · exact ⟨value, start, List.mem_append_left _ inValues, reference, path⟩
  · rcases List.mem_cons.mp inTail with same | inStack
    · subst value
      have startEq : start = ptr := by simpa [getRefs] using reference
      subst start
      rcases Relation.ReflTransGen.cases_head path with same | ⟨next, edge, _⟩
      · exact False.elim (different same.symm)
      · simp [refEdge, fresh] at edge
    · exact ⟨value, start, List.mem_append_right _ inStack, reference, path⟩

/-- A directly observed value retains its invariant after fresh array allocation; used in HOL `new_ref_thm`. -/
theorem valueInv_freshValueArray {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr a : Nat) (values stack : List Value)
    (f tf : HolFiniteMapExact Nat Nat) (heap heap2 : ValueHeap width)
    (value : Value) (address : HeapAddress (WordLocW width))
    (fresh : sptLookup ptr refs = none) (freshMap : f.lookup ptr = none)
    (rel : heapStoreRel heap heap2)
    (related : valueInv conf value refs (address, f, tf, heap))
    (observed : (∃ index cell, sptLookup index (sptInsert ptr (.valueArray values) refs) = some cell ∧ findRef cell value) ∨ value ∈ stack) :
    valueInv conf value (sptInsert ptr (.valueArray values) refs)
      (address, f.update (ptr, a), restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray values) refs) stack), heap2) := by
  have unchanged : refBlockInv heap heap := ⟨by intro _ _ h; exact h.1, by intro _ _ h; exact h.1⟩
  have inserted := valueInv_insertValueArray conf value refs address f tf heap ptr values heap
    ⟨unchanged, related, by intro mem; simp [sptMem, sptDomain, fresh] at mem⟩
  have fsub : f.submap (f.update (ptr, a)) := by
    intro key result lookup
    have ne : key ≠ ptr := by intro same; subst key; rw [freshMap] at lookup; contradiction
    simpa [HolFiniteMapExact.update, FUPDATE, ne, Ne.symm ne] using lookup
  have extended := valueInv_submap conf _ f (f.update (ptr, a)) tf tf heap heap2 value address
    ⟨fsub, HolFiniteMapExact.submap_refl tf, rel, inserted⟩
  apply valueInv_tfRestrict conf value _ stack address (f.update (ptr, a)) tf heap2 _
  exact ⟨extended, fun stamp member => ⟨value, observed, member⟩, fun _ member => member⟩

/-- Existing reference cells retain their invariants under fresh allocation, as required by HOL `new_ref_thm`. -/
theorem bcRefInv_freshValueArray_other {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (be : Bool) (ptr index a : Nat) (values stack : List Value)
    (fresh : sptLookup ptr refs = none) (freshMap : f.lookup ptr = none) (different : index ≠ ptr)
    (rel : heapStoreRel heap heap2) (valid : bcRefInv conf index refs (f, tf, heap, be)) :
    bcRefInv conf index (sptInsert ptr (.valueArray values) refs)
      (f.update (ptr, a), restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray values) refs) stack), heap2, be) := by
  have lookupRefs : sptLookup index (sptInsert ptr (.valueArray values) refs) = sptLookup index refs :=
    sptLookup_sptInsert_ne ptr index _ refs different
  have cells : ∀ ptr cell, isDataElement cell → heapLookup ptr heap = some cell → heapLookup ptr heap2 = some cell := by
    intro ptr cell data found
    obtain ⟨xs, len, d, rfl⟩ := data
    exact (rel ptr ⟨xs, len, d, found⟩).trans found
  cases fLookup : f.lookup index with
  | none => simp [bcRefInv, fLookup] at valid
  | some mapped =>
    have fNew : (f.update (ptr, a)).lookup index = some mapped := by
      simpa [HolFiniteMapExact.update, FUPDATE, different, Ne.symm different] using fLookup
    cases refLookup : sptLookup index refs with
    | none => simp [bcRefInv, fLookup, refLookup] at valid
    | some cell =>
      cases cell with
      | valueArray items =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        obtain ⟨addresses, cell, related⟩ := valid
        refine ⟨addresses, cells mapped _ (by simp [isDataElement, refBlock]) cell, ?_⟩
        apply List.Forall₂.flip
        apply forall2_imp_member related.flip
        intro value addr member inv
        apply valueInv_freshValueArray conf refs ptr a values stack f tf heap heap2 value addr fresh freshMap rel inv
        exact Or.inl ⟨index, .valueArray items, by rw [lookupRefs, refLookup], member⟩
      | byteArray flag bytes =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        exact cells mapped _ (by simp [isDataElement, bytesRep]) valid
      | thunk mode value =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        obtain ⟨addr, cell, safe, inv⟩ := valid
        refine ⟨addr, cells mapped _ (by simp [isDataElement, thunkBlock]) cell, ?_, ?_⟩
        · intro evaluated
          exact destThunk_notThunk_insertValueArray value refs ptr values (safe evaluated)
        · apply valueInv_freshValueArray conf refs ptr a values stack f tf heap heap2 value addr fresh freshMap rel inv
          exact Or.inl ⟨index, .thunk mode value, by rw [lookupRefs, refLookup], rfl⟩
      | mutBlock tag finalised left value right =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        obtain ⟨gen, noStamp, addresses, cell, related⟩ := valid
        refine ⟨gen, ?_, addresses, cells mapped _ (by simp [isDataElement, blockRep]) cell, ?_⟩
        · intro unfinished ⟨stamp, domain, maps⟩
          obtain ⟨oldDomain, sameApply⟩ := restrictTimestampMap_domain_apply tf _ stamp domain
          exact noStamp unfinished ⟨stamp, oldDomain, sameApply.symm.trans maps⟩
        · apply List.Forall₂.flip
          apply forall2_imp_member related.flip
          intro item addr member inv
          apply valueInv_freshValueArray conf refs ptr a values stack f tf heap heap2 item addr fresh freshMap rel inv
          exact Or.inl ⟨index, .mutBlock tag finalised left value right, by rw [lookupRefs, refLookup], member⟩

/-- Fresh array allocation preserves the complete stack/reference relation of HOL `new_ref_thm`. -/
theorem bcStackRefInv_freshValueArray {width : Nat} [NeZero width] (conf : DataToWord.Config) (next : Nat)
    (values stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (rs roots : List (HeapAddress (WordLocW width))) (heap heap2 : ValueHeap width)
    (be : Bool) (ptr a : Nat) (lengths : values.length = rs.length)
    (fresh : sptLookup ptr refs = none) (oldNot : ¬ isSomeDataElement (heapLookup a heap))
    (rel : heapStoreRel heap heap2) (newCell : heapLookup a heap2 = some (refBlock rs))
    (valid : bcStackRefInv conf next (values ++ stack) refs (rs ++ roots, heap, be)) :
    bcStackRefInv conf next (values ++ .refPtr true ptr :: stack) (sptInsert ptr (.valueArray values) refs)
      (rs ++ .pointer a (.word 0) :: roots, heap2, be) := by
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, related, refsInv⟩ := valid
  have freshMap : f.lookup ptr = none := by
    cases found : f.lookup ptr with
    | none => rfl
    | some mapped =>
      obtain ⟨cell, lookup⟩ := domainF ptr ⟨mapped, found⟩
      simp [fresh] at lookup
  have preserved (index : Nat) (old : isSomeDataElement (heapLookup index heap)) :
      isSomeDataElement (heapLookup index heap2) := by rw [rel index old]; exact old
  have newData : isSomeDataElement (heapLookup a heap2) := by rw [newCell]; simp [isSomeDataElement, refBlock]
  have freshTarget : ∀ n, mapDomain f n → holFapply f n ≠ a := by
    intro n domain same
    apply oldNot
    rw [← same]
    exact injF.1 n domain
  have injF1 := freshBlock_timestampMap_injective f ptr a
    (fun p => isSomeDataElement (heapLookup p heap)) (fun p => isSomeDataElement (heapLookup p heap2))
    injF preserved newData freshTarget
  let newRefs := sptInsert ptr (.valueArray values) refs
  let newStack := values ++ .refPtr true ptr :: stack
  let keep := allTimestamps newRefs newStack
  let tf2 := restrictTimestampMap tf keep
  have injTf1 : mapInjInto tf2 (fun p => isSomeDataElement (heapLookup p heap2)) := by
    refine ⟨?_, ?_⟩
    · intro key domain
      obtain ⟨oldDomain, same⟩ := restrictTimestampMap_domain_apply tf keep key domain
      rw [same]
      exact preserved _ (injTf.1 key oldDomain)
    · intro x y ⟨domainX, domainY⟩ equal
      obtain ⟨oldX, sameX⟩ := restrictTimestampMap_domain_apply tf keep x domainX
      obtain ⟨oldY, sameY⟩ := restrictTimestampMap_domain_apply tf keep y domainY
      apply injTf.2 x y ⟨oldX, oldY⟩
      exact sameX.symm.trans (equal.trans sameY)
  have newLookup : (f.update (ptr, a)).lookup ptr = some a := by simp [HolFiniteMapExact.update, FUPDATE]
  have transformed : List.Forall₂ (fun value address => valueInv conf value newRefs
      (address, f.update (ptr, a), tf2, heap2)) (values ++ stack) (rs ++ roots) := by
    apply forall2_imp_member related
    intro value address member inv
    apply valueInv_freshValueArray conf refs ptr a values newStack f tf heap heap2 value address fresh freshMap rel inv
    right
    rcases List.mem_append.mp member with first | last
    · exact List.mem_append_left _ first
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ last)
  have prefixInv : List.Forall₂ (fun value address => valueInv conf value newRefs
      (address, f.update (ptr, a), tf2, heap2)) values rs := by
    have h := List.forall₂_take values.length transformed
    simpa [lengths] using h
  have tailInv : List.Forall₂ (fun value address => valueInv conf value newRefs
      (address, f.update (ptr, a), tf2, heap2)) stack roots := by
    have h := List.forall₂_drop values.length transformed
    simpa [lengths] using h
  refine ⟨f.update (ptr, a), tf2, injF1, ?_, injTf1, ?_, ?_, endian, ?_, ?_, ?_⟩
  · intro n domain
    by_cases same : n = ptr
    · subst n
      exact ⟨.valueArray values, sptLookup_sptInsert_same _ _ _⟩
    · obtain ⟨mapped, lookup⟩ := domain
      have old : f.lookup n = some mapped := by simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      obtain ⟨cell, found⟩ := domainF n ⟨mapped, old⟩
      exact ⟨cell, by simpa [newRefs, sptLookup_sptInsert_ne ptr n _ refs same] using found⟩
  · intro n domain
    obtain ⟨v, lookup⟩ := domain
    exact ((restrictTimestampMap_lookup_some tf keep n v).mp lookup).1
  · intro n domain
    exact nextBound n (restrictTimestampMap_domain_apply tf keep n domain).1
  · exact blocksUnique_newRef next refs values stack ptr unique
  · apply List.rel_append prefixInv
    apply List.Forall₂.cons
    · intro ck
      have refFound : sptLookup ptr newRefs = some (.valueArray values) := sptLookup_sptInsert_same _ _ _
      have applied : holFapply (f.update (ptr, a)) ptr = a := holFapply_of_lookup newLookup
      have head := ClockValueInv.refPtr true ck conf ptr newRefs (f.update (ptr, a)) tf2 heap2 ⟨a, newLookup⟩
        (by intro mode value; simp [refFound])
        (by intro tag finalised left child right h; simp [refFound] at h)
      simpa [applied, refFound, refPtrAnnot] using head
    · exact tailInv
  · intro n ⟨reachable, domain⟩
    by_cases same : n = ptr
    · subst n
      simp only [bcRefInv, newLookup, sptLookup_sptInsert_same]
      exact ⟨rs, newCell, prefixInv.flip⟩
    · obtain ⟨mapped, lookup⟩ := domain
      have oldLookup : f.lookup n = some mapped := by simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      have oldReach := reachableRefs_freshValueArray_old refs values stack ptr n fresh same reachable
      exact bcRefInv_freshValueArray_other conf refs f tf heap heap2 be ptr n a values newStack fresh freshMap same rel
        (refsInv n ⟨oldReach, ⟨mapped, oldLookup⟩⟩)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
