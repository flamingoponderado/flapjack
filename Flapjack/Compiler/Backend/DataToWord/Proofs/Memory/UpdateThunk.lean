module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.UpdateCons
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ThunkHeap
public import Flapjack.Misc.UpdateList

@[expose] public section

/-!
# Updating an unevaluated thunk

Counterparts of `v_inv_Thunk_insert_lemma`, `v_inv_Thunk_insert`,
`update_thunk_thm` and `memory_rel_UpdateThunk_NotEvaluated`/`_Evaluated` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Inserting a thunk over a thunk keeps every non-thunk value a non-thunk.
Flapjack proof infrastructure. -/
theorem destThunk_notThunk_insertThunk (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ptr : Nat)
    (mode ev : AstHOL.ThunkMode) (old h : Flapjack.Compiler.Backend.DataSem.Value)
    (found : sptLookup ptr refs = some (.thunk mode old))
    (notThunk : destThunk value refs = .notThunk) :
    destThunk value (sptInsert ptr (.thunk ev h) refs) = .notThunk := by
  cases value with
  | refPtr bit index =>
    by_cases same : index = ptr
    · subst index
      cases bit <;> simp [destThunk, found] at notThunk
    · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs same] using notThunk
  | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]

/-- The clocked value invariant survives replacing an unevaluated thunk by a
new thunk, both in the references and in its heap cell. Flapjack proof
infrastructure for `v_inv_Thunk_insert_lemma`. -/
theorem clockValueInv_thunkInsert {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ev : AstHOL.ThunkMode)
    (h : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (ptr : Nat) (v : Flapjack.Compiler.Backend.DataSem.Value)
    (y q : HeapAddress (WordLocW width))
    (inj : mapInjInto f (fun a => isSomeDataElement (heapLookup a heap)))
    (dom : mapDomain f ptr)
    (found : sptLookup ptr refs = some (.thunk .notEvaluated v))
    (oldCell : heapLookup (holFapply f ptr) heap = some (thunkBlock .notEvaluated y))
    (evaluated : ev = .evaluated → destThunk h refs = .notThunk)
    (newCell : heapLookup (holFapply f ptr) heap2 = some (thunkBlock ev q))
    (kept : ∀ m x, m ≠ holFapply f ptr ∧ heapLookup m heap = some x → heapLookup m heap2 = some x)
    (hInv : valueInv conf h refs (q, f, tf, heap)) :
    ∀ ck v1 x, ClockValueInv ck conf v1 refs (x, f, tf, heap) →
      ClockValueInv ck conf v1 (sptInsert ptr (.thunk ev h) refs) (x, f, tf, heap2) := by
  have notHere : ∀ m cell, heapLookup m heap = some cell → cell ≠ thunkBlock .notEvaluated y →
      heapLookup m heap2 = some cell := by
    intro m cell lookup different
    apply kept m cell ⟨?_, lookup⟩
    intro same
    subst same
    rw [oldCell] at lookup
    exact different (Option.some.inj lookup).symm
  have otherAddr : ∀ n, mapDomain f n → n ≠ ptr → holFapply f n ≠ holFapply f ptr := by
    intro n domain different equal
    exact different (inj.2 n ptr ⟨domain, dom⟩ equal)
  intro ck
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro v1 x related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i _ f tf heap2 small
    | numberBig _ _ i address _ _ _ _ large cell =>
      refine .numberBig ck conf i address _ f tf heap2 large (notHere _ _ cell ?_)
      simp [bignumRep, thunkBlock]
    | word64 _ _ word address _ _ _ _ cell =>
      refine .word64 ck conf word address _ f tf heap2 (notHere _ _ cell ?_)
      unfold word64Rep
      split <;> simp [thunkBlock]
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n _ f tf heap2
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      have different : n ≠ ptr := by
        intro same
        subst same
        exact notThunk _ _ found
      have lookupEq : sptLookup n (sptInsert ptr (.thunk ev h) refs) = sptLookup n refs :=
        sptLookup_sptInsert_ne ptr n _ refs different
      have result := ClockValueInv.refPtr bit ck conf n (sptInsert ptr (.thunk ev h) refs) f tf heap2 domain
        (by intro mode body; rw [lookupEq]; exact notThunk mode body)
        (by intro tag finalised left body right lookup; rw [lookupEq] at lookup
            exact notMut tag finalised left body right lookup)
      rwa [lookupEq] at result
    | refPtrThunk _ _ mode n body addr _ _ _ _ cellFound cellEvaluated domain cell recursive =>
      by_cases same : n = ptr
      · subst n
        exact .refPtrThunk ck conf ev ptr h q _ f tf heap2 (sptLookup_sptInsert_same _ _ _)
          (fun e => destThunk_notThunk_insertThunk h refs ptr .notEvaluated ev v h found (evaluated e))
          domain newCell (fun positive => ih (ck - 1) (by omega) h q (hInv (ck - 1)))
      · have lookupEq : sptLookup n (sptInsert ptr (.thunk ev h) refs) = sptLookup n refs :=
          sptLookup_sptInsert_ne ptr n _ refs same
        refine .refPtrThunk ck conf mode n body addr _ f tf heap2 (by rw [lookupEq]; exact cellFound)
          (fun e => destThunk_notThunk_insertThunk body refs ptr .notEvaluated ev v h found (cellEvaluated e))
          domain (kept _ _ ⟨otherAddr n domain same, cell⟩) ?_
        intro positive
        exact ih (ck - 1) (by omega) body addr (recursive positive)
    | refPtrThunkInlined _ _ n body addr _ _ _ _ cellFound notThunk recursive =>
      have different : n ≠ ptr := by
        intro same
        subst same
        rw [found] at cellFound
        cases cellFound
      have lookupEq : sptLookup n (sptInsert ptr (.thunk ev h) refs) = sptLookup n refs :=
        sptLookup_sptInsert_ne ptr n _ refs different
      refine .refPtrThunkInlined ck conf n body x _ f tf heap2 (by rw [lookupEq]; exact cellFound)
        (destThunk_notThunk_insertThunk body refs ptr .notEvaluated ev v h found notThunk) ?_
      intro positive
      exact ih (ck - 1) (by omega) body x (recursive positive)
    | blockNil _ _ stamp tag values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag values _ f tf heap2 empty bound zero
    | blockCons _ _ stamp tag address values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag address values xs _ f tf heap2 nonempty ?_ timestamp
        (notHere _ _ cell (by simp [blockRep, thunkBlock]))
      intro positive
      apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
      apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
      intro child addr childInv
      exact ih (ck - 1) (by omega) child addr childInv

/-- HOL `v_inv_Thunk_insert_lemma`. `INJ (FAPPLY f) (FDOM f) {a | ...}` is
`mapInjInto`, `ptr ∈ FDOM f` is `mapDomain f ptr`, `f ' ptr` is
`holFapply f ptr` and `v_inv_ck` is `ClockValueInv`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_Thunk_insert_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_thunkInsert_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ev : AstHOL.ThunkMode)
    (h : Flapjack.Compiler.Backend.DataSem.Value)
    (heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
    ∀ (ck : Nat) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ptr : Nat)
      (v : Flapjack.Compiler.Backend.DataSem.Value) (y q : HeapAddress (WordLocW width)),
      valueInv conf v1 refs (x, f, tf, heap) ∧
          mapInjInto f (fun a => isSomeDataElement (heapLookup a heap)) ∧ mapDomain f ptr ∧
          sptLookup ptr refs = some (.thunk .notEvaluated v) ∧
          heapLookup (holFapply f ptr) heap = some (thunkBlock .notEvaluated y) ∧
          valueInv conf v refs (y, f, tf, heap) ∧
          (ev = .evaluated → destThunk h refs = .notThunk) ∧
          heapStore (holFapply f ptr) [thunkBlock ev q] heap = (heap2, true) ∧
          heapLookup (holFapply f ptr) heap2 = some (thunkBlock ev q) ∧
          (∀ m x, m ≠ holFapply f ptr ∧ heapLookup m heap = some x → heapLookup m heap2 = some x) ∧
          valueInv conf h refs (q, f, tf, heap) →
        ClockValueInv ck conf v1 (sptInsert ptr (.thunk ev h) refs) (x, f, tf, heap2) := by
  rintro ck v1 refs x f tf heap ptr v y q
    ⟨inv, inj, dom, found, oldCell, _, evaluated, _, newCell, kept, hInv⟩
  exact clockValueInv_thunkInsert conf ev h refs f tf heap heap2 ptr v y q inj dom found oldCell
    evaluated newCell kept hInv ck v1 x (inv ck)

/-- HOL `v_inv_Thunk_insert`, the unclocked form of
`v_inv_Thunk_insert_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_Thunk_insert"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_thunkInsert {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ptr : Nat)
    (v : Flapjack.Compiler.Backend.DataSem.Value) (y : HeapAddress (WordLocW width))
    (ev : AstHOL.ThunkMode) (h : Flapjack.Compiler.Backend.DataSem.Value) (q : HeapAddress (WordLocW width))
    (heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
    valueInv conf v1 refs (x, f, tf, heap) ∧
        mapInjInto f (fun a => isSomeDataElement (heapLookup a heap)) ∧ mapDomain f ptr ∧
        sptLookup ptr refs = some (.thunk .notEvaluated v) ∧
        heapLookup (holFapply f ptr) heap = some (thunkBlock .notEvaluated y) ∧
        valueInv conf v refs (y, f, tf, heap) ∧
        (ev = .evaluated → destThunk h refs = .notThunk) ∧
        heapStore (holFapply f ptr) [thunkBlock ev q] heap = (heap2, true) ∧
        heapLookup (holFapply f ptr) heap2 = some (thunkBlock ev q) ∧
        (∀ m x, m ≠ holFapply f ptr ∧ heapLookup m heap = some x → heapLookup m heap2 = some x) ∧
        valueInv conf h refs (q, f, tf, heap) →
      valueInv conf v1 (sptInsert ptr (.thunk ev h) refs) (x, f, tf, heap2) := by
  intro valid ck
  exact valueInv_thunkInsert_lemma conf ev h heap2 ck v1 refs x f tf heap ptr v y q valid

/-- A heap lookup at a cell boundary returns that cell. Flapjack heap
infrastructure. -/
theorem heapLookup_cell_here {α β : Type} (pre post : List (HeapElement α β)) (cell : HeapElement α β) :
    heapLookup (heapLength pre) (pre ++ cell :: post) = some cell := by
  induction pre with
  | nil => simp [heapLength, heapLookup]
  | cons head tail ih =>
    have positive : 0 < elLength head := by cases head <;> simp [elLength]
    change heapLookup (elLength head + heapLength tail) (head :: (tail ++ cell :: post)) = _
    simp only [heapLookup, show ¬ elLength head + heapLength tail = 0 by omega, ↓reduceIte,
      show ¬ elLength head + heapLength tail < elLength head by omega]
    simpa using ih

/-- Replacing one mutable data cell by another of the same size preserves
the complete garbage-collector invariant, including the generational
partition. Flapjack heap infrastructure. -/
theorem gcKindInv_refCellReplace {α β : Type} (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (pre post : List (HeapElement α (HeapTag × β))) (old new : HeapElement α (HeapTag × β))
    (a sp sp1 : Nat) (gens : GcCombined.GenState) (sameLength : elLength old = elLength new)
    (dataIff : isDataElement old ↔ isDataElement new) (refOld : isRef old) (refNew : isRef new)
    (valid : gcKindInv conf a sp sp1 gens (pre ++ [old] ++ post)) :
    gcKindInv conf a sp sp1 gens (pre ++ [new] ++ post) := by
  cases kind : conf.gcKind with
  | none => simpa [gcKindInv, kind] using valid
  | simple => simpa [gcKindInv, kind] using valid
  | generational sizes =>
    simp only [gcKindInv, kind] at valid ⊢
    obtain ⟨gensOk, first, second, split, noRefs, refs⟩ := valid
    obtain ⟨heapEq, lengthEq⟩ := heapSplit_decomposition _ (a + sp + sp1) first second split
    have afterBoundary : a + sp + sp1 ≤ heapLength pre := by
      by_contra notAfter
      have before : heapLength pre < heapLength first := by omega
      have found : heapLookup (heapLength pre) (first ++ second) = some old := by
        rw [← heapEq]
        simpa [List.append_assoc] using heapLookup_cell_here pre post old
      exact noRefs old (heapLookup_mem_beforePrefix first second _ old before found) refOld
    have self (heap : List (HeapElement α (HeapTag × β))) :
        List.Forall₂ (fun left right => HeapCellLayout left right ∧ (isRef left ↔ isRef right)) heap heap := by
      induction heap with
      | nil => exact .nil
      | cons head tail ih => exact .cons ⟨⟨rfl, Iff.rfl⟩, Iff.rfl⟩ ih
    have layout : List.Forall₂ (fun left right => HeapCellLayout left right ∧ (isRef left ↔ isRef right))
        (pre ++ [old] ++ post) (pre ++ [new] ++ post) :=
      List.rel_append (List.rel_append (self pre)
        (.cons ⟨⟨sameLength, dataIff⟩, ⟨fun _ => refNew, fun _ => refOld⟩⟩ .nil)) (self post)
    obtain ⟨first2, second2, split2, firstLayout, secondLayout⟩ :=
      heapSplit_relation (fun h : HeapCellLayout _ _ ∧ (_ ↔ _) => h.1.1) layout (a + sp + sp1) first second split
    refine ⟨?_, first2, second2, split2, ?_, ?_⟩
    · cases gens with
      | genState _ starts =>
        refine ⟨gensOk.1, ?_⟩
        intro start member
        obtain ⟨left, right, leftSplit, pointers⟩ := gensOk.2 start member
        have bound : start ≤ heapLength pre := (gensOk.1 start member).trans (by omega)
        obtain ⟨right2, split3⟩ := heapSplit_before_replacement pre post old new start bound left right
          (by simpa [List.append_assoc] using leftSplit)
        exact ⟨left, right2, by simpa [List.append_assoc] using split3, pointers⟩
    · exact forall_mem_of_forall₂ firstLayout (fun h noRef ref => noRef (h.2.mpr ref)) noRefs
    · exact forall_mem_of_forall₂ secondLayout (fun h ref => h.2.mp ref) refs

/-- Core of `update_thunk_thm`, also exposing the old thunk cell. Flapjack
proof infrastructure. -/
theorem updateThunkCore {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (h : Flapjack.Compiler.Backend.DataSem.Value) (ptr : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit ts : Nat)
    (v : Flapjack.Compiler.Backend.DataSem.Value) (ev : AstHOL.ThunkMode)
    (valid : absMlInv conf (h :: .refPtr false ptr :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit ts ∧
      sptLookup ptr refs = some (.thunk .notEvaluated v) ∧ (ev = .evaluated → destThunk h refs = .notThunk)) :
    ∃ (p : Nat) (r : HeapAddress (WordLocW width)) (roots2 : List (HeapAddress (WordLocW width)))
      (y : HeapAddress (WordLocW width)) (heap2 : ValueHeap width),
      roots = r :: .pointer p (.word 0) :: roots2 ∧ heapLookup p heap = some (thunkBlock .notEvaluated y) ∧
      heapStore p [thunkBlock ev r] heap = (heap2, true) ∧
      absMlInv conf (h :: .refPtr false ptr :: stack) (sptInsert ptr (.thunk ev h) refs)
        (roots, heap2, be, a, sp, sp1, gens) limit ts := by
  obtain ⟨⟨rootsValid, heapValid, gcValid, unused, stackInv⟩, found, evaluated⟩ := valid
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, related, refsInv⟩ := stackInv
  obtain ⟨pre0, rr, rest0, rootsEq0, preRel0, hRel, restRel0⟩ :=
    forall2_split_head [] h (.refPtr false ptr :: stack) roots related
  cases preRel0
  obtain ⟨pre1, ptrRoot, roots2, restEq, preRel1, ptrRel, tailRel⟩ :=
    forall2_split_head [] (.refPtr false ptr) stack rest0 restRel0
  cases preRel1
  simp only [List.nil_append] at rootsEq0 restEq
  subst restEq
  subst rootsEq0
  obtain ⟨p, pLookup, ptrEq⟩ : ∃ p, f.lookup ptr = some p ∧ ptrRoot = .pointer p (.word 0) := by
    have ptrRel0 := ptrRel 0
    cases ptrRel0 with
    | refPtr _ _ _ _ _ _ _ _ _ notThunk _ => exact absurd found (notThunk _ _)
    | refPtrThunk _ _ _ _ _ _ _ _ _ _ _ _ domain _ _ =>
      obtain ⟨q, qLookup⟩ := domain
      exact ⟨q, qLookup, by rw [holFapply_of_lookup qLookup]⟩
    | refPtrThunkInlined _ _ _ _ _ _ _ _ _ cellFound _ _ =>
      rw [found] at cellFound
      cases cellFound
  have reachable : reachableRefs (h :: .refPtr false ptr :: stack) refs ptr :=
    ⟨.refPtr false ptr, ptr, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
  have ptrInv := refsInv ptr ⟨reachable, ⟨p, pLookup⟩⟩
  simp only [bcRefInv, pLookup, found] at ptrInv
  obtain ⟨y, yCell, _, _⟩ := ptrInv
  have fptr : holFapply f ptr = p := holFapply_of_lookup pLookup
  obtain ⟨heap2, stored, newLookup, lenEq, fwdEq, members, dataEq, kept⟩ :=
    heapStore_thunkBlock_source p heap y rr ev yCell
  let newRefs := sptInsert ptr (.thunk ev h) refs
  let newStack := h :: .refPtr false ptr :: stack
  let tf2 := restrictTimestampMap tf (allTimestamps newRefs newStack)
  have transport : ∀ value address, valueInv conf value refs (address, f, tf, heap) →
      ((∃ index cell, sptLookup index newRefs = some cell ∧ findRef cell value) ∨ value ∈ newStack) →
      valueInv conf value newRefs (address, f, tf2, heap2) := by
    intro value address rel obs
    have moved : valueInv conf value newRefs (address, f, tf, heap2) := fun ck =>
      clockValueInv_thunkInsert conf ev h refs f tf heap heap2 ptr v y rr injF ⟨p, pLookup⟩ found
        (by rw [fptr]; exact yCell) evaluated (by rw [fptr]; exact newLookup)
        (by rw [fptr]; exact kept) hRel ck value address (rel ck)
    exact valueInv_tfRestrict conf value _ newStack address f tf heap2 _
      ⟨moved, fun stamp member => ⟨value, obs, member⟩, fun _ member => member⟩
  refine ⟨p, rr, roots2, y, heap2, by rw [ptrEq], yCell, stored, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q w member
    exact (dataEq q).mpr (rootsValid q w member)
  · refine ⟨lenEq.trans heapValid.1, fwdEq.trans heapValid.2.1, ?_⟩
    intro xs len data q w ⟨member, qMember⟩
    apply (dataEq q).mpr
    rcases members xs len data member with newCell | oldCell
    · simp only [thunkBlock, HeapElement.dataElement.injEq] at newCell
      obtain ⟨rfl, -, -⟩ := newCell
      simp only [List.mem_singleton] at qMember
      subst qMember
      exact rootsValid q w (by simp)
    · exact heapValid.2.2 xs len data q w ⟨oldCell, qMember⟩
  · obtain ⟨pre, post, heapEq, pEq⟩ := heapLookup_split heap p _ yCell
    subst heapEq
    subst pEq
    have canonical := heapStore_thunkBlock (β := WordLocW width) ev .notEvaluated rr y post pre
    have heapEq2 : heap2 = pre ++ thunkBlock ev rr :: post := congrArg Prod.fst (stored.symm.trans canonical)
    subst heapEq2
    simpa [List.append_assoc] using gcKindInv_refCellReplace conf pre post (thunkBlock .notEvaluated y)
      (thunkBlock ev rr) a sp sp1 gens (by simp [thunkBlock, elLength])
      (by simp [thunkBlock, isDataElement]) (by simp [thunkBlock, isRef, isMutTag])
      (by simp [thunkBlock, isRef, isMutTag]) (by simpa [List.append_assoc] using gcValid)
  · obtain ⟨unusedLookup, bound, upTo⟩ := unused
    refine ⟨?_, by rw [lenEq]; exact bound,
      dataUpTo_heapStore heap a p heap2 _ ⟨upTo, stored, by simp [thunkBlock, isDataElement]⟩⟩
    intro nonzero
    have old := unusedLookup nonzero
    apply kept a _ ⟨?_, old⟩
    intro same
    subst same
    rw [yCell] at old
    simp [thunkBlock] at old
  refine ⟨f, tf2, ⟨fun n domain => (dataEq _).mpr (injF.1 n domain), injF.2⟩, ?_, ?_, ?_, ?_, endian,
    blocksUnique_updateThunk ts ptr ev refs h stack unique, ?_, ?_⟩
  · intro n domain
    by_cases same : n = ptr
    · subst n
      exact ⟨_, sptLookup_sptInsert_same _ _ _⟩
    · obtain ⟨cell, oldCell⟩ := domainF n domain
      exact ⟨cell, by simpa [newRefs, sptLookup_sptInsert_ne ptr n _ refs same] using oldCell⟩
  · refine ⟨?_, ?_⟩
    · intro key domain
      obtain ⟨oldDomain, sameApply⟩ := restrictTimestampMap_domain_apply tf _ key domain
      rw [sameApply]
      exact (dataEq _).mpr (injTf.1 key oldDomain)
    · intro x y ⟨domainX, domainY⟩ equal
      obtain ⟨oldX, sameX⟩ := restrictTimestampMap_domain_apply tf _ x domainX
      obtain ⟨oldY, sameY⟩ := restrictTimestampMap_domain_apply tf _ y domainY
      exact injTf.2 x y ⟨oldX, oldY⟩ (sameX.symm.trans (equal.trans sameY))
  · intro n domain
    obtain ⟨w, lookup⟩ := domain
    exact ((restrictTimestampMap_lookup_some tf _ n w).mp lookup).1
  · intro n domain
    exact nextBound n (restrictTimestampMap_domain_apply tf _ n domain).1
  · refine .cons (transport h rr hRel (Or.inr (by simp [newStack]))) ?_
    refine .cons (transport _ ptrRoot ptrRel (Or.inr (by simp [newStack]))) ?_
    exact forall2_imp_member tailRel
      (fun w addr member rel => transport w addr rel (Or.inr (by simp [newStack, member])))
  intro n ⟨reachNew, domain⟩
  have reachOld := reachableRefs_thunkUpdate h false ptr stack ev refs n reachNew
  have oldRef := refsInv n ⟨reachOld, domain⟩
  by_cases same : n = ptr
  · subst n
    simp only [bcRefInv, pLookup, sptLookup_sptInsert_same]
    exact ⟨rr, newLookup,
      fun e => destThunk_notThunk_insertThunk h refs ptr .notEvaluated ev v h found (evaluated e),
      transport h rr hRel (Or.inr (by simp [newStack]))⟩
  · have lookupRefs : sptLookup n (sptInsert ptr (.thunk ev h) refs) = sptLookup n refs :=
      sptLookup_sptInsert_ne ptr n _ refs same
    obtain ⟨q, qLookup⟩ := domain
    have qNe : q ≠ p := by
      intro eq
      apply same
      apply injF.2 n ptr ⟨⟨q, qLookup⟩, ⟨p, pLookup⟩⟩
      rw [holFapply_of_lookup qLookup, holFapply_of_lookup pLookup, eq]
    have move : ∀ y, heapLookup q heap = some y → heapLookup q heap2 = some y :=
      fun y old => kept q y ⟨qNe, old⟩
    cases refLookup : sptLookup n refs with
    | none => simp [bcRefInv, qLookup, refLookup] at oldRef
    | some cell =>
      have observedCell : ∀ w, findRef cell w →
          (∃ index cell, sptLookup index newRefs = some cell ∧ findRef cell w) ∨ w ∈ newStack :=
        fun w member => Or.inl ⟨n, cell, by rw [lookupRefs, refLookup], member⟩
      cases cell with
      | valueArray values =>
        simp only [bcRefInv, qLookup, refLookup] at oldRef
        simp only [bcRefInv, qLookup, lookupRefs, refLookup]
        obtain ⟨addresses, cell, valuesInv⟩ := oldRef
        refine ⟨addresses, move _ cell, ?_⟩
        apply List.Forall₂.flip
        exact forall2_imp_member valuesInv.flip
          (fun w addr member rel => transport w addr rel (observedCell w member))
      | byteArray flag bytes =>
        simp only [bcRefInv, qLookup, refLookup] at oldRef
        simp only [bcRefInv, qLookup, lookupRefs, refLookup]
        exact move _ oldRef
      | thunk mode value =>
        simp only [bcRefInv, qLookup, refLookup] at oldRef
        simp only [bcRefInv, qLookup, lookupRefs, refLookup]
        obtain ⟨addr, cell, safe, valueRel⟩ := oldRef
        refine ⟨addr, move _ cell, ?_, transport value addr valueRel (observedCell value rfl)⟩
        intro e
        exact destThunk_notThunk_insertThunk value refs ptr .notEvaluated ev v h found (safe e)
      | mutBlock tag' finalised left value right =>
        simp only [bcRefInv, qLookup, refLookup] at oldRef
        simp only [bcRefInv, qLookup, lookupRefs, refLookup]
        obtain ⟨gen, fresh', addresses, cell, valuesInv⟩ := oldRef
        refine ⟨gen, ?_, addresses, move _ cell, ?_⟩
        · intro notFinal ⟨stamp, domainS, maps⟩
          obtain ⟨oldDomain, sameApply⟩ := restrictTimestampMap_domain_apply tf _ stamp domainS
          exact fresh' notFinal ⟨stamp, oldDomain, sameApply.symm.trans maps⟩
        · apply List.Forall₂.flip
          exact forall2_imp_member valuesInv.flip
            (fun w addr member rel => transport w addr rel (observedCell w member))

/-- HOL `update_thunk_thm`: updating an unevaluated thunk through the
reference just below the stack top stores a new thunk block and preserves
the abstract ML invariant. The three source conjuncts are the single
hypothesis `valid`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "update_thunk_thm"
  (words_as_type_indexed_bitvec)]
theorem updateThunk {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (h : Flapjack.Compiler.Backend.DataSem.Value) (ptr : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit ts : Nat)
    (v : Flapjack.Compiler.Backend.DataSem.Value) (ev : AstHOL.ThunkMode)
    (valid : absMlInv conf (h :: .refPtr false ptr :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit ts ∧
      sptLookup ptr refs = some (.thunk .notEvaluated v) ∧ (ev = .evaluated → destThunk h refs = .notThunk)) :
    ∃ (p : Nat) (r : HeapAddress (WordLocW width)) (roots2 v1 : List (HeapAddress (WordLocW width)))
      (heap2 : ValueHeap width) (u : WordLocW width),
      roots = r :: .pointer p u :: roots2 ∧ thunkDeref p heap = some v1 ∧
      heapStore p [thunkBlock ev r] heap = (heap2, true) ∧
      absMlInv conf (h :: .refPtr false ptr :: stack) (sptInsert ptr (.thunk ev h) refs)
        (roots, heap2, be, a, sp, sp1, gens) limit ts := by
  obtain ⟨p, r, roots2, y, heap2, rootsEq, cell, stored, inv⟩ :=
    updateThunkCore conf h ptr stack refs roots heap be a sp sp1 gens limit ts v ev valid
  exact ⟨p, r, roots2, [y], heap2, .word 0, rootsEq, by simp [thunkDeref, cell, thunkBlock], stored, inv⟩

/-- The encoded word heap assertion of a thunk cell. Flapjack proof
infrastructure. -/
theorem wordEl_thunkUnfold {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (base : BitVec width) (mode : AstHOL.ThunkMode) (z : HeapAddress (WordLocW width)) :
    wordEl base (thunkBlock (β := WordLocW width) mode z) conf =
      SetSep.star (Misc.wordList base
          [WordLocW.word (DataToWord.makeHeader conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1), wordAddr conf z])
        (SetSep.cond (1 < 2 ^ (width - 4) ∧
          WordGcFunctions.decodeLength conf
            (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1) =
            BitVec.ofNat width 1)) := by
  simp [wordEl, thunkBlock, wordPayload]

/-- Separating conjunction is monotone in both arguments. Flapjack
separation-logic infrastructure. -/
theorem star_mono_both {α : Type} {left left' right right' : (α → Prop) → Prop} {heap : α → Prop}
    (assertion : SetSep.star left right heap) (hl : ∀ part, left part → left' part)
    (hr : ∀ part, right part → right' part) : SetSep.star left' right' heap := by
  obtain ⟨first, second, split, l, r⟩ := assertion
  exact ⟨first, second, split, hl _ l, hr _ r⟩

/-- Writing a thunk payload word. Flapjack proof infrastructure. -/
theorem wordEl_thunkPayloadStore {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (mode : AstHOL.ThunkMode) (y r : HeapAddress (WordLocW width)) (base : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (separated : SetSep.star (wordEl base (thunkBlock mode y) conf) frame (SetSep.fun2Set (memory, domain))) :
    domain (base + StackRemove.bytesInWord width) ∧
    SetSep.star (wordEl base (thunkBlock mode r) conf) frame
      (SetSep.fun2Set ((fun key => if key = base + StackRemove.bytesInWord width then wordAddr conf r
        else memory key), domain)) := by
  rw [wordEl_thunkUnfold, ← SetSep.starAssoc] at separated
  have inGraph : SetSep.fun2Set (memory, domain) (base + StackRemove.bytesInWord width, wordAddr conf y) := by
    obtain ⟨payload, rest, split, words, _⟩ := separated
    rw [← split.1]
    left
    have member := wordList_indexMember
      [WordLocW.word (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1),
        wordAddr conf y] 1 (by simp) base payload words
    simpa using member
  have inDomain := ((SetSep.fun2SetThm memory domain _ _).mp inGraph).2
  have changed := wordList_write base
    [WordLocW.word (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1),
      wordAddr conf y] 1 (wordAddr conf r) memory domain _ (by simp) separated
  refine ⟨inDomain, ?_⟩
  rw [wordEl_thunkUnfold, ← SetSep.starAssoc]
  simpa using changed

/-- Rewriting a thunk header to another thunk mode. Flapjack proof
infrastructure. -/
theorem wordEl_thunkHeaderStore {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (mode mode2 : AstHOL.ThunkMode) (y : HeapAddress (WordLocW width)) (base : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (decoded : WordGcFunctions.decodeLength conf
      (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode2 <<< (3 : Nat)) ||| 6) 1) =
      BitVec.ofNat width 1)
    (separated : SetSep.star (wordEl base (thunkBlock mode y) conf) frame (SetSep.fun2Set (memory, domain))) :
    domain base ∧
    SetSep.star (wordEl base (thunkBlock mode2 y) conf) frame
      (SetSep.fun2Set ((fun key => if key = base then
        WordLocW.word (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode2 <<< (3 : Nat)) ||| 6) 1)
        else memory key), domain)) := by
  rw [wordEl_thunkUnfold, ← SetSep.starAssoc] at separated
  have inGraph : SetSep.fun2Set (memory, domain)
      (base, WordLocW.word (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1)) := by
    obtain ⟨payload, rest, split, words, _⟩ := separated
    rw [← split.1]
    left
    have member := wordList_indexMember
      [WordLocW.word (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1),
        wordAddr conf y] 0 (by simp) base payload words
    simpa using member
  have inDomain := ((SetSep.fun2SetThm memory domain _ _).mp inGraph).2
  have changed := wordList_write base
    [WordLocW.word (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1),
      wordAddr conf y] 0
    (WordLocW.word (DataToWord.makeHeader (width := width) conf ((thunkTagToBits mode2 <<< (3 : Nat)) ||| 6) 1))
    memory domain _ (by simp) separated
  refine ⟨inDomain, ?_⟩
  rw [wordEl_thunkUnfold, ← SetSep.starAssoc]
  simp only [List.set_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.zero_mul, BitVec.add_zero] at changed
  refine star_mono_both changed (fun _ part => part) ?_
  intro part rest
  refine star_mono_both rest ?_ (fun _ part => part)
  rintro _ ⟨empty, bound, _⟩
  exact ⟨empty, bound, decoded⟩

/-- Replacing one heap cell of the same length, through a separation-logic
step on its encoded cell, transforms the whole encoded heap. Flapjack proof
infrastructure. -/
theorem wordHeap_cellReplace {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (old new : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) (pre post : ValueHeap width)
    (curr : BitVec width) (memory : BitVec width → WordLocW width)
    (memory2 : BitVec width → BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (condition : BitVec width → Prop) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (sameLength : elLength old = elLength new)
    (step : ∀ base (frame' : ((BitVec width × WordLocW width) → Prop) → Prop),
      SetSep.star (wordEl base old conf) frame' (SetSep.fun2Set (memory, domain)) →
        condition base ∧ SetSep.star (wordEl base new conf) frame' (SetSep.fun2Set (memory2 base, domain)))
    (separated : SetSep.star (wordHeap curr (pre ++ [old] ++ post) conf) frame (SetSep.fun2Set (memory, domain))) :
    condition (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)) ∧
    SetSep.star (wordHeap curr (pre ++ [new] ++ post) conf) frame
      (SetSep.fun2Set (memory2 (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)),
        domain)) := by
  rw [List.append_assoc, wordHeapAppend] at separated
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  obtain ⟨holds, result⟩ := step _ _ separated
  refine ⟨holds, ?_⟩
  rw [star_swap_first] at result
  rw [List.append_assoc, wordHeapAppend]
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc]
  simpa [sameLength] using result

/-- The heap/store invariant counterpart of `wordHeap_cellReplace`. Flapjack
proof infrastructure. -/
theorem heapInMemoryStore_cellReplace {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (old new : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) (pre post : ValueHeap width)
    (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (memory2 : BitVec width → BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (condition : BitVec width → Prop) (limit : Nat) (sameLength : elLength old = elLength new)
    (step : ∀ base (frame' : ((BitVec width × WordLocW width) → Prop) → Prop),
      SetSep.star (wordEl base old conf) frame' (SetSep.fun2Set (memory, fun addr => domain addr = true)) →
        condition base ∧
        SetSep.star (wordEl base new conf) frame' (SetSep.fun2Set (memory2 base, fun addr => domain addr = true)))
    (heapMem : heapInMemoryStore (pre ++ [old] ++ post) a sp sp1 gens conf store memory domain limit) :
    ∃ curr, store.lookup .currHeap = some (.word curr) ∧
      condition (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)) ∧
      heapInMemoryStore (pre ++ [new] ++ post) a sp sp1 gens conf store
        (memory2 (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))) domain limit := by
  obtain ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, globals,
    curr, other, currAligned, otherAligned, currStore, otherStore, nextStore,
    triggerStore, endStore, lengthStore, globInv, genInv, separated⟩ := heapMem
  obtain ⟨holds, heapNew⟩ :=
    wordHeap_cellReplace conf old new pre post curr memory memory2 _ condition _ sameLength step separated
  have lengthEq : heapLength (pre ++ [old] ++ post) = heapLength (pre ++ [new] ++ post) := by
    simp [heapLength, List.map_append, List.sum_append, sameLength]
  refine ⟨curr, currStore, holds, ?_⟩
  refine ⟨?_, ?_, shift, lenNonzero, lenBound, shiftBound, globals, curr, other, currAligned, otherAligned,
    currStore, otherStore, nextStore, triggerStore, endStore, lengthStore, globInv, genInv, heapNew⟩
  · simpa only [← lengthEq] using bound1
  · simpa only [← lengthEq] using bound2

/-- HOL `memory_rel_UpdateThunk_NotEvaluated`: overwriting the payload of an
unevaluated thunk keeps it unevaluated and preserves the memory relation.
The three source conjuncts are the single hypothesis `valid`;
`x + bytes_in_word ∈ dm` is `domain (x + bytesInWord) = true` and
`(x + bytes_in_word =+ w) m` is the pointwise if-update of `memory`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_UpdateThunk_NotEvaluated"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_updateThunk_notEvaluated {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (h : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (nn : Nat) (ptr : WordLocW width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (v : Flapjack.Compiler.Backend.DataSem.Value)
    (valid : memoryRel conf be next refs space store memory domain ((h, w) :: (.refPtr false nn, ptr) :: vars) ∧
      sptLookup nn refs = some (.thunk .notEvaluated v) ∧ goodDimindex width) :
    ∃ ptrW x : BitVec width, ptr = .word ptrW ∧ getRealAddr conf store ptrW = some x ∧
      domain (x + StackRemove.bytesInWord width) = true ∧
      memoryRel conf be next (sptInsert nn (.thunk .notEvaluated h) refs) space store
        (fun key => if key = x + StackRemove.bytesInWord width then w else memory key) domain
        ((h, w) :: (.refPtr false nn, ptr) :: vars) := by
  obtain ⟨related, found, good⟩ := valid
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, spaceBound, limitBound⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  have absInv' : absMlInv conf (h :: .refPtr false nn :: vars.map Prod.fst) refs
      (roots, heap, be, a, sp, sp1, gens) limit next := by simpa using absInv
  obtain ⟨p, rr, roots2, y, heap2, rootsEq, cell, stored, absNew⟩ :=
    updateThunkCore conf h nn _ refs roots heap be a sp sp1 gens limit next v .notEvaluated
      ⟨absInv', found, fun e => by cases e⟩
  subst rootsEq
  cases rootWords with
  | cons valueAddr remaining =>
    cases remaining with
    | cons ptrAddr tail =>
      have wordEq : wordAddr conf rr = w := valueAddr
      have rootEq : ptr = .word (getAddr conf p (.word 0)) := by simpa [wordAddr] using ptrAddr.symm
      obtain ⟨pre, post, heapEq, pEq⟩ := heapLookup_split heap p _ cell
      subst heap
      subst p
      have canonical := heapStore_thunkBlock (β := WordLocW width) .notEvaluated .notEvaluated rr y post pre
      have heapEq2 : heap2 = pre ++ thunkBlock .notEvaluated rr :: post :=
        congrArg Prod.fst (stored.symm.trans canonical)
      subst heap2
      have heapMem' : heapInMemoryStore (pre ++ [thunkBlock .notEvaluated y] ++ post)
          a sp sp1 gens conf store memory domain limit := by simpa [List.append_assoc] using heapMem
      obtain ⟨curr, currStore, inDomain, memoryNew⟩ :=
        heapInMemoryStore_cellReplace conf (thunkBlock .notEvaluated y) (thunkBlock .notEvaluated rr) pre post
          a sp sp1 gens store memory
          (fun base key => if key = base + StackRemove.bytesInWord width then wordAddr conf rr else memory key)
          domain (fun base => domain (base + StackRemove.bytesInWord width) = true) limit
          (by simp [thunkBlock, elLength])
          (fun base frame' separated => wordEl_thunkPayloadStore conf .notEvaluated y rr base memory _ frame' separated)
          heapMem'
      have address := getRealAddr_getAddr conf store _ (heapLength pre) _ curr (.word 0)
        ⟨heapMem'.1, by simpa [List.append_assoc] using cell, currStore, good⟩
      refine ⟨getAddr conf (heapLength pre) (.word 0),
        curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre), rootEq,
        by simpa [BitVec.mul_comm] using address.2, inDomain, ?_⟩
      refine ⟨pre ++ [thunkBlock .notEvaluated rr] ++ post, limit, a, sp, sp1, gens,
        ?_, ?_, spaceBound, limitBound⟩
      · simpa [wordEq] using memoryNew
      · refine ⟨rr :: .pointer (heapLength pre) (.word 0) :: roots2, ?_, ?_⟩
        · simpa [List.append_assoc] using absNew
        · exact .cons valueAddr (.cons ptrAddr tail)

/-- HOL `memory_rel_UpdateThunk_Evaluated`: evaluating a thunk rewrites its
header and payload and preserves the memory relation. The five source
conjuncts are the single hypothesis `valid`; `m =++ [...]` is
`Misc.UpdateList.updateList`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_UpdateThunk_Evaluated"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_updateThunk_evaluated {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (h : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (nn : Nat) (ptr : WordLocW width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (v : Flapjack.Compiler.Backend.DataSem.Value) (hdr : BitVec width)
    (valid : memoryRel conf be next refs space store memory domain ((h, w) :: (.refPtr false nn, ptr) :: vars) ∧
      sptLookup nn refs = some (.thunk .notEvaluated v) ∧ DataToWord.encodeHeader conf (8 + 6) 1 = some hdr ∧
      destThunk h refs = .notThunk ∧ goodDimindex width) :
    ∃ ptrW x : BitVec width, ptr = .word ptrW ∧ getRealAddr conf store ptrW = some x ∧
      domain x = true ∧ domain (x + StackRemove.bytesInWord width) = true ∧
      memoryRel conf be next (sptInsert nn (.thunk .evaluated h) refs) space store
        (Misc.UpdateList.updateList memory [(x, .word hdr), (x + StackRemove.bytesInWord width, w)]) domain
        ((h, w) :: (.refPtr false nn, ptr) :: vars) := by
  obtain ⟨related, found, encoded, notThunk, good⟩ := valid
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, spaceBound, limitBound⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have hdrEq : DataToWord.makeHeader (width := width) conf ((thunkTagToBits .evaluated <<< (3 : Nat)) ||| 6) 1 = hdr := by
    rw [thunkTagBits_evaluated]
    simp only [DataToWord.encodeHeader] at encoded
    split at encoded
    · exact Option.some.inj encoded
    · cases encoded
  have decoded := (encodeHeaderImp conf (8 + 6) 1 hdr encoded (by omega) good).2
  rw [← hdrEq] at decoded
  have absInv' : absMlInv conf (h :: .refPtr false nn :: vars.map Prod.fst) refs
      (roots, heap, be, a, sp, sp1, gens) limit next := by simpa using absInv
  obtain ⟨p, rr, roots2, y, heap2, rootsEq, cell, stored, absNew⟩ :=
    updateThunkCore conf h nn _ refs roots heap be a sp sp1 gens limit next v .evaluated
      ⟨absInv', found, fun _ => notThunk⟩
  subst rootsEq
  cases rootWords with
  | cons valueAddr remaining =>
    cases remaining with
    | cons ptrAddr tail =>
      have wordEq : wordAddr conf rr = w := valueAddr
      have rootEq : ptr = .word (getAddr conf p (.word 0)) := by simpa [wordAddr] using ptrAddr.symm
      obtain ⟨pre, post, heapEq, pEq⟩ := heapLookup_split heap p _ cell
      subst heap
      subst p
      have canonical := heapStore_thunkBlock (β := WordLocW width) .evaluated .notEvaluated rr y post pre
      have heapEq2 : heap2 = pre ++ thunkBlock .evaluated rr :: post :=
        congrArg Prod.fst (stored.symm.trans canonical)
      subst heap2
      have heapMem' : heapInMemoryStore (pre ++ [thunkBlock .notEvaluated y] ++ post)
          a sp sp1 gens conf store memory domain limit := by simpa [List.append_assoc] using heapMem
      obtain ⟨curr, currStore, inDomain, memoryNew⟩ :=
        heapInMemoryStore_cellReplace conf (thunkBlock .notEvaluated y) (thunkBlock .evaluated rr) pre post
          a sp sp1 gens store memory
          (fun base key => if key = base + StackRemove.bytesInWord width then wordAddr conf rr
            else if key = base then .word hdr else memory key)
          domain (fun base => domain base = true ∧ domain (base + StackRemove.bytesInWord width) = true) limit
          (by simp [thunkBlock, elLength])
          (fun base frame' separated => by
            obtain ⟨headerIn, headerNew⟩ :=
              wordEl_thunkHeaderStore conf .notEvaluated .evaluated y base memory _ frame' decoded separated
            obtain ⟨payloadIn, payloadNew⟩ :=
              wordEl_thunkPayloadStore conf .evaluated y rr base _ _ frame' headerNew
            refine ⟨⟨headerIn, payloadIn⟩, ?_⟩
            rw [hdrEq] at payloadNew
            exact payloadNew)
          heapMem'
      have address := getRealAddr_getAddr conf store _ (heapLength pre) _ curr (.word 0)
        ⟨heapMem'.1, by simpa [List.append_assoc] using cell, currStore, good⟩
      refine ⟨getAddr conf (heapLength pre) (.word 0),
        curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre), rootEq,
        by simpa [BitVec.mul_comm] using address.2, inDomain.1, inDomain.2, ?_⟩
      have memoryEq : Misc.UpdateList.updateList memory
          [(curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre), .word hdr),
            (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
              StackRemove.bytesInWord width, w)] =
          fun key => if key = curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
              StackRemove.bytesInWord width then wordAddr conf rr
            else if key = curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) then .word hdr
            else memory key := by
        funext key
        simp [Misc.UpdateList.updateList, wordEq, eq_comm]
      rw [memoryEq]
      refine ⟨pre ++ [thunkBlock .evaluated rr] ++ post, limit, a, sp, sp1, gens,
        memoryNew, ?_, spaceBound, limitBound⟩
      refine ⟨rr :: .pointer (heapLength pre) (.word 0) :: roots2, ?_, ?_⟩
      · simpa [List.append_assoc] using absNew
      · exact .cons valueAddr (.cons ptrAddr tail)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
