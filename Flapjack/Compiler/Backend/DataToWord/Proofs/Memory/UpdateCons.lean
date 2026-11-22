module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.MutCons
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CellUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateRestriction

@[expose] public section

/-!
# Writing the hole of an unfinalised mutable block

Counterparts of `v_inv_BlockRep_upd_lemma` and `update_mutblock_thm` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`t IN FDOM tf` is `mapDomain tf t`, `tf ' t` is `holFapply tf t`,
`LUPDATE x n l` is `l.set n x` and `v_inv_ck` is `ClockValueInv`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- The clocked value invariant survives a heap change at a block cell `p`
that no timestamp targets, when every other cell is kept. Flapjack proof
infrastructure for `v_inv_BlockRep_upd_lemma`. -/
theorem clockValueInv_blockRepUpd {width : Nat} [NeZero width] (ck : Nat)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f tf : HolFiniteMapExact Nat Nat) (heap heap2 : ValueHeap width) (p tag : Nat)
    (zs : List (HeapAddress (WordLocW width)))
    (cellP : heapLookup p heap = some (blockRep tag zs))
    (noStamp : ∀ t, mapDomain tf t → holFapply tf t ≠ p)
    (kept : ∀ m y, m ≠ p ∧ heapLookup m heap = some y → heapLookup m heap2 = some y) :
    ∀ (value : Flapjack.Compiler.Backend.DataSem.Value) (address : HeapAddress (WordLocW width)),
      ClockValueInv ck conf value refs (address, f, tf, heap) →
      ClockValueInv ck conf value refs (address, f, tf, heap2) := by
  have keep : ∀ m y, heapLookup m heap = some y → y ≠ blockRep tag zs → heapLookup m heap2 = some y := by
    intro m y found ne
    apply kept m y ⟨?_, found⟩
    rintro rfl
    rw [cellP] at found
    exact ne (Option.some.inj found).symm
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value address related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i refs f tf heap2 small
    | numberBig _ _ i ptr _ _ _ _ large found =>
      apply ClockValueInv.numberBig ck conf i ptr refs f tf heap2 large
      apply keep ptr _ found
      simp [bignumRep, blockRep]
    | word64 _ _ word ptr _ _ _ _ found =>
      apply ClockValueInv.word64 ck conf word ptr refs f tf heap2
      apply keep ptr _ found
      unfold word64Rep
      split <;> simp [blockRep]
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n refs f tf heap2
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      exact .refPtr bit ck conf n refs f tf heap2 domain notThunk notMut
    | refPtrThunk _ _ mode n body x _ _ _ _ found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body x refs f tf heap2 found evaluated domain ?_ ?_
      · apply keep _ _ cell
        simp [thunkBlock, blockRep]
      · intro positive
        exact ih (ck - 1) (by omega) body x (recursive positive)
    | refPtrThunkInlined _ _ n body x _ _ _ _ found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body address refs f tf heap2 found notThunk ?_
      intro positive
      exact ih (ck - 1) (by omega) body address (recursive positive)
    | blockNil _ _ stamp tag' values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag' values refs f tf heap2 empty bound zero
    | blockCons _ _ stamp tag' ptr values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag' ptr values xs refs f tf heap2 nonempty ?_ timestamp ?_
      · intro positive
        apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
        apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
        intro child addr childInv
        exact ih (ck - 1) (by omega) child addr childInv
      · apply kept ptr _ ⟨?_, cell⟩
        have := noStamp stamp ⟨ptr, timestamp⟩
        rwa [holFapply_of_lookup timestamp] at this

/-- HOL `v_inv_BlockRep_upd_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_BlockRep_upd_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_blockRepUpd_lemma {width : Nat} [NeZero width] :
    ∀ (ck : Nat) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (p tag : Nat)
      (zs : List (HeapAddress (WordLocW width))),
      valueInv conf v1 refs (x, f, tf, heap) ∧ heapLookup p heap = some (blockRep tag zs) ∧
          (∀ t, mapDomain tf t → holFapply tf t ≠ p) ∧
          (∀ m y, m ≠ p ∧ heapLookup m heap = some y → heapLookup m heap2 = some y) →
        ClockValueInv ck conf v1 refs (x, f, tf, heap2) := by
  rintro ck conf v1 refs x f tf heap heap2 p tag zs ⟨inv, cellP, noStamp, kept⟩
  exact clockValueInv_blockRepUpd ck conf refs f tf heap heap2 p tag zs cellP noStamp kept v1 x (inv ck)

/-- Inserting a mutable block over a mutable block keeps every non-thunk
value a non-thunk. Flapjack proof infrastructure. -/
theorem destThunk_notThunk_insertMutBlock (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ptr tag : Nat) (fin : Bool)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value)
    (r : List Flapjack.Compiler.Backend.DataSem.Value)
    (notThunk : destThunk value refs = .notThunk) :
    destThunk value (sptInsert ptr (.mutBlock tag fin l c r) refs) = .notThunk := by
  cases value with
  | refPtr bit index =>
    by_cases same : index = ptr
    · subst index
      simp [destThunk, sptLookup_sptInsert_same]
    · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs same] using notThunk
  | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]

/-- A value related before writing the hole of an unfinalised mutable block
stays related after the heap cell, the reference cell and the timestamp map
(restricted to the new timestamps) all change. Flapjack proof
infrastructure for `update_mutblock_thm`. -/
theorem valueInv_mutBlockUpdate_restrict {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ptr tag p : Nat)
    (l r stack : List Flapjack.Compiler.Backend.DataSem.Value) (cv h : Flapjack.Compiler.Backend.DataSem.Value)
    (zs : List (HeapAddress (WordLocW width))) (address : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap heap2 : ValueHeap width)
    (value : Flapjack.Compiler.Backend.DataSem.Value)
    (found : sptLookup ptr refs = some (.mutBlock tag false l cv r))
    (cellP : heapLookup p heap = some (blockRep tag zs))
    (noStamp : ∀ t, mapDomain tf t → holFapply tf t ≠ p)
    (kept : ∀ m y, m ≠ p ∧ heapLookup m heap = some y → heapLookup m heap2 = some y)
    (related : valueInv conf value refs (address, f, tf, heap))
    (observed : (∃ index cell, sptLookup index (sptInsert ptr (.mutBlock tag false l h r) refs) = some cell ∧
      findRef cell value) ∨ value ∈ stack) :
    valueInv conf value (sptInsert ptr (.mutBlock tag false l h r) refs)
      (address, f, restrictTimestampMap tf (allTimestamps (sptInsert ptr (.mutBlock tag false l h r) refs) stack),
        heap2) := by
  have moved : valueInv conf value refs (address, f, tf, heap2) := fun ck =>
    valueInv_blockRepUpd_lemma ck conf value refs address f tf heap heap2 p tag zs
      ⟨related, cellP, noStamp, kept⟩
  have updated := valueInv_mutBlockHole conf value refs address f tf heap2 ptr tag false false l cv h r
    ⟨moved, found⟩
  exact valueInv_tfRestrict conf value _ stack address f tf heap2 _
    ⟨updated, fun stamp member => ⟨value, observed, member⟩, fun _ member => member⟩

/-- HOL `update_mutblock_thm`: writing the hole of an unfinalised mutable
block through the reference just below the stack top replaces the hole's
pointer in the heap block and preserves the abstract ML invariant. The two
source conjuncts are the single hypothesis `valid`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "update_mutblock_thm"
  (words_as_type_indexed_bitvec)]
theorem updateMutBlock {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (h : Flapjack.Compiler.Backend.DataSem.Value) (ptr : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit ts : Nat)
    (tag : Nat) (l : List Flapjack.Compiler.Backend.DataSem.Value) (cv : Flapjack.Compiler.Backend.DataSem.Value)
    (r : List Flapjack.Compiler.Backend.DataSem.Value)
    (valid : absMlInv conf (h :: .refPtr false ptr :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit ts ∧
      sptLookup ptr refs = some (.mutBlock tag false l cv r)) :
    ∃ (p : Nat) (rr : HeapAddress (WordLocW width)) (roots2 vs1 : List (HeapAddress (WordLocW width)))
      (heap2 : ValueHeap width) (u : WordLocW width),
      roots = rr :: .pointer p u :: roots2 ∧ heapLookup p heap = some (blockRep tag vs1) ∧
      vs1.length = l.length + 1 + r.length ∧
      heapStore p [blockRep tag (vs1.set l.length rr)] heap = (heap2, true) ∧
      absMlInv conf (h :: .refPtr false ptr :: stack) (sptInsert ptr (.mutBlock tag false l h r) refs)
        (roots, heap2, be, a, sp, sp1, gens) limit ts := by
  obtain ⟨⟨rootsValid, heapValid, gcValid, unused, stackInv⟩, found⟩ := valid
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
  have noThunk : ∀ mode value, sptLookup ptr refs ≠ some (.thunk mode value) := by
    intro mode value
    simp [found]
  obtain ⟨⟨p, pLookup⟩, _, ptrEq⟩ :=
    (valueInv_refPtr_notThunk conf false ptr refs ptrRoot f tf heap noThunk).mp ptrRel
  have reachable : reachableRefs (h :: .refPtr false ptr :: stack) refs ptr :=
    ⟨.refPtr false ptr, ptr, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
  have ptrInv := refsInv ptr ⟨reachable, ⟨p, pLookup⟩⟩
  simp only [bcRefInv, pLookup, found] at ptrInv
  obtain ⟨notGen, fresh, zs, zsLookup, zsInv⟩ := ptrInv
  have noStamp : ∀ t, mapDomain tf t → holFapply tf t ≠ p := fun t dom eq => fresh (by trivial) ⟨t, dom, eq⟩
  obtain ⟨pre2, v2, tail2, zsEq, lRel, -, rRel⟩ :=
    forall2_split_head l cv r zs (by simpa using zsInv.flip)
  have preLen : pre2.length = l.length := lRel.length_eq.symm
  have zsLen : zs.length = l.length + 1 + r.length := by
    rw [zsEq]
    simp [preLen, rRel.length_eq]
    omega
  have setEq : zs.set l.length rr = pre2 ++ rr :: tail2 := by
    rw [zsEq, ← preLen]
    simp
  obtain ⟨heap2, stored, newLookup, lenEq, fwdEq, members, dataEq, kept⟩ :=
    heapStore_blockRep_source zs (zs.set l.length rr) p tag heap ⟨by simp, zsLookup⟩
  let newRefs := sptInsert ptr (.mutBlock tag false l h r) refs
  let newStack := h :: .refPtr false ptr :: stack
  let tf2 := restrictTimestampMap tf (allTimestamps newRefs newStack)
  have transport : ∀ value address, valueInv conf value refs (address, f, tf, heap) →
      ((∃ index cell, sptLookup index newRefs = some cell ∧ findRef cell value) ∨ value ∈ newStack) →
      valueInv conf value newRefs (address, f, tf2, heap2) := fun value address rel obs =>
    valueInv_mutBlockUpdate_restrict conf refs ptr tag p l r newStack cv h zs address f tf heap heap2 value
      found zsLookup noStamp kept rel obs
  refine ⟨p, rr, roots2, zs, heap2, refPtrAnnot conf (sptLookup ptr refs), ?_, zsLookup, zsLen, stored, ?_⟩
  · rw [ptrEq, holFapply_of_lookup pLookup]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q v member
    exact (dataEq q).mpr (rootsValid q v member)
  · refine ⟨lenEq.trans heapValid.1, fwdEq.trans heapValid.2.1, ?_⟩
    intro xs len data q v ⟨member, qMember⟩
    apply (dataEq q).mpr
    rcases members xs len data member with newCell | oldCell
    · simp only [blockRep, HeapElement.dataElement.injEq] at newCell
      obtain ⟨rfl, -, -⟩ := newCell
      rcases List.mem_or_eq_of_mem_set qMember with old | eq
      · exact heapValid.2.2 zs zs.length (.blockTag tag, []) q v
          ⟨by simpa [blockRep] using heapLookup_mem heap p _ zsLookup, old⟩
      · subst eq
        exact rootsValid q v (by simp)
    · exact heapValid.2.2 xs len data q v ⟨oldCell, qMember⟩
  · cases kind : conf.gcKind with
    | none => simpa [gcKindInv, kind] using gcValid
    | simple => simpa [gcKindInv, kind] using gcValid
    | generational sizes => exact absurd kind (notGen sizes)
  · obtain ⟨unusedLookup, bound, upTo⟩ := unused
    refine ⟨?_, by rw [lenEq]; exact bound,
      dataUpTo_heapStore heap a p heap2 _ ⟨upTo, stored, by simp [blockRep, isDataElement]⟩⟩
    intro nonzero
    have old := unusedLookup nonzero
    apply kept a _ ⟨?_, old⟩
    intro same
    subst same
    rw [zsLookup] at old
    simp [blockRep] at old
  refine ⟨f, tf2, ⟨fun n domain => (dataEq _).mpr (injF.1 n domain), injF.2⟩, ?_, ?_, ?_, ?_, endian,
    blocksUnique_updateMutBlock ts ptr tag false refs l cv h r stack ⟨found, unique⟩, ?_, ?_⟩
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
    obtain ⟨v, lookup⟩ := domain
    exact ((restrictTimestampMap_lookup_some tf _ n v).mp lookup).1
  · intro n domain
    exact nextBound n (restrictTimestampMap_domain_apply tf _ n domain).1
  · refine .cons (transport h rr hRel (Or.inr (by simp [newStack]))) ?_
    refine .cons (transport _ ptrRoot ptrRel (Or.inr (by simp [newStack]))) ?_
    exact forall2_imp_member tailRel
      (fun v addr member rel => transport v addr rel (Or.inr (by simp [newStack, member])))
  intro n ⟨reachNew, domain⟩
  have reachOld := reachableRefs_mutBlock_update ptr tag n false false l cv h r stack refs ⟨found, reachNew⟩
  have oldRef := refsInv n ⟨reachOld, domain⟩
  by_cases same : n = ptr
  · subst n
    simp only [bcRefInv, pLookup, sptLookup_sptInsert_same]
    refine ⟨notGen, ?_, zs.set l.length rr, newLookup, ?_⟩
    · intro _ ⟨stamp, domainS, maps⟩
      obtain ⟨oldDomain, sameApply⟩ := restrictTimestampMap_domain_apply tf _ stamp domainS
      exact fresh (by trivial) ⟨stamp, oldDomain, sameApply.symm.trans maps⟩
    · have observedIn : ∀ v, v ∈ l ++ [h] ++ r →
          (∃ index cell, sptLookup index newRefs = some cell ∧ findRef cell v) ∨ v ∈ newStack :=
        fun v member => Or.inl ⟨ptr, _, sptLookup_sptInsert_same _ _ _, member⟩
      rw [setEq]
      apply List.Forall₂.flip
      have shape : l ++ [h] ++ r = l ++ h :: r := by simp
      rw [shape]
      refine List.rel_append ?_ (.cons ?_ ?_)
      · exact forall2_imp_member lRel
          (fun v addr member rel => transport v addr rel (observedIn v (by simp [member])))
      · exact transport h rr hRel (observedIn h (by simp))
      · exact forall2_imp_member rRel
          (fun v addr member rel => transport v addr rel (observedIn v (by simp [member])))
  · have lookupRefs : sptLookup n (sptInsert ptr (.mutBlock tag false l h r) refs) = sptLookup n refs := sptLookup_sptInsert_ne ptr n _ refs same
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
      have observedCell : ∀ v, findRef cell v →
          (∃ index cell, sptLookup index newRefs = some cell ∧ findRef cell v) ∨ v ∈ newStack :=
        fun v member => Or.inl ⟨n, cell, by rw [lookupRefs, refLookup], member⟩
      cases cell with
      | valueArray values =>
        simp only [bcRefInv, qLookup, refLookup] at oldRef
        simp only [bcRefInv, qLookup, lookupRefs, refLookup]
        obtain ⟨addresses, cell, valuesInv⟩ := oldRef
        refine ⟨addresses, move _ cell, ?_⟩
        apply List.Forall₂.flip
        exact forall2_imp_member valuesInv.flip
          (fun v addr member rel => transport v addr rel (observedCell v member))
      | byteArray flag bytes =>
        simp only [bcRefInv, qLookup, refLookup] at oldRef
        simp only [bcRefInv, qLookup, lookupRefs, refLookup]
        exact move _ oldRef
      | thunk mode value =>
        simp only [bcRefInv, qLookup, refLookup] at oldRef
        simp only [bcRefInv, qLookup, lookupRefs, refLookup]
        obtain ⟨addr, cell, safe, valueRel⟩ := oldRef
        refine ⟨addr, move _ cell, ?_, transport value addr valueRel (observedCell value rfl)⟩
        intro evaluated
        exact destThunk_notThunk_insertMutBlock value refs ptr tag false l h r (safe evaluated)
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
            (fun v addr member rel => transport v addr rel (observedCell v member))

/-- Replacing one encoded block payload word preserves its header and any
disjoint memory frame. Flapjack proof infrastructure. -/
theorem wordEl_blockStore {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (tag : Nat) (pointers : List (HeapAddress (WordLocW width))) (replacement : HeapAddress (WordLocW width))
    (base : BitVec width) (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (index : Nat)
    (bound : index < pointers.length)
    (separated : SetSep.star (wordEl base (blockRep tag pointers) conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    domain (base + StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width) = true ∧
    SetSep.star (wordEl base (blockRep tag (pointers.set index replacement)) conf) frame
      (SetSep.fun2Set ((fun key => if key = base + StackRemove.bytesInWord width +
        BitVec.ofNat width index * StackRemove.bytesInWord width then wordAddr conf replacement else memory key),
        fun addr => domain addr = true)) := by
  simp only [wordEl, blockRep, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map,
    Misc.wordList, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  have inGraph : SetSep.fun2Set (memory, fun addr => domain addr = true)
      (base + StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width,
        wordAddr conf pointers[index]) := by
    obtain ⟨payload, rest, split, words, _⟩ := separated
    rw [← split.1]
    left
    have member := wordList_indexMember (pointers.map (wordAddr conf)) index
      (by simpa using bound) (base + StackRemove.bytesInWord width) payload words
    simpa [List.getElem_map] using member
  have inDomain := ((SetSep.fun2SetThm memory (fun addr => domain addr = true) _ _).mp inGraph).2
  have changed := wordList_write (base + StackRemove.bytesInWord width) (pointers.map (wordAddr conf)) index
    (wordAddr conf replacement) memory (fun addr => domain addr = true) _ (by simpa using bound) separated
  rw [star_swap_first] at changed
  refine ⟨inDomain, ?_⟩
  simpa [wordEl, blockRep, wordPayload, List.map_set, Misc.wordList, ← SetSep.starAssoc] using changed

/-- A block payload store preserves the surrounding word heap and an
arbitrary separated frame. Flapjack proof infrastructure. -/
theorem wordHeap_blockStore {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (tag : Nat) (pointers : List (HeapAddress (WordLocW width))) (replacement : HeapAddress (WordLocW width))
    (curr : BitVec width) (pre post : ValueHeap width) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (index : Nat) (bound : index < pointers.length)
    (separated : SetSep.star (wordHeap curr (pre ++ [blockRep tag pointers] ++ post) conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    let addr := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
      StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width
    domain addr = true ∧
    SetSep.star (wordHeap curr (pre ++ [blockRep tag (pointers.set index replacement)] ++ post) conf) frame
      (SetSep.fun2Set ((fun key => if key = addr then wordAddr conf replacement else memory key),
        fun addr => domain addr = true)) := by
  rw [List.append_assoc, wordHeapAppend] at separated
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  obtain ⟨inDomain, result⟩ := wordEl_blockStore conf tag pointers replacement
    (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)) memory domain _ index bound separated
  refine ⟨inDomain, ?_⟩
  rw [star_swap_first] at result
  rw [List.append_assoc, wordHeapAppend]
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc]
  simpa [blockRep, elLength] using result

/-- Updating a block payload word preserves the heap/store invariant and
identifies the concrete store address. Flapjack proof infrastructure. -/
theorem heapInMemoryStore_blockStore {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (tag : Nat)
    (pointers : List (HeapAddress (WordLocW width))) (replacement : HeapAddress (WordLocW width))
    (pre post : ValueHeap width) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (limit index : Nat) (bound : index < pointers.length)
    (heapMem : heapInMemoryStore (pre ++ [blockRep tag pointers] ++ post)
      a sp sp1 gens conf store memory domain limit) :
    ∃ curr, store.lookup .currHeap = some (.word curr) ∧
      let addr := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
        StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width
      domain addr = true ∧
      heapInMemoryStore (pre ++ [blockRep tag (pointers.set index replacement)] ++ post)
        a sp sp1 gens conf store (fun key => if key = addr then wordAddr conf replacement else memory key)
        domain limit := by
  obtain ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, globals,
    curr, other, currAligned, otherAligned, currStore, otherStore, nextStore,
    triggerStore, endStore, lengthStore, globInv, genInv, separated⟩ := heapMem
  obtain ⟨inDomain, heapNew⟩ :=
    wordHeap_blockStore conf tag pointers replacement curr pre post memory domain _ index bound separated
  have lengthEq : heapLength (pre ++ [blockRep tag pointers] ++ post) =
      heapLength (pre ++ [blockRep tag (pointers.set index replacement)] ++ post) := by
    simp [heapLength, List.map_append, List.sum_append, blockRep, elLength]
  refine ⟨curr, currStore, inDomain, ?_⟩
  refine ⟨?_, ?_, shift, lenNonzero, lenBound, shiftBound, globals, curr, other, currAligned, otherAligned,
    currStore, otherStore, nextStore, triggerStore, endStore, lengthStore, globInv, genInv, heapNew⟩
  · simpa only [← lengthEq] using bound1
  · simpa only [← lengthEq] using bound2

/-- A block in an encoded word heap has fewer than `2 ^ (width - 4)`
payload words. Flapjack proof infrastructure. -/
theorem wordHeap_blockRep_lengthBound {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (heap : ValueHeap width) (index tag : Nat)
    (roots : List (HeapAddress (WordLocW width))) (curr : BitVec width)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (blockRep tag roots))
    (assertion : wordHeap curr heap conf whole) :
    roots.length < 2 ^ (width - 4) := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index _ found
  subst heap
  subst index
  rw [wordHeapAppend] at assertion
  obtain ⟨_, restHeap, _, _, restAssertion⟩ := assertion
  change SetSep.star (wordEl _ (blockRep tag roots) conf) (wordHeap _ after conf) restHeap at restAssertion
  obtain ⟨_, _, _, elementAssertion, _⟩ := restAssertion
  simp only [wordEl, blockRep, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map] at elementAssertion
  obtain ⟨_, _, _, _, pureAssertion⟩ := elementAssertion
  exact pureAssertion.2.1

/-- HOL `memory_rel_UpdateCons`: writing the hole of an unfinalised mutable
block stores the new value's word at the hole's payload address. The four
source conjuncts are the single hypothesis `valid`; `&index` is
`Int.ofNat index`, `x + y ∈ dm` is `domain (x + y) = true` and `(x + y =+ w) m`
is the pointwise update of `memory`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_UpdateCons"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_updateCons {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (be : Bool) (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (h : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (bl : Bool) (nn : Nat) (ptr : WordLocW width) (index : Nat) (i : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (tag : Nat)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (cv : Flapjack.Compiler.Backend.DataSem.Value)
    (r : List Flapjack.Compiler.Backend.DataSem.Value)
    (valid : memoryRel conf be next refs space store memory domain
      ((h, w) :: (.refPtr bl nn, ptr) :: (.number (Int.ofNat index), i) :: vars) ∧
      sptLookup nn refs = some (.mutBlock tag false l cv r) ∧ goodDimindex width ∧ index = l.length) :
    ∃ ptrW iW x y : BitVec width, ptr = .word ptrW ∧ i = .word iW ∧
      getRealAddr conf store ptrW = some x ∧ getRealOffset iW = some y ∧ domain (x + y) = true ∧
      memoryRel conf be next (sptInsert nn (.mutBlock tag false l h r) refs) space store
        (fun key => if key = x + y then w else memory key) domain
        ((h, w) :: (.refPtr bl nn, ptr) :: (.number (Int.ofNat index), i) :: vars) := by
  obtain ⟨related, found, good, indexEq⟩ := valid
  subst indexEq
  have reordered : memoryRel conf be next refs space store memory domain
      ((.number (Int.ofNat l.length), i) :: (h, w) :: (.refPtr bl nn, ptr) :: vars) := by
    apply memoryRel_rearrange conf be next refs space store memory domain _ _ ?_ related
    intro pair member
    simp only [List.mem_cons] at member ⊢
    tauto
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, spaceBound, limitBound⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  have absInv' : absMlInv conf (h :: .refPtr bl nn :: ((Flapjack.Compiler.Backend.DataSem.Value.number
      (Int.ofNat l.length)) :: vars.map Prod.fst)) refs (roots, heap, be, a, sp, sp1, gens) limit next := by
    simpa using absInv
  have blFalse : bl = false := by
    obtain ⟨_, _, _, _, stackInv⟩ := absInv'
    obtain ⟨f, tf, _, _, _, _, _, _, _, pairs, _⟩ := stackInv
    cases pairs with
    | cons _ rest =>
      cases rest with
      | cons ptrRel _ =>
        have noThunk : ∀ mode value, sptLookup nn refs ≠ some (.thunk mode value) := by
          intro mode value
          simp [found]
        exact ((valueInv_refPtr_notThunk conf bl nn refs _ f tf heap noThunk).mp ptrRel).2.1 tag false l cv r found
  subst blFalse
  obtain ⟨p, rr, roots2, vs1, heap2, u, rootsEq, vsLookup, vsLen, stored, absNew⟩ :=
    updateMutBlock conf h nn _ refs roots heap be a sp sp1 gens limit next tag l cv r ⟨absInv', found⟩
  have lengthBound : vs1.length < 2 ^ (width - 4) := by
    obtain ⟨curr, other, _, _, _, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
    obtain ⟨active, inactive, _, activeHeap, _⟩ := heapAssertion
    exact wordHeap_blockRep_lengthBound conf heap p tag vs1 curr active vsLookup activeHeap
  have small : smallInt width (Int.ofNat l.length) := by
    rcases good with hw | hw <;> subst width <;> simp [smallInt] at lengthBound ⊢ <;> omega
  have indexWordEq := memoryRel_numberImp conf be next refs space store memory domain _ i _
    ⟨good, small, reordered⟩
  subst rootsEq
  cases rootWords with
  | cons valueAddr remaining =>
    cases remaining with
    | cons ptrAddr tail =>
      have wordEq : wordAddr conf rr = w := valueAddr
      have rootEq : ptr = .word (getAddr conf p u) := by simpa [wordAddr] using ptrAddr.symm
      obtain ⟨pre, post, heapEq, pEq⟩ := heapLookup_split heap p _ vsLookup
      subst heap
      subst p
      have canonical := heapStore_blockRep tag (vs1.set l.length rr) vs1 post pre (by simp)
      have heapEq2 : heap2 = pre ++ blockRep tag (vs1.set l.length rr) :: post :=
        congrArg Prod.fst (stored.symm.trans canonical)
      subst heap2
      have indexBound : l.length < vs1.length := by omega
      have heapMem' : heapInMemoryStore (pre ++ [blockRep tag vs1] ++ post)
          a sp sp1 gens conf store memory domain limit := by simpa [List.append_assoc] using heapMem
      obtain ⟨curr, currStore, domainEq, memoryNew⟩ :=
        heapInMemoryStore_blockStore conf tag vs1 rr pre post a sp sp1 gens store memory domain limit l.length
          indexBound heapMem'
      have address := getRealAddr_getAddr conf store _ (heapLength pre) _ curr u
        ⟨heapMem'.1, by simpa [List.append_assoc] using vsLookup, currStore, good⟩
      have offsetEq := getRealOffset_smallnum (width := width) l.length good
      have addrEq : curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
          (StackRemove.bytesInWord width + BitVec.ofNat width l.length * StackRemove.bytesInWord width) =
          curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
            StackRemove.bytesInWord width + BitVec.ofNat width l.length * StackRemove.bytesInWord width := by
        rw [← BitVec.add_assoc]
      refine ⟨getAddr conf (heapLength pre) u, smallnum (Int.ofNat l.length),
        curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre),
        StackRemove.bytesInWord width + BitVec.ofNat width l.length * StackRemove.bytesInWord width,
        rootEq, indexWordEq, ?_, offsetEq, ?_, ?_⟩
      · simpa [BitVec.mul_comm] using address.2
      · rw [addrEq]
        exact domainEq
      · rw [addrEq]
        refine ⟨pre ++ [blockRep tag (vs1.set l.length rr)] ++ post, limit, a, sp, sp1, gens,
          ?_, ?_, spaceBound, limitBound⟩
        · simpa [wordEq] using memoryNew
        · refine ⟨rr :: .pointer (heapLength pre) u :: roots2, ?_, ?_⟩
          · simpa [List.append_assoc] using absNew
          · exact .cons valueAddr (.cons ptrAddr tail)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
