module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.NumberVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Integer
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StateTstamps
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BignumHalt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocVarNary
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GetVars
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GetVarsCutEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.JoinEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreList
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RefRead
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.OddInter
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvs
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.AllocVarBinary
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Replicate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.RefArrayLemmas

@[expose] public section

/-! Reference-array allocation in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace RefArrayWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end RefArrayWitness

/-- A successful assignment in a sequence continues from the updated state.
Private infrastructure for the HOL `assign_RefArray` proof. -/
private theorem refSeqAssign {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign k e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setVar k v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- A successful store-name update in a sequence continues from the updated state.
Private infrastructure for the HOL `assign_RefArray` proof. -/
private theorem refSeqSet {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : WordStoreHOL) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (ok : ¬ (k = .handler ∨ k = .bitmapBase)) (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.set k e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setStore k v) := by
  simp only [WordSemStateFiniteExact.evaluate, if_neg ok, read, WordSemStateFiniteExact.fixClock]
  simp [WordSemStateFiniteExact.setStore]

/-- A successful memory store in a sequence continues from the updated state.
Private infrastructure for the HOL `assign_RefArray` proof. -/
private theorem refSeqStore {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (e : WordLangExpHOL (BitVec width)) (v : Nat)
    (a : BitVec width) (w : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some (.word a)) (hv : WordSemStateFiniteExact.getVar v t = some w)
    (dom : t.mdomain a = true) :
    WordSemStateFiniteExact.evaluate (.seq (.store e v) p) t =
      WordSemStateFiniteExact.evaluate p
        { t with memory := fun x => if x = a then w else t.memory x } := by
  simp [WordSemStateFiniteExact.evaluate, read, hv, WordSemStateFiniteExact.memStore, dom,
    WordSemStateFiniteExact.fixClock]

/-- Running the reference-array stub body from its entry state: it reserves
`i + 1` words below the end of the heap, writes the header, and tail-calls the
replication loop, returning the new pointer. Private infrastructure for the HOL
`assign_RefArray` proof, which performs the same steps inline. -/
private theorem refArrayCodeRun {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (entry : WordSemStateFiniteExact width C F) (i n l : Nat) (v : WordLocW width)
    (eoh trig curr hd : BitVec width) (m1 : BitVec width → WordLocW width)
    (good : width = 32 ∨ width = 64) (shiftBound : shiftLength conf < width)
    (wordBound : 4 * i < 2 ^ width) (clockBound : i < entry.clock)
    (read0 : sptLookup 0 entry.locals = some (.loc n l))
    (read2 : sptLookup 2 entry.locals = some (.word (BitVec.ofNat width (4 * i))))
    (read4 : sptLookup 4 entry.locals = some v)
    (trigRead : entry.store.lookup .triggerGC = some (.word trig))
    (eohRead : entry.store.lookup .endOfHeap = some (.word eoh))
    (currRead : entry.store.lookup .currHeap = some (.word curr))
    (code : sptLookup replicateLocation entry.code = some (5, replicateCode))
    (header : (BitVec.ofNat width (4 * i) <<< (width - conf.lenSize - 2)) |||
      makeHeader conf (2 : BitVec width) 0 = hd)
    (stored : storeList (eoh - wordSemBytesInWord * BitVec.ofNat width (i + 1))
      (.word hd :: List.replicate i v) entry.memory entry.mdomain = some m1) :
    ∃ m : Option Nat,
      WordSemStateFiniteExact.evaluate (refArrayCode conf) entry =
        (some (.result (.loc n l)
          [Build.makePtr conf (eoh - wordSemBytesInWord * BitVec.ofNat width (i + 1) - curr)
            (0 : BitVec width) i]),
          { entry with
            store := (entry.store.updateEq
              (.triggerGC, .word (trig - wordSemBytesInWord * BitVec.ofNat width (i + 1)))).updateEq
              (.endOfHeap, .word (eoh - wordSemBytesInWord * BitVec.ofNat width (i + 1))),
            memory := m1, clock := entry.clock - i - 1, locals := .ln,
            localsSize := some 0, stackMax := m }) ∧
      optionLe m (Option.map₂ max entry.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize entry.stack)
          (sptLookup replicateLocation entry.stackSize))) := by
  have widthPow : width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> decide
  have widthBig : 8 < width := by rcases good with h | h <;> omega
  have toNatSmall (k : Nat) (h : k < width) : (BitVec.ofNat width k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h widthPow)]
  have shiftAmtBound : wordShiftAmount width < width := by
    unfold wordShiftAmount; split <;> omega
  let B : BitVec width := wordSemBytesInWord
  let sz : BitVec width := (BitVec.ofNat width i + 1) <<< wordShiftAmount width
  let addr : BitVec width := eoh - sz
  let ptr : BitVec width := ((addr - curr) <<< (shiftLength conf - wordShiftAmount width)) ||| 1
  have szEq : sz = wordSemBytesInWord * BitVec.ofNat width (i + 1) := by
    rcases good with h | h <;> subst width <;>
      apply BitVec.eq_of_toNat_eq <;>
      simp [sz, wordShiftAmount, wordSemBytesInWord, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
        BitVec.toNat_ofNat, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.mul_mod, Nat.add_mod, Nat.mul_comm] <;> omega
  have quarter : BitVec.ofNat width (4 * i) >>> (2 : Nat) = BitVec.ofNat width i := by
    apply BitVec.eq_of_toNat_eq
    have iBelow : i < 2 ^ width := by omega
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt wordBound,
      Nat.mod_eq_of_lt iBelow]
  have e1 : entry.wordExp (.shift .lsl (.op .add [.shift .lsr (.var 2) (.const (BitVec.ofNat width 2)),
      .const 1]) (.const (BitVec.ofNat width (wordShiftAmount width)))) = some (.word sz) := by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, read2, wordShiftHOL,
      toNatSmall 2 (by omega), toNatSmall _ shiftAmtBound, Nat.not_le_of_gt shiftAmtBound,
      show ¬ width ≤ 2 by omega, theWords, wordOpHOL, wordOp, sz]
    rw [quarter]
  let s1 := entry.setVar 1 (.word sz)
  have e2 : s1.wordExp (.op .sub [.lookup .triggerGC, .var 1]) = some (.word (trig - sz)) := by
    simp [s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same,
      trigRead, theWords, wordOpHOL, wordOp]
  let s2 := s1.setStore .triggerGC (.word (trig - sz))
  have e3 : s2.wordExp (.op .sub [.lookup .endOfHeap, .var 1]) = some (.word addr) := by
    simp [s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore,
      sptLookup_sptInsert_same, HolFiniteMapExact.updateEq, FUPDATE_HOL, eohRead, theWords,
      wordOpHOL, wordOp, addr]
  let s3 := s2.setVar 1 (.word addr)
  have e4 : s3.wordExp (.var 1) = some (.word addr) := by
    simp [s3, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  let s4 := s3.setStore .endOfHeap (.word addr)
  have shiftPtrBound : shiftLength conf - wordShiftAmount width < width := by omega
  have e5 : s4.wordExp (.op .or [.shift .lsl (.op .sub [.var 1, .lookup .currHeap])
      (.const (BitVec.ofNat width (shiftLength conf - wordShiftAmount width))), .const 1]) =
      some (.word ptr) := by
    simp [s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore,
      sptLookup_sptInsert_same, HolFiniteMapExact.updateEq, FUPDATE_HOL, currRead, theWords,
      wordOpHOL, wordOp, wordShiftHOL, toNatSmall _ shiftPtrBound, Nat.not_le_of_gt shiftPtrBound, ptr,
      OrOp.or]
  let s5 := s4.setVar 3 (.word ptr)
  have headShift : width - conf.lenSize - 2 < width := by omega
  have e6 : s5.wordExp (.op .or [.shift .lsl (.var 2) (.const (BitVec.ofNat width (width - conf.lenSize - 2))),
      .const (makeHeader conf 2 0)]) = some (.word hd) := by
    simp [s5, s4, s3, s2, s1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore,
      sptLookup_sptInsert_ne, read2, theWords, wordOpHOL, wordOp, wordShiftHOL, toNatSmall _ headShift,
      Nat.not_le_of_gt headShift, OrOp.or, ← header]
  let s6 := s5.setVar 5 (.word hd)
  have storedAddr : storeList addr (.word hd :: List.replicate i v) entry.memory entry.mdomain = some m1 := by
    simpa [addr, szEq] using stored
  have dom : entry.mdomain addr = true := by
    simp only [storeList] at storedAddr
    split at storedAddr
    · assumption
    · contradiction
  have tail : storeList (addr + wordSemBytesInWord) (List.replicate i v)
      (fun x => if x = addr then .word hd else entry.memory x) entry.mdomain = some m1 := by
    simpa [storeList, dom] using storedAddr
  let s7 := { s6 with memory := fun x => if x = addr then .word hd else s6.memory x }
  obtain ⟨m, run, bound⟩ := Bignum.replicateCode_thm v n l (.word ptr) i addr s7 m1 0 1 4 2 3
    ⟨by simpa [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore] using code,
     by simpa [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore] using tail,
     by simp [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne, read0],
     by simp [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne, sptLookup_sptInsert_same],
     by simp [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne, read4],
     by simp [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne, read2],
     by simp [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne, sptLookup_sptInsert_same],
     wordBound,
     by simpa [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore] using clockBound⟩
  refine ⟨m, ?_, ?_⟩
  · unfold refArrayCode
    simp only [wordListSeq]
    rw [refSeqAssign entry 1 _ (.word sz) _ e1]
    rw [refSeqSet s1 .triggerGC _ (.word (trig - sz)) _ (by decide) e2]
    rw [refSeqAssign s2 1 _ (.word addr) _ e3]
    rw [refSeqSet s3 .endOfHeap _ (.word addr) _ (by decide) e4]
    rw [refSeqAssign s4 3 _ (.word ptr) _ e5]
    rw [refSeqAssign s5 5 _ (.word hd) _ e6]
    rw [refSeqStore s6 (.var 1) 5 addr (.word hd) _ (by
      simp [s6, s5, s4, s3, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne,
        sptLookup_sptInsert_same]) (by
      simp [s6, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same]) (by
      simpa [s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore] using dom)]
    rw [run]
    simp [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore,
      Build.makePtr, ptr, addr, szEq]
  · simpa [s7, s6, s5, s4, s3, s2, s1, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore] using bound

open Classical in
/-- The source state after the `RefArray` space reset. Private infrastructure
for the HOL `assign_RefArray` proof. -/
private noncomputable def sourceNext {C F : Type} (cut : DataSem.State C F) (i : Nat) (v : DataSem.Value) :
    DataSem.State C F :=
  { cut with
    space := 0
    safeForSpace := cut.safeForSpace && decide (DataSem.noThunksInRefs cut.refs ∧
      DataSem.sizeOfHeapArgs [.number (i : Int), v] cut + (i + 1) ≤ cut.limits.heapLimit)
    peakHeapLength := max cut.peakHeapLength (DataSem.sizeOfHeapArgs [.number (i : Int), v] cut + (i + 1)) }

/-- The source semantics of `RefArray`: a nonnegative length and an initial
value, with the space reset and a fresh reference holding the replicated array.
Private infrastructure for the HOL `assign_RefArray` proof. -/
private theorem refArraySource {C F : Type} (values : List DataSem.Value)
    (cut resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .refArray) values cut = .val (result, resultState)) :
    ∃ (i : Nat) (v : DataSem.Value), values = [.number (i : Int), v] ∧
      result = .refPtr true (DataSem.leastUnusedRef cut.refs) ∧
      resultState = { (DataSem.doStack (.memOp .refArray) values
        (DataSem.doLimSafe (sourceNext cut i v) (.memOp .refArray) values)) with
        refs := sptInsert (DataSem.leastUnusedRef cut.refs) (.valueArray (List.replicate i v)) cut.refs } := by
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;>
    try (solve | simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
      DataSem.applyNonFfi] at run)
  cases first <;> try (solve | simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset,
    DataSem.doAppAux, DataSem.applyNonFfi] at run)
  case number count =>
    by_cases negative : count < 0
    · simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
        DataSem.applyNonFfi, negative] at run
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ count)
      refine ⟨i, second, rfl, ?_⟩
      simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.spaceConsumed] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨rfl, rfl⟩

/-- Reference-array allocation satisfies the original assignment simulation,
including the bignum guard, allocation failure and the returning call into the
`RefArray` stub. The evaluator inherits the real-model assumption documented in
`docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_RefArray"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignRefArray_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .refArray)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  subst op
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some live =>
  obtain ⟨wordCut, words, wordCutRun, wordReads, sourceLen, wordLen, cutRelated, targetCutRelated⟩ :=
    stateRel_cutStateOpt_some conf l1 l2 source target locs args values live cut ⟨related, argsEq, cutEq⟩
  obtain ⟨i, v, valuesEq, resultEq, stateEq⟩ := refArraySource values cut resultState result run
  subst valuesEq
  subst resultEq
  subst stateEq
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, tail⟩⟩⟩ <;> simp at sourceLen
  have cutShape := cutStateOpt_some_eq live source cut cutEq
  have cutStackMax : cut.stackMax = source.stackMax := by rw [cutShape]
  have cutLimits : cut.limits = source.limits := by rw [cutShape]
  have cutRefs : cut.refs = source.refs := by rw [cutShape]
  have codeEq : (compileAssign conf n l dest (.memOp .refArray) [a1, a2] (some live)).1 =
      .seq (bignumHalt (adjustVar a1)) (.seq (.move 0 [(1, adjustVar a1)])
        (.seq (allocVar conf (min (2 ^ conf.lenSize) (2 ^ width / 16)) (sptListInsert [a1, a2] live))
          (.mustTerminate (.call (some ([adjustVar dest], adjustSets live, .skip, n, l))
            (some refArrayLocation) [adjustVar a1, adjustVar a2] none)))) := rfl
  rw [codeEq]
  have good := related.2.2.2.2.2.2.1
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have arch : DataSem.archSize source.limits = width := by
    rcases good with h | h <;> subst width <;> simp [DataSem.archSize, limits.2.2.1]
  have targetBound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have resultMaxLe : optionLe target.stackMax
      ({ (DataSem.doStack (.memOp .refArray) [.number (i : Int), v]
        (DataSem.doLimSafe (sourceNext cut i v) (.memOp .refArray) [.number (i : Int), v])) with
        refs := sptInsert (DataSem.leastUnusedRef cut.refs) (.valueArray (List.replicate i v)) cut.refs }).stackMax := by
    dsimp [DataSem.doStack, DataSem.doLimSafe, sourceNext]
    rw [cutStackMax, BackendProps.optionLe_max_right]
    exact Or.inl targetBound
  have sourceReads1 := (getVars_some_iff_data source.locals a1 _ _ _).2.mp argsEq
  have sourceReads2 := (getVars_some_iff_data source.locals a2 _ _ _).2.mp sourceReads1.2
  have reads := wordReads
  simp only [List.map_cons] at reads
  obtain ⟨w1, ws1, _, wread1, reads1⟩ := (getVars_some_iff_eq target _ _ _).2.mp reads
  obtain ⟨numberWord, wordEq, bigIff⟩ := stateRel_getVar_number_alt conf l1 l2 source
    target locs a1 (i : Int) w1 related sourceReads1.1 (by simpa [adjustVar, Nat.mul_comm] using wread1)
  subst w1
  obtain ⟨guardOut, guardEval, guardFfi, guardTargetFfi, guardMax⟩ :=
    evaluateBignumHalt2 conf l1 l2 source target locs (adjustVar a1) numberWord related wread1
  cases bit : numberWord.getLsbD 0 with
  | true =>
    simp only [bit, ↓reduceIte] at guardEval
    let fixed := { guardOut with
      clock := if target.clock < guardOut.clock then target.clock else guardOut.clock,
      termdep := target.termdep }
    refine ⟨some .notEnoughSpace, fixed, ?_, ?_, ?_⟩
    · rw [WordSemStateFiniteExact.evaluate, guardEval]
      rfl
    · intro _
      refine ⟨guardFfi.trans guardTargetFfi.symm,
        BackendProps.optionLe_trans _ _ _ ⟨guardMax, resultMaxLe⟩, ?_⟩
      intro _
      have notSmall := bigIff.mp bit
      have large : 2 ^ width / 8 ≤ i := by
        by_contra h
        apply notSmall
        unfold smallInt
        change -((2 ^ width / 8 : Nat) : Int) ≤ (i : Int) ∧ (i : Int) < ((2 ^ width / 8 : Nat) : Int)
        constructor
        · omega
        · exact_mod_cast (by omega : i < 2 ^ width / 8)
      have : ¬ i < 2 ^ width / 16 := by omega
      have archCut : DataSem.archSize cut.limits = width := by rw [cutLimits, arch]
      simp [DataSem.doStack, DataSem.doLimSafe, DataSem.limSafe, sourceNext, archCut, this]
    · simp
  | false =>
    have small : smallInt width (i : Int) := by
      by_contra h
      have bad := bigIff.mpr h
      simp [bit] at bad
    have roots := memoryRel_getVar a1 (holThe source.tstamps) target target.store source.space
      source target.memory
      ([(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
      target.mdomain conf target.be (.number (i : Int)) (.word numberWord) (by
        refine ⟨?_, sourceReads1.1, ?_⟩
        · simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        · simpa using wread1)
    have wordSmall := memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs
      source.space target.store target.memory target.mdomain (i : Int) (.word numberWord) _
      ⟨good, small, by simpa using roots⟩
    have smallNatWord (x : Nat) : smallnum ((x : Nat) : Int) = BitVec.ofNat width (4 * x) := by
      have positive : ¬ (x : Int) < 0 := by omega
      simp only [smallnum, if_neg positive]
      congr 1
    have wordEncoding : numberWord = BitVec.ofNat width (4 * i) := by
      cases wordSmall
      exact smallNatWord i
    have iBound : i < 2 ^ width / 8 := by
      have h := small.2
      change (i : Int) < ((2 ^ width / 8 : Nat) : Int) at h
      exact_mod_cast h
    have wideCut : ∃ wide, DataSem.cutEnv (sptListInsert [a1, a2] live) source.locals = some wide := by
      have narrowLive : ∀ k, sptMem k live → sptMem k source.locals := by
        cases narrow : DataSem.cutEnv live source.locals with
        | none => simp [DataSem.cutStateOpt, DataSem.cutState, narrow] at cutEq
        | some env =>
          unfold DataSem.cutEnv at narrow
          split at narrow
          · assumption
          · contradiction
      have allLive : ∀ k, sptMem k (sptListInsert [a1, a2] live) → sptMem k source.locals := by
        intro k mem
        change sptDomain (sptListInsert [a1, a2] live) k at mem
        rw [Flapjack.Compiler.Backend.BviToData.domain_listInsert] at mem
        rcases mem with member | member
        · exact DataProps.getVars_imp_domain _ k source.locals _ ⟨member, argsEq⟩
        · exact narrowLive k member
      exact ⟨sptMkWf (sptInter source.locals (sptListInsert [a1, a2] live)),
        by rw [DataSem.cutEnv, if_pos allLive]⟩
    obtain ⟨wide, wideRun⟩ := wideCut
    let target1 := target.setVar 1 (.word numberWord)
    have rel1 : stateRel conf l1 l2 source target1 none locs := by
      change stateRel conf l1 l2 source
        { target with locals := sptInsert 1 (.word numberWord) target.locals } none locs
      rw [stateRel_insert_1]
      exact related
    have read1 : target1.getVar 1 = some (.word (BitVec.ofNat width (4 * i))) := by
      simp [target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same, wordEncoding]
    have totalBound : 4 * i < 2 ^ width := by omega
    have limitBound : min (2 ^ conf.lenSize) (2 ^ width / 16) < 2 ^ width / 8 := by
      have minBound := Nat.min_le_right (2 ^ conf.lenSize) (2 ^ width / 16)
      rcases good with h | h <;> subst width <;> norm_num at minBound ⊢ <;> omega
    have moveEval : WordSemStateFiniteExact.evaluate (.move 0 [(1, adjustVar a1)]) target = (none, target1) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars, wread1, target1,
        setVars_singleton]
    cases allocRun : WordSemStateFiniteExact.evaluate
        (allocVar conf (min (2 ^ conf.lenSize) (2 ^ width / 16)) (sptListInsert [a1, a2] live)) target1 with
    | mk allocResult target2 =>
    have allocFacts := allocVar_binary conf l1 l2 source target1 locs a1 a2 live wide i v
      (min (2 ^ conf.lenSize) (2 ^ width / 16)) allocResult target2 rel1 wideRun argsEq read1 totalBound
      allocRun limitBound
    simp only [bit, Bool.false_eq_true, ↓reduceIte] at guardEval
    rw [WordSemStateFiniteExact.evaluate, guardEval]
    simp only [WordSemStateFiniteExact.fixClock, Nat.lt_irrefl, ↓reduceIte]
    rw [WordSemStateFiniteExact.evaluate, moveEval]
    simp only [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar,
      Nat.lt_irrefl, ↓reduceIte]
    change ∃ q r, WordSemStateFiniteExact.evaluate
      (.seq (allocVar conf (min (2 ^ conf.lenSize) (2 ^ width / 16)) (sptListInsert [a1, a2] live)) _)
        target1 = (q, r) ∧ _
    rw [WordSemStateFiniteExact.evaluate, allocRun]
    by_cases allocFail : allocResult = some .notEnoughSpace
    · subst allocResult
      have failed := allocFacts.1 rfl
      refine ⟨some .notEnoughSpace, _, rfl, ?_, ?_⟩
      · intro _
        refine ⟨?_, ?_, ?_⟩
        · exact failed.1.trans related.1.symm
        · dsimp [DataSem.doStack, DataSem.doLimSafe, sourceNext]
          rw [cutStackMax, BackendProps.optionLe_max_right]
          exact Or.inl failed.2.1
        · intro gc
          by_contra safe
          have safeTrue : ((DataSem.doStack (.memOp .refArray) [.number (i : Int), v]
              (DataSem.doLimSafe (sourceNext cut i v) (.memOp .refArray) [.number (i : Int), v]))).safeForSpace = true := by
            simpa using safe
          simp only [DataSem.doStack, DataSem.doLimSafe, sourceNext, DataSem.limSafe,
            Bool.and_eq_true, decide_eq_true_eq] at safeTrue
          have archCut : DataSem.archSize cut.limits = width := by rw [cutLimits, arch]
          have lim : 0 ≤ (i : Int) ∧ (i : Int).toNat < 2 ^ DataSem.archSize cut.limits / 16 ∧
              (i : Int).toNat < 2 ^ cut.limits.lengthLimit := by
            exact @of_decide_eq_true _ (Classical.propDecidable _) safeTrue.1.1
          simp only [Int.toNat_natCast, cutLimits, limits.2.1, arch] at lim
          have withinLimit : i < min (2 ^ conf.lenSize) (2 ^ width / 16) :=
            Nat.lt_min.mpr ⟨lim.2.2, lim.2.1⟩
          have noThunks : DataSem.noThunksInRefs source.refs := by
            simpa [cutRefs] using safeTrue.1.2.2.1
          have exceeded := failed.2.2 ⟨gc, withinLimit, noThunks⟩
          rw [cutStateOpt_imp_cutLocals live source cut cutEq] at exceeded
          have fits := safeTrue.1.2.2.2
          rw [cutLimits] at fits
          omega
      · simp
    · obtain ⟨withinLimit, rel2, _, _, _, _, _, resultNone⟩ := allocFacts.2 allocFail
      subst allocResult
      have clocks : target1.clock = target2.clock := by
        have first := related.2.1
        have second := rel2.2.1
        simpa [target1, WordSemStateFiniteExact.setVar, first] using second.symm
      simp only [WordSemStateFiniteExact.fixClock, clocks, Nat.lt_irrefl, ↓reduceIte]
      let allocatedSource := { source with locals := wide, space := i + 1 }
      let allocatedTarget := { target2 with termdep := target1.termdep }
      have allocatedRel : stateRel conf l1 l2 allocatedSource allocatedTarget none locs := rel2
      have allocatedDepth : allocatedTarget.termdep > 1 := by
        simpa [allocatedTarget, target1, WordSemStateFiniteExact.setVar] using depth
      have wideReads : DataSem.getVars [a1, a2] wide = some [.number (i : Int), v] := by
        apply getVars_cutEnv _ source.locals wide _ _
        refine ⟨wideRun, argsEq, ?_⟩
        intro k mem
        change sptDomain (sptListInsert [a1, a2] live) k
        rw [Flapjack.Compiler.Backend.BviToData.domain_listInsert]
        exact Or.inl mem
      obtain ⟨newWords, newReads, newLength⟩ := stateRel_getVars conf l1 l2
        allocatedSource allocatedTarget locs [a1, a2] [.number (i : Int), v] allocatedRel wideReads
      rcases newWords with _ | ⟨new1, _ | ⟨new2, _ | ⟨_, _⟩⟩⟩ <;> simp at newLength
      have newMemory := memoryRel_getVars conf allocatedTarget.be (holThe allocatedSource.tstamps)
        allocatedSource allocatedSource.space allocatedTarget.store allocatedTarget.memory
        allocatedTarget.mdomain allocatedTarget
        ([(theGlobal allocatedSource.global, holFapply allocatedTarget.store .globals)] ++
          flatStack allocatedSource.stack allocatedTarget.stack)
        [a1, a2] [.number (i : Int), v] [new1, new2] (by
          refine ⟨?_, wideReads, newReads⟩
          simpa using allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      have blockRoot := newMemory
      simp only [List.zip_cons_cons, List.zip_nil_left, List.cons_append, List.nil_append] at blockRoot
      have firstWord := memoryRel_numberImp conf allocatedTarget.be (holThe allocatedSource.tstamps)
        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
        allocatedTarget.mdomain (i : Int) new1 _ ⟨good, small, blockRoot⟩
      have memory2 := memoryRel_tl conf allocatedTarget.be (holThe allocatedSource.tstamps)
        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
        allocatedTarget.mdomain _ _ blockRoot
      simp only [List.map_cons] at newReads
      have newRead1 := (getVars_some_iff allocatedTarget _ _ _ _).2.mp newReads
      have newRead2 := (getVars_some_iff allocatedTarget _ _ _ _).2.mp newRead1.2
      have newCount : allocatedTarget.getVar (adjustVar a1) =
          some (.word (BitVec.ofNat width (4 * i))) := by
        have read := newRead1.1
        rw [firstWord, smallNatWord] at read
        exact read
      have newValue : allocatedTarget.getVar (adjustVar a2) = some new2 := newRead2.1
      have narrowRun : DataSem.cutEnv live source.locals = some cut.locals := by
        cases narrow : DataSem.cutEnv live source.locals with
        | none => simp [DataSem.cutStateOpt, DataSem.cutState, narrow] at cutEq
        | some env =>
          simp only [DataSem.cutStateOpt, DataSem.cutState, narrow] at cutEq
          rw [← Option.some.inj cutEq]
      have wideNarrow := cutEnv_cutEnv_listInsert [a1, a2] live source.locals wide cut.locals
        ⟨wideRun, narrowRun⟩
      have subLookup : ∀ key value, sptLookup key cut.locals = some value →
          sptLookup key wide = some value := by
        intro key value found
        rw [DataLive.cutEnv_lookup live wide cut.locals wideNarrow key] at found
        split at found
        · exact found
        · contradiction
      let vars := joinEnv cut.locals
          (sptToAList (sptInter allocatedTarget.locals (adjustSet cut.locals))) ++
          [(theGlobal allocatedSource.global, holFapply allocatedTarget.store .globals)] ++
          flatStack allocatedSource.stack allocatedTarget.stack
      have narrowMemory : memoryRel conf allocatedTarget.be (holThe allocatedSource.tstamps)
          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
          allocatedTarget.mdomain ((v, new2) :: vars) := by
        apply memoryRel_rearrange conf allocatedTarget.be (holThe allocatedSource.tstamps)
          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
          allocatedTarget.mdomain _ _ ?_ memory2
        intro pair member
        have subJoin : pair ∈ joinEnv cut.locals
            (sptToAList (sptInter allocatedTarget.locals (adjustSet cut.locals))) →
            pair ∈ joinEnv allocatedSource.locals
              (sptToAList (sptInter allocatedTarget.locals (adjustSet allocatedSource.locals))) := by
          intro inJoin
          exact joinEnv_submap_mem cut.locals wide allocatedTarget.locals allocatedTarget.locals pair
            ⟨subLookup, by intros; assumption, inJoin⟩
        simp only [vars, List.mem_cons, List.mem_append] at member ⊢
        aesop
      let key := DataSem.leastUnusedRef cut.refs
      have fresh : ¬ sptDomain allocatedSource.refs key := by
        intro domain
        obtain ⟨value, found⟩ := (sptDomain_iff_lookup _ key).mp domain
        have no := DataSem.leastUnusedRef_unused cut.refs
        rw [cutRefs] at no
        simp only [allocatedSource, key, cutRefs] at found
        rw [found] at no
        contradiction
      have heapMem := allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨_, _, _, _, _, _, heapIn, _⟩ := heapMem
      have lenBound : conf.lenSize + 7 < width := heapIn.2.2.2.2.1
      have lenSizeBound : i < 2 ^ conf.lenSize := (Nat.lt_min.mp withinLimit).1
      have widthQuarter : 2 ^ width / 16 = 2 ^ (width - 4) := by
        rcases good with h | h <;> rw [h] <;> norm_num
      have lenWidthBound : i < 2 ^ (width - 4) := by
        have h := (Nat.lt_min.mp withinLimit).2
        omega
      have tagBound : 2 < 2 ^ (width - conf.lenSize - 2) := by
        have h : 2 ^ 3 ≤ 2 ^ (width - conf.lenSize - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have tagSmall : 2 < 2 ^ width / 16 := by rcases good with h | h <;> rw [h] <;> decide
      have headerEq : encodeHeader (width := width) conf 2 i =
          some (makeHeader conf (BitVec.ofNat width 2) i) := by
        simp [encodeHeader, tagBound, tagSmall, lenWidthBound, lenSizeBound]
      obtain ⟨eoh, curr, trig, m1, eohRead, trigRead, currRead, stored, finalMem⟩ :=
        memoryRel_refArray (tagWidth := width) conf allocatedTarget.be (holThe allocatedSource.tstamps)
          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
          allocatedTarget.mdomain v new2 vars i (makeHeader conf (BitVec.ofNat width 2) i) key
          ⟨narrowMemory, headerEq, fresh, by simp [allocatedSource], good⟩
      let addr := eoh - wordSemBytesInWord * BitVec.ofNat width (i + 1)
      let trig1 := trig - wordSemBytesInWord * BitVec.ofNat width (i + 1)
      let resultPointer : WordLocW width := Build.makePtr conf (addr - curr) (0 : BitVec width) i
      have shiftBound : shiftLength conf < width := allocatedRel.2.2.2.2.2.2.2.1
      have headerCode : (BitVec.ofNat width (4 * i) <<< (width - conf.lenSize - 2)) |||
          makeHeader conf (2 : BitVec width) 0 = makeHeader conf (BitVec.ofNat width 2) i := by
        have timesFour : BitVec.ofNat width (4 * i) = (BitVec.ofNat width i <<< (2 : Nat)) := by
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
            Nat.mul_mod, Nat.mul_comm]
        have addShift : 2 + (width - conf.lenSize - 2) = width - conf.lenSize := by omega
        simp only [makeHeader]
        rw [timesFour, ← BitVec.shiftLeft_add, addShift]
        simp [BitVec.or_assoc]
      have stubMember : (refArrayLocation, 3, refArrayCode conf) ∈ stubs (width := width) conf := by
        simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
          fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
          replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
          divLocation, modLocation, compare1Location, compareLocation, equal1Location,
          equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
          byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
          installLocation, installCodeLocation, installDataLocation, dummyLocation,
          appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
          unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
      have replicateMember : (replicateLocation, 5, replicateCode) ∈ stubs (width := width) conf := by
        simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
          fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
          replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
          divLocation, modLocation, compare1Location, compareLocation, equal1Location,
          equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
          byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
          installLocation, installCodeLocation, installDataLocation, dummyLocation,
          appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
          unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
      have codeRead : sptLookup refArrayLocation allocatedTarget.code = some (3, refArrayCode conf) :=
        allocatedRel.2.2.2.2.1.2.1 _ stubMember
      have replicateRead : sptLookup replicateLocation allocatedTarget.code = some (5, replicateCode) :=
        allocatedRel.2.2.2.2.1.2.1 _ replicateMember
      obtain ⟨gcCut, gcCutRun⟩ := cutEnv_imp_wordCutEnv conf l1 l2 allocatedSource
        allocatedTarget locs live cut.locals ⟨allocatedRel, wideNarrow⟩
      obtain ⟨env1, env2, envRun, envEq⟩ :=
        cutEnv_imp_cutEnvs (adjustSets live) allocatedTarget.locals gcCut gcCutRun
      let mustState := { allocatedTarget with
        clock := wordSemMustTerminateLimit width
        termdep := allocatedTarget.termdep - 1 }
      let callInputs : List (WordLocW width) := [.loc n l, .word (BitVec.ofNat width (4 * i)), new2]
      let callSize := sptLookup refArrayLocation mustState.stackSize
      let entry := WordSemStateFiniteExact.callEnv callInputs callSize
        (WordSemStateFiniteExact.pushEnv (env1, env2) none (WordSemStateFiniteExact.decClock mustState))
      have enoughClock : i < entry.clock := by
        simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          WordSemStateFiniteExact.decClock, mustState]
        dsimp [wordSemMustTerminateLimit]
        omega
      obtain ⟨calleeStackMax, calleeRun, calleeStackBound⟩ := refArrayCodeRun conf entry i n l new2
        eoh trig curr (makeHeader conf (BitVec.ofNat width 2) i) m1 good shiftBound totalBound enoughClock
        (by simp [entry, WordSemStateFiniteExact.callEnv, callInputs, sptFromList2, sptInsert, sptLookup])
        (by simp [entry, WordSemStateFiniteExact.callEnv, callInputs, sptFromList2, sptInsert, sptLookup])
        (by simp [entry, WordSemStateFiniteExact.callEnv, callInputs, sptFromList2, sptInsert, sptLookup])
        (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
              WordSemStateFiniteExact.decClock, mustState] using trigRead)
        (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
              WordSemStateFiniteExact.decClock, mustState] using eohRead)
        (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
              WordSemStateFiniteExact.decClock, mustState] using currRead)
        (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
              WordSemStateFiniteExact.decClock, mustState] using replicateRead)
        headerCode
        (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
              WordSemStateFiniteExact.decClock, mustState] using stored)
      let finalSource := { (DataSem.doStack (.memOp .refArray) [.number (i : Int), v]
        (DataSem.doLimSafe (sourceNext cut i v) (.memOp .refArray) [.number (i : Int), v])) with
        refs := sptInsert key (.valueArray (List.replicate i v)) cut.refs }
      let finalTarget := { allocatedTarget with
        store := (allocatedTarget.store.update (.endOfHeap, .word addr)).update (.triggerGC, .word trig1)
        memory := m1 }
      have finalRoot : memoryRel conf finalTarget.be (holThe finalSource.tstamps) finalSource.refs
          finalSource.space finalTarget.store finalTarget.memory finalTarget.mdomain
          ((.refPtr true key, resultPointer) ::
            (joinEnv finalSource.locals (sptToAList (sptInter finalTarget.locals (adjustSet finalSource.locals))) ++
              [(theGlobal finalSource.global, holFapply finalTarget.store .globals)] ++
              flatStack finalSource.stack finalTarget.stack)) := by
        simpa [finalSource, finalTarget, vars, allocatedSource, DataSem.doStack, DataSem.doLimSafe,
          sourceNext, cutShape, holFapply, HolFiniteMapExact.update, FUPDATE, resultPointer, addr,
          trig1, key] using finalMem
      have finalBase := memoryRel_tl conf finalTarget.be (holThe finalSource.tstamps) finalSource.refs
        finalSource.space finalTarget.store finalTarget.memory finalTarget.mdomain _ _ finalRoot
      have finalRelated : stateRel conf l1 l2 finalSource finalTarget none locs := by
        rcases allocatedRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
          htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hgood, hshift, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using hffi
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using hclock
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using hhandler
        · exact hgc
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using hcode
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource, codeOracleRel, HolFiniteMapExact.update, FUPDATE] using horacle
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using htstamp
        · simpa [finalTarget, HolFiniteMapExact.update, FUPDATE] using hglobal
        · exact hzero
        · intro k found
          change (sptLookup k cut.locals).isSome = true at found
          cases lookup : sptLookup k cut.locals with
          | none => simp [lookup] at found
          | some value =>
            have wideFound := subLookup k value lookup
            apply hpresent k
            simp [allocatedSource, wideFound]
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using hstack
        · exact hlocs
        · exact hacc
        · dsimp [finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext]
          rw [cutStackMax, BackendProps.optionLe_max_right]
          exact Or.inl hmax
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using hsizes
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource] using hlocals
        · simpa [finalTarget, finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext, cutShape,
            allocatedSource, limitsInv, HolFiniteMapExact.update, FUPDATE] using hlim
        · simpa [finalTarget] using finalBase
      have finalLocals : finalSource.locals = cut.locals := rfl
      have narrowSelf : DataSem.cutEnv live finalSource.locals = some finalSource.locals := by
        rw [finalLocals]
        exact cutEnv_idempotent live source.locals cut.locals narrowRun
      have finalCutRun : wordSemCutEnv (adjustSets live) finalTarget.locals = some gcCut := by
        simpa [finalTarget] using gcCutRun
      have finalCutRel : stateRel conf l1 l2 finalSource { finalTarget with locals := gcCut } none locs := by
        simpa using stateRel_cutEnv_cutEnv conf l1 l2 finalSource finalTarget locs live
          finalSource.locals gcCut ⟨finalRelated, narrowSelf, finalCutRun⟩
      have cutNames : ∀ key, sptMem key finalSource.locals → sptMem key live := by
        intro key present
        obtain ⟨value, found⟩ := (sptMem_iff_lookup key finalSource.locals).mp present
        have cutRun := narrowSelf
        unfold DataSem.cutEnv at cutRun
        split at cutRun
        · simp only [Option.some.injEq] at cutRun
          conv at found => rw [← cutRun]
          rw [sptLookup_mkWf, sptLookup_sptInterCases] at found
          cases h : sptLookup key live with
          | none => simp [h] at found
          | some entry => exact (sptMem_iff_lookup key live).mpr ⟨entry, h⟩
        · contradiction
      have wordCutEq : gcCut = sptUnion (sptInter finalTarget.locals (adjustSet live))
          (sptInter finalTarget.locals (.ls ())) := by
        have wordRun := finalCutRun
        by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (.ls ()) finalTarget.locals <;>
          by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSet live) finalTarget.locals <;>
          simp [wordSemCutEnv, wordSemCutEnvs, wordSemCutNames, adjustSets, h1, h2] at wordRun
        exact wordRun.symm
      have cutLookup : ∀ key, sptMem key (adjustSet live) →
          sptLookup key gcCut = sptLookup key finalTarget.locals := by
        intro key member
        obtain ⟨value, found⟩ := (sptMem_iff_lookup key (adjustSet live)).mp member
        rw [wordCutEq, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases]
        cases sptLookup key finalTarget.locals <;> simp [found]
      have rootsEq : sptInter gcCut (adjustSet finalSource.locals) =
          sptInter finalTarget.locals (adjustSet finalSource.locals) := by
        apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
        intro key
        rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
        cases lookup : sptLookup key (adjustSet finalSource.locals) with
        | none => simp
        | some value =>
          have member := (sptMem_iff_lookup key (adjustSet finalSource.locals)).mpr ⟨value, lookup⟩
          obtain ⟨name, eq, present⟩ := (adjustSet_domain finalSource.locals key).mp member
          have kept := (adjustSet_domain live key).mpr ⟨name, eq, cutNames name present⟩
          rw [cutLookup key kept]
      have cutRoot : memoryRel conf finalTarget.be (holThe finalSource.tstamps) finalSource.refs
          finalSource.space finalTarget.store finalTarget.memory finalTarget.mdomain
          ((.refPtr true key, resultPointer) ::
            (joinEnv finalSource.locals (sptToAList (sptInter gcCut (adjustSet finalSource.locals))) ++
              [(theGlobal finalSource.global, holFapply finalTarget.store .globals)] ++
              flatStack finalSource.stack finalTarget.stack)) := by
        rw [rootsEq]
        exact finalRoot
      have firstLive : ¬ sptDomainEmpty (adjustSets live).1 := by
        intro empty
        have absent := empty 0
        exact absent (by simp [adjustSets, sptMem, sptDomain, sptLookup])
      have mustClock : mustState.clock ≠ 0 := by
        simp only [mustState]
        dsimp [wordSemMustTerminateLimit]
        omega
      have argsMust : WordSemStateFiniteExact.getVars [adjustVar a1, adjustVar a2] mustState =
          some [.word (BitVec.ofNat width (4 * i)), new2] := by
        change sptLookup (adjustVar a1) allocatedTarget.locals = _ at newCount
        change sptLookup (adjustVar a2) allocatedTarget.locals = _ at newValue
        simp [mustState, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, newCount, newValue]
      have codeMust : sptLookup refArrayLocation mustState.code = some (3, refArrayCode conf) := codeRead
      have envMust : wordSemCutEnvs (adjustSets live) mustState.locals = some (env1, env2) := envRun
      cases envList : wordSemEnvToList env2 mustState.permute with
      | mk entries permutation =>
      have cutsWf := cutEnvs_wf (adjustSets live) mustState.locals env1 env2 envRun
      have firstRestore : sptFromAList (sptToAList env1) = env1 := by
        apply (sptEqThm _ _ ⟨sptWfFromAList _, cutsWf.1⟩).2
        intro key
        exact sptLookup_sptFromAList_sptToAList key env1
      have secondRestore : sptFromAList entries = env2 := by
        apply (sptEqThm _ _ ⟨sptWfFromAList _, cutsWf.2⟩).2
        intro key
        rw [sptLookup_sptFromAList]
        exact (wordSemEnvToListLookupEquiv env2 mustState.permute entries permutation envList).1 key
      let returned := { entry with
        store := (entry.store.updateEq (.triggerGC, .word trig1)).updateEq (.endOfHeap, .word addr)
        memory := m1
        clock := entry.clock - i - 1
        locals := .ln
        localsSize := some 0
        stackMax := calleeStackMax }
      let restored := { returned with
        locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList env1))
        stack := mustState.stack
        localsSize := mustState.localsSize }
      have popRun : WordSemStateFiniteExact.popEnv returned = some restored := by
        simp only [returned, restored, entry, WordSemStateFiniteExact.callEnv,
          WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.popEnv,
          WordSemStateFiniteExact.decClock, envList]
      have restoredDomain : sptDomainEqUnion restored.locals env1 env2 := by
        intro key
        change sptMem key (sptUnion (sptFromAList entries) (sptFromAList (sptToAList env1))) ↔ _
        rw [secondRestore, firstRestore, sptMem_sptUnion]
        exact or_comm
      have directCall : WordSemStateFiniteExact.evaluate
          (.call (some ([adjustVar dest], adjustSets live, .skip, n, l))
            (some refArrayLocation) [adjustVar a1, adjustVar a2] none) mustState =
          (none, WordSemStateFiniteExact.setVars [adjustVar dest] [resultPointer] restored) := by
        rw [WordSemStateFiniteExact.evaluate]
        simp only [argsMust, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc,
          wordSemFindCode, codeMust, List.length_cons, List.length_nil, if_true, firstLive,
          not_false_eq_true, List.nodup_cons, List.mem_nil_iff, not_false_eq_true, envMust, mustClock]
        simp only [List.nodup_nil, true_and, not_true_eq_false, false_or, if_false]
        rw [WordSemStateFiniteExact.fix_clock_evaluate]
        simp only [dif_neg, not_false_eq_true]
        have directCallee : WordSemStateFiniteExact.evaluate (refArrayCode conf)
            (WordSemStateFiniteExact.callEnv
              [.loc n l, .word (BitVec.ofNat width (4 * i)), new2]
              (sptLookup refArrayLocation mustState.stackSize)
              (WordSemStateFiniteExact.pushEnv (env1, env2) none
                (WordSemStateFiniteExact.decClock mustState))) =
            (some (.result (.loc n l) [resultPointer]), returned) := by
          exact calleeRun
        rw [directCallee]
        simp only [List.length_cons, List.length_nil]
        change (match WordSemStateFiniteExact.popEnv returned with | _ => _) = _
        rw [popRun]
        simp [restoredDomain, WordSemStateFiniteExact.evaluate]
      let finalCallState := { WordSemStateFiniteExact.setVars [adjustVar dest] [resultPointer] restored with
        clock := allocatedTarget.clock, termdep := allocatedTarget.termdep }
      have nonzeroDepth : allocatedTarget.termdep ≠ 0 := by omega
      have terminateCall : WordSemStateFiniteExact.evaluate
          (.mustTerminate (.call (some ([adjustVar dest], adjustSets live, .skip, n, l))
            (some refArrayLocation) [adjustVar a1, adjustVar a2] none)) allocatedTarget =
          (none, finalCallState) := by
        rw [WordSemStateFiniteExact.evaluate]
        simp only [nonzeroDepth]
        rw [directCall]
        rfl
      let usage := Option.map₂ (· + ·) (wordSemStackSize finalTarget.stack) finalTarget.localsSize
      have pushedStack : wordSemStackSize (WordSemStateFiniteExact.pushEnv (env1, env2) none
          (WordSemStateFiniteExact.decClock mustState)).stack = usage := by
        simp only [WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock,
          envList, wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame]
        change wordSemOptionAdd finalTarget.localsSize (wordSemStackSize finalTarget.stack) = usage
        dsimp only [usage]
        cases finalTarget.localsSize <;> cases wordSemStackSize finalTarget.stack <;>
          simp [wordSemOptionAdd, Nat.add_comm]
      have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
        cases x <;> cases y <;> rfl
      have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
        cases x <;> cases y <;> rfl
      have entryMaxEq : entry.stackMax = Option.map₂ max
          (Option.map₂ max finalTarget.stackMax usage)
          (Option.map₂ (· + ·) usage (sptLookup refArrayLocation finalTarget.stackSize)) := by
        simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          WordSemStateFiniteExact.decClock, envList, callSize, optMax, optAdd]
        rw [← pushedStack]
        simp [WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, envList, optMax,
          mustState, finalTarget]
      have entryStack : wordSemStackSize entry.stack = usage := pushedStack
      have entryFrames : entry.stackSize = finalTarget.stackSize := by
        simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          WordSemStateFiniteExact.decClock, mustState, finalTarget]
      have sourceStackEq : wordSemStackSize finalTarget.stack = DataSem.sizeOfStack source.stack := by
        simpa [finalTarget, allocatedSource] using
          stackRel_sizeOfStack allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.1
      have frameEq : finalTarget.stackSize = source.stackFrameSizes := by
        simpa [finalTarget, allocatedSource] using allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have sizeEq : finalTarget.localsSize = source.localsSize := by
        simpa [finalTarget, allocatedSource] using allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have resultMaxEq : finalSource.stackMax = Option.map₂ max source.stackMax
          (Option.map₂ (· + ·) (Option.map₂ max (sptLookup refArrayLocation finalTarget.stackSize)
            (sptLookup replicateLocation finalTarget.stackSize)) usage) := by
        simp only [finalSource, DataSem.doStack, DataSem.doLimSafe, sourceNext,
          DataSem.stackConsumed, cutShape]
        simp [usage, frameEq, sizeEq, sourceStackEq]
      have optionBound (a u r1 r2 d mm : Option Nat) (h : optionLe a d)
          (hm : optionLe mm (Option.map₂ max (Option.map₂ max (Option.map₂ max a u)
            (Option.map₂ (· + ·) u r1)) (Option.map₂ (· + ·) u r2))) :
          optionLe mm (Option.map₂ max d (Option.map₂ (· + ·) (Option.map₂ max r1 r2) u)) := by
        cases a <;> cases u <;> cases r1 <;> cases r2 <;> cases d <;> cases mm <;>
          simp [optionLe] at h hm ⊢
        all_goals omega
      have oldMaxBound : optionLe finalTarget.stackMax source.stackMax := by
        simpa [finalTarget, allocatedSource] using
          allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have calleeUpper : optionLe calleeStackMax finalSource.stackMax := by
        rw [resultMaxEq]
        apply optionBound finalTarget.stackMax usage _ _ source.stackMax calleeStackMax oldMaxBound
        rw [← entryMaxEq, ← entryStack, ← entryFrames]
        exact calleeStackBound
      have calleeLower := WordSemStateFiniteExact.evaluate_stack_max_le (refArrayCode conf) entry
        (some (.result (.loc n l) [resultPointer])) _ calleeRun
      have usageBound : optionLe usage calleeStackMax := by
        apply BackendProps.optionLe_trans _ entry.stackMax _
        refine ⟨?_, by simpa using calleeLower⟩
        rw [entryMaxEq, BackendProps.optionLe_max_right, BackendProps.optionLe_max_right]
        exact Or.inl (Or.inr (BackendProps.optionLe_refl _))
      let cutWithStack := { finalTarget with locals := gcCut, stackMax := calleeStackMax }
      have cutStackRel : stateRel conf l1 l2 finalSource cutWithStack none locs := by
        rcases finalCutRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
          htstamp, hglobal, hzero, hpresent, hstack, hlocs, _, _, hsizes, hlocals, hlim, hmem⟩
        exact ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
          hzero, hpresent, hstack, hlocs, usageBound, calleeUpper, hsizes, hlocals, hlim, hmem⟩
      have stackDestRel := Flapjack.Compiler.Backend.DataToWord.Proofs.stateRel_insertRoot
        conf l1 l2 finalSource cutWithStack locs dest (.refPtr true key) resultPointer cutStackRel cutRoot
      have storesEqual : (allocatedTarget.store.updateEq (.triggerGC, .word trig1)).updateEq
            (.endOfHeap, .word addr) =
          (allocatedTarget.store.update (.endOfHeap, .word addr)).update (.triggerGC, .word trig1) := by
        apply HolFiniteMapExact.ext_lookup
        intro k
        cases k <;> simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE]
      have finalCallShape : finalCallState =
          { cutWithStack.setVar (adjustVar dest) resultPointer with permute := permutation } := by
        simp [finalCallState, setVars_singleton, restored, returned, entry, callInputs, callSize,
          WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          WordSemStateFiniteExact.decClock, firstRestore, secondRestore, ← envEq,
          mustState, finalTarget, cutWithStack,
          WordSemStateFiniteExact.setVar, storesEqual]
        simpa [mustState] using congrArg Prod.snd envList
      have finalCallRel : stateRel conf l1 l2 (DataSem.setVar dest (.refPtr true key) finalSource)
          finalCallState none locs := by
        rw [finalCallShape]
        exact stackDestRel
      refine ⟨none, finalCallState, terminateCall, ?_, ?_⟩
      · simp
      · intro _
        exact ⟨finalCallRel, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
