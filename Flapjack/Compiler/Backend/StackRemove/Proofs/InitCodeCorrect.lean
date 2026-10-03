import Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitMake
import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitReadMemory
import Mathlib.Data.BitVec

/-! The StackRemove initializer correctness theorem `init_code_thm`
(`stack_removeProofScript.sml` 3225-3837).
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm

/-- A word whose value is an in-range offset of another. -/
theorem addMulOfNat {width : Nat} [NeZero width] (good : goodDimindex width)
    (a c : BitVec width) (n : Nat) (h : c.toNat = a.toNat + n * (width / 8)) :
    c = a + bytesInWord width * BitVec.ofNat width n := by
  have hc := c.isLt
  rcases good with hw | hw <;> subst hw <;>
  · simp only [bytesInWord] at *; norm_num at *; bv_omega

/-- Heap and stack word counts from the computed initial pointers. -/
theorem spaceCounts {width : Nat} [NeZero width] (good : goodDimindex width)
    (p2 reg3 p4 : BitVec width) (heapLength stackLength : Nat)
    (regEqN : reg3.toNat = p2.toNat + heapLength * (width / 8))
    (endEqN : p4.toNat = reg3.toNat + stackLength * (width / 8))
    (long : 49 ≤ stackLength) :
    ((reg3 + bytesInWord width * BitVec.ofNat width 48) - p2).toNat / (width / 8) - 48 =
        heapLength ∧
      ((p4 - bytesInWord width) - (reg3 + bytesInWord width * BitVec.ofNat width 48)).toNat /
        (width / 8) = stackLength - 49 := by
  have h4 := p4.isLt
  rcases good with hw | hw <;> subst hw <;>
  · simp only [bytesInWord] at *; norm_num at *; constructor <;> bv_omega

/-- When the third pointer lies within the margins and below the heap bound,
the initializer keeps it, rounded to a double word (source 3240-3247). -/
theorem thirdInRange {width : Nat} [NeZero width] (good : goodDimindex width) (maxHeap : Nat)
    (p2 p3 p4 : BitVec width)
    (lo : p2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ p3)
    (hi : p3 ≤ p4 - BitVec.ofNat width maxStackAlloc * bytesInWord width)
    (hm : (-1 * p2 + p3).toNat ≤ maxHeap * (bytesInWord width).toNat)
    (hb : (bytesInWord width).toNat * maxHeap < 2 ^ width) :
    roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
      (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap)) =
      ((p3 + -1 * p2) >>> (wordShiftAmount width + 1)) <<< (wordShiftAmount width + 1) + p2 := by
  have adj : adjustedThird p3 (middleWord p2 p4) (p2 + marginWord width)
      (p4 - marginWord width) = p3 := by
    unfold adjustedThird marginWord
    rw [if_neg (by rw [BitVec.lt_def]; rw [BitVec.le_def] at lo; omega),
      if_neg (by rw [BitVec.lt_def]; rw [BitVec.le_def] at hi; omega)]
  have sub : p3 + -1 * p2 = p3 - p2 := by
    rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg]
  have sub' : -1 * p2 + p3 = p3 - p2 := by rw [BitVec.add_comm, sub]
  rw [sub'] at hm
  have shr : shrunkThird p2 p3 (maxHeapWord width maxHeap) = p3 := by
    unfold shrunkThird
    rw [if_neg]
    rw [BitVec.lt_def]
    unfold maxHeapWord
    have hb' : maxHeap * (bytesInWord width).toNat < 2 ^ width := by rw [Nat.mul_comm]; exact hb
    rw [if_pos hb', BitVec.toNat_mul, BitVec.toNat_ofNat]
    have bpos : 0 < (bytesInWord width).toNat := by
      unfold bytesInWord; rcases good with h | h <;> subst h <;> decide
    have : maxHeap % 2 ^ width * (bytesInWord width).toNat % 2 ^ width =
        maxHeap * (bytesInWord width).toNat := by
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ bpos) hb'),
        Nat.mod_eq_of_lt hb']
    omega
  rw [adj, shr, roundedThird, sub]

/-- An in-range offset by whole words. -/
theorem addWordsNat {width : Nat} [NeZero width] (good : goodDimindex width) (a : BitVec width)
    (n : Nat) (h : a.toNat + n * (width / 8) < 2 ^ width) :
    (a + bytesInWord width * BitVec.ofNat width n).toNat = a.toNat + n * (width / 8) := by
  rcases good with hw | hw <;> subst hw <;>
  · simp only [bytesInWord] at *; norm_num at *; bv_omega

/-- The final stack word address. -/
theorem lastWordAddress {width : Nat} [NeZero width] (base : BitVec width) (n : Nat)
    (long : 49 ≤ n) :
    base + bytesInWord width * BitVec.ofNat width 48 +
        bytesInWord width * BitVec.ofNat width (n - 49) =
      base + bytesInWord width * BitVec.ofNat width n - bytesInWord width := by
  have split : n = 48 + (n - 49) + 1 := by omega
  conv => rhs; rw [split]
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_add]
  simp only [← BitVec.add_assoc]
  rw [show bytesInWord width * BitVec.ofNat width 1 = bytesInWord width by simp,
    BitVec.add_sub_cancel]

/-- The original limit calculation repeats the initializer's pointer
arithmetic: its third register is the code's rounded heap end. -/
theorem getStackHeapLimit_eq {width : Nat} [NeZero width] (maxHeap : Nat) (p2 p3 p4 : BitVec width) :
    InitLimits.getStackHeapLimit maxHeap (p2, p3, p4) =
      InitLimitsDouble.getStackHeapLimitDouble (p2.toNat / (width / 8))
        ((roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
          (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap))).toNat /
          (width / 8))
        (p4.toNat / (width / 8)) := by
  have negAdd : ∀ x y : BitVec width, -1 * x + y = y - x := by
    intro x y; rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
  have adj : (if p2 + bytesInWord width * BitVec.ofNat width maxStackAlloc ≤ p3 ∧
        p3 ≤ p4 - bytesInWord width * BitVec.ofNat width maxStackAlloc then p3
      else p2 + ((-1 * p2 + p4) >>> (wordShiftAmount width + 1)) <<< wordShiftAmount width) =
      adjustedThird p3 (middleWord p2 p4) (p2 + marginWord width) (p4 - marginWord width) := by
    unfold adjustedThird middleWord marginWord
    rw [negAdd, BitVec.mul_comm (bytesInWord width), Nat.add_comm (wordShiftAmount width) 1,
      BitVec.add_comm p2]
    split_ifs <;> first
      | rfl
      | exact BitVec.add_comm _ _
      | (exfalso; simp only [BitVec.le_def, BitVec.lt_def] at *; omega)
  have mh : (if maxHeap * (bytesInWord width).toNat < 2 ^ width then
        bytesInWord width * BitVec.ofNat width maxHeap else -1) = maxHeapWord width maxHeap := by
    unfold maxHeapWord
    split_ifs
    · exact BitVec.mul_comm _ _
    · simp
  unfold InitLimits.getStackHeapLimit InitLimits.getStackHeapLimitPrime
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [adj, mh]
  congr 2
  unfold roundedThird shrunkThird
  simp only [negAdd]
  split_ifs
  · rw [BitVec.add_sub_cancel, show p2 + maxHeapWord width maxHeap - p2 =
      maxHeapWord width maxHeap by rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _,
      BitVec.add_comm p2]
  · rw [BitVec.add_comm p2]

/-- A framed word list in a functional heap cannot wrap around the address
space (source 3746-3770, via the original `word_list_wrap`). -/
theorem wordListNoWrap {width : Nat} [NeZero width] {β : Type} (good : goodDimindex width)
    (F : ((BitVec width × β) → Prop) → Prop) (a : BitVec width) (ls : List β)
    (m : BitVec width → β) (d : BitVec width → Prop)
    (hyp : SetSep.star F (Misc.wordList a ls) (SetSep.fun2Set (m, d))) :
    ls.length ≤ 2 ^ width / (width / 8) := by
  by_contra long
  obtain ⟨x, xs, y, ys, b, split, rfl⟩ :=
    WordListMemory.wordListWrap a ls ⟨good, by omega⟩
  rw [split] at hyp
  obtain ⟨_, rest, outer, _, A, B, inner, hA, hB⟩ := hyp
  have inA := StackHeap.wordListNth b (x :: xs) A 0 (by simp) hA
  have inB := StackHeap.wordListNth b (y :: ys) B 0 (by simp) hB
  simp only [BitVec.mul_zero, BitVec.add_zero, List.getElem_cons_zero] at inA inB
  have whole : ∀ e, rest e → SetSep.fun2Set (m, d) e := fun e member => by
    rw [← outer.1]; exact Or.inr member
  have wx := ((SetSep.fun2SetThm m d b x).mp (whole _ (by rw [← inner.1]; exact Or.inl inA))).1
  have wy := ((SetSep.fun2SetThm m d b y).mp (whole _ (by rw [← inner.1]; exact Or.inr inB))).1
  subst wx; subst wy
  exact inner.2 _ ⟨inA, inB⟩

theorem holLast_append_singleton {β : Type} [Nonempty β] (l : List β) (x : β) :
    holLast (l ++ [x]) = x := by
  induction l with
  | nil => simp [holLast]
  | cons h t ih =>
    cases t with
    | nil => simp [holLast]
    | cons h' t' => simpa [holLast] using ih

/-- Half of an even heap of whole words. -/
theorem halfHeapWord {width : Nat} [NeZero width] (good : goodDimindex width)
    (p2 reg3 : BitVec width) (heapLength : Nat)
    (regEqN : reg3.toNat = p2.toNat + heapLength * (width / 8)) (even : heapLength % 2 = 0) :
    (reg3 - p2) >>> (1 : Nat) = BitVec.ofNat width (heapLength / 2) * bytesInWord width := by
  have h3 := reg3.isLt
  rcases good with hw | hw <;> subst hw <;>
  · simp only [bytesInWord] at *; norm_num at *; bv_omega

/-- Lookup through a folded update list whose keys are distinct. -/
theorem foldUpdate_lookup_mem {α β : Type} [DecidableEq α] :
    ∀ (entries : List (α × β)) (f : α → Option β) (key : α) (value : β),
      (entries.map Prod.fst).Nodup → (key, value) ∈ entries →
      FUPDATE_LIST_HOL f entries key = some value := by
  intro entries
  induction entries with
  | nil => intro _ _ _ _ member; simp at member
  | cons e es ih =>
    intro f key value nodup member
    simp only [List.map_cons, List.nodup_cons] at nodup
    simp only [FUPDATE_LIST_HOL, List.foldl_cons] at ⊢
    rcases List.mem_cons.mp member with rfl | inTail
    · -- the head key is absent from the rest, so it survives the remaining updates
      have keep : ∀ (es : List (α × β)) (g : α → Option β), key ∉ es.map Prod.fst →
          es.foldl (fun g entry => FUPDATE_HOL g entry) g key = g key := by
        intro es
        induction es with
        | nil => intros; rfl
        | cons e' es' ih' =>
          intro g absent
          simp only [List.map_cons, List.mem_cons, not_or] at absent
          simp only [List.foldl_cons]
          rw [ih' _ absent.2]
          simp [FUPDATE_HOL, absent.1]
      rw [keep es _ nodup.1]
      simp [FUPDATE_HOL]
    · exact ih _ key value nodup.2 inTail

/-- Alignment makes the shift round trip the identity. -/
theorem alignedShift {width : Nat} [NeZero width] (good : goodDimindex width) (w : BitVec width)
    (aligned : holByteAligned w = true) :
    (w >>> wordShiftAmount width) <<< wordShiftAmount width = w := by
  have hlog : holLOG2 (width / 8) = wordShiftAmount width := by
    rw [holLOG2_eq_log2 (by rcases good with h | h <;> subst h <;> decide)]
    unfold wordShiftAmount
    rcases good with h | h <;> subst h <;> decide
  unfold holByteAligned holAligned at aligned
  rw [hlog, decide_eq_true_iff, holAlign_eq_shift] at aligned
  exact aligned

/-- The initial store keys are distinct after translation. -/
theorem storeKeysNodup :
    ((StoreName.currHeap :: storeList).map StackSemRegisterTransfers.storeOfSyntax).Nodup := by
  decide

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about the initializer run. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

open Classical in
/-- Complete original initializer correctness theorem. From the original
`init_code_pre`, code relation, compile-oracle equation and register bounds,
halt-label entry and heap lower bound, the native evaluator run of the actual
`init_code` never returns a result, and its normal post-state satisfies every
original conclusion: the pointer-register facts (including the conditional
heap-end equation), the full `state_rel` to the actual `init_reduce` state,
FFI and domain preservation, the original `init_prop` at the limits read from
the input pointers, and agreement of the heap region with the input memory.
No target run, post-state relation or heap representation is assumed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_code_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem initCodeThm {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (s : StackSemStateFiniteExact width C F) (jump : Bool) (bounds : BitVec width × BitVec width)
    (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hyp : InitCodePre.initCodePre pointer bitmaps dataSpace s ∧
      codeRelHOL jump bounds pointer code s.code ∧
      s.compileOracle = (fun index =>
        let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      maxStackAlloc ≤ maxHeap) :
    match StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
    | (some _, _) => False
    | (none, t) =>
      (∃ w2 w3 w4 : BitVec width,
        s.regs.lookup 2 = some (.word w2) ∧ holByteAligned w2 = true ∧
        t.regs.lookup (pointer + 2) = some (.word w2) ∧
        s.regs.lookup 4 = some (.word w4) ∧ holByteAligned w4 = true ∧ w2 < w4 ∧
        t.regs.lookup pointer = some (.word (w4 - bytesInWord width)) ∧
        (w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3 ∧
          w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width ∧
          (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat ∧
          (bytesInWord width).toNat * maxHeap < 2 ^ width →
          t.regs.lookup (pointer + 1) =
            some (.word ((((w3 + -1 * w2) >>> (wordShiftAmount width + 1)) <<<
              (wordShiftAmount width + 1)) + w2 +
              bytesInWord width * BitVec.ofNat width storeList.length))) ∧
        s.regs.lookup 3 = some (.word w3)) ∧
      stateRelHOL jump bounds pointer
        (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t) t ∧
      t.ffi = s.ffi ∧
      InitProp.initProp generateGc maxHeap dataSpace
        (InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s))
        (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t) ∧
      s.mdomain = t.mdomain ∧ s.shMdomain = t.shMdomain ∧
      (let t0 := InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t
       SetSep.fun2Set (s.memory, fun a => t0.mdomain a = true) =
         SetSep.fun2Set (t.memory, fun a => t0.mdomain a = true)) := by
  obtain ⟨pre, codeRel, oracleEq, oracleBound, errLab, maxOk⟩ := hyp
  obtain ⟨p2, p3, p4, bp, good, k8, entry, saveRegs, noStack, noStore, noAlloc, read2, read3,
    read4, mem0, mem1, mem2, mem3, mem4, le, big, al2, al4, albp, cbEmpty, heap⟩ := pre
  have a2 := (byteAligned_iff good p2).mp al2
  have a4 := (byteAligned_iff good p4).mp al4
  have bnat : (bytesInWord width).toNat = width / 8 := by
    rcases good with h | h <;> subst h <;> rfl
  have diff : (p4 - p2).toNat = p4.toNat - p2.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact le)]
  have big' : 1024 * (width / 8) ≤ p4.toNat - p2.toNat := by
    rw [← diff]
    have : (1024 * bytesInWord width).toNat = 1024 * (width / 8) := by
      rcases good with h | h <;> subst h <;> rfl
    omega
  have bpos : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  obtain ⟨adjLe, shrLe, heapLength, stackLength, regEqN, endEqN, even, heapLe, heapLow,
    stackLow⟩ := initLayout good maxHeap maxOk p2 p3 p4 le big' a2 a4
  set reg3 := roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
    (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap)) with hreg3
  have regEq := addMulOfNat good p2 reg3 heapLength regEqN
  have endEq := addMulOfNat good reg3 p4 stackLength endEqN
  have count : (p4 - p2).toNat / (bytesInWord width).toNat = heapLength + stackLength := by
    rw [diff, bnat, endEqN, regEqN]
    rw [show p2.toNat + heapLength * (width / 8) + stackLength * (width / 8) - p2.toNat =
      (heapLength + stackLength) * (width / 8) by rw [Nat.add_mul]; omega]
    exact Nat.mul_div_cancel _ bpos
  rw [count] at heap
  have long : storeList.length + 1 ≤ stackLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at stackLow; omega
  obtain ⟨heapValues, storeValues, restValues, last, hlen, slen, rlen, split⟩ :=
    initHeapSplit _ p2 reg3 p4 heapLength stackLength _ _ regEq endEq long heap
  set P0 := SetSep.star (Misc.wordList bp (bitmaps.map WordLocW.word))
    (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
      dataSpace) with hP0
  set H := Misc.wordList p2 heapValues with hH
  set S := Misc.wordList reg3 storeValues with hS
  set R := Misc.wordList (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)
    restValues with hR
  set D : BitVec width → Prop := fun a => s.mdomain a = true with hD
  -- header reads and domain
  have headerSplit : SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H (SetSep.fun2Set (s.memory, D)) := by
    rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, last)) by ac_rfl]
    exact split
  have heapBig : 5 ≤ heapLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at heapLow; omega
  have domain5 : ∀ i, i < 5 →
      s.mdomain (p2 + BitVec.ofNat width i * bytesInWord width) = true := by
    intro i hi
    have := (framedListRead _ p2 heapValues s.memory D headerSplit i (by omega)).2
    rw [BitVec.mul_comm] at this
    exact this
  -- the final stack word
  have lastDomain : s.mdomain (p4 - bytesInWord width) = true := by
    obtain ⟨part, single, sub⟩ := starRightMember _ _ _ split
    have member := sub (p4 - bytesInWord width, last) (by rw [single])
    exact ((SetSep.fun2SetThm _ _ _ _).mp member).2
  have written := StoreListCodeThm.writeWord (.word 0) last (p4 - bytesInWord width)
    (SetSep.star (SetSep.star (SetSep.star P0 H) S) R) s.memory D
    (by rw [SetSep.starComm]; exact split)
  have storeHeap : SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0)))
      (SetSep.fun2Set ((fun key => if key = p4 - bytesInWord width then .word 0
        else s.memory key), D)) := by
    rw [show SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, .word 0)) by ac_rfl]
    exact written
  obtain ⟨t, run, shape, t0, t1, t2, t3, t4, t5, t6, t7, tk, tk1, tk2, tOther, tHeap⟩ :=
    runInitCode generateGc maxHeap pointer s p2 p3 p4 bp _ _ _ _ good k8 read2 read3 read4
      domain5 mem0 rfl rfl rfl rfl lastDomain entry storeValues _ slen storeHeap
  rw [run]
  dsimp only
  -- computed initializer pointers in the post-state
  have sl48 : storeList.length = 48 := rfl
  have basePtr : wordSemTheWord (holFapply t.regs (pointer + 1)) =
      reg3 + bytesInWord width * BitVec.ofNat width storeList.length := by
    rw [holFapply_of_lookup tk1]; rfl
  have heapPtr : wordSemTheWord (holFapply t.regs (pointer + 2)) = p2 := by
    rw [holFapply_of_lookup tk2]; rfl
  have stackPtr : wordSemTheWord (holFapply t.regs pointer) = p4 - bytesInWord width := by
    rw [holFapply_of_lookup tk]; rfl
  have heapSpace : ((reg3 + bytesInWord width * BitVec.ofNat width storeList.length) - p2).toNat /
      (width / 8) - storeList.length = heapLength := by
    rw [sl48]
    exact (spaceCounts good p2 reg3 p4 heapLength stackLength regEqN endEqN (by omega)).1
  have stackSpace : ((p4 - bytesInWord width) -
      (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)).toNat / (width / 8) =
      stackLength - (storeList.length + 1) := by
    rw [sl48]
    exact (spaceCounts good p2 reg3 p4 heapLength stackLength regEqN endEqN (by omega)).2
  have ffiEq : t.ffi = s.ffi := (congrArg (·.ffi) shape).trans rfl
  have mdomEq : t.mdomain = s.mdomain := (congrArg (·.mdomain) shape).trans rfl
  have shmEq : t.shMdomain = s.shMdomain := (congrArg (·.shMdomain) shape).trans rfl
  have codeEq : t.code = s.code := (congrArg (·.code) shape).trans rfl
  have cbEq : t.codeBuffer = s.codeBuffer := (congrArg (·.codeBuffer) shape).trans rfl
  have oracleT : t.compileOracle = s.compileOracle := (congrArg (·.compileOracle) shape).trans rfl
  have saveT : t.ffiSaveRegs = s.ffiSaveRegs := (congrArg (·.ffiSaveRegs) shape).trans rfl
  have flagsT : t.useStack = s.useStack ∧ t.useStore = s.useStore ∧ t.useAlloc = s.useAlloc :=
    ⟨(congrArg (·.useStack) shape).trans rfl, (congrArg (·.useStore) shape).trans rfl,
      (congrArg (·.useAlloc) shape).trans rfl⟩
  set T0 := InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t
    with hT0
  have heapDom : ∀ a, T0.mdomain a = true ↔ addresses p2 heapLength a := by
    intro a
    simp only [hT0, InitReduce.initReduce]
    erw [heapPtr, basePtr, heapSpace, decide_eq_true_iff]
  set NS := Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
    (MemVal.memVal t.regs)) with hNS
  have tHeapLast : SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) H (SetSep.fun2Set (t.memory, D)) := by
    rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) H =
      SetSep.star NS (SetSep.star (SetSep.star (SetSep.star P0 H) R)
        (SetSep.one (p4 - bytesInWord width, .word 0))) by ac_rfl]
    exact tHeap
  -- the stored initial values
  have storeVal : ∀ name, name ∈ StoreName.currHeap :: storeList →
      T0.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) =
        some (MemVal.memVal t.regs (storeInit generateGc pointer name)) := by
    intro name member
    simp only [hT0, InitReduce.initReduce, HolFiniteMapExact.lookup_updateListEq]
    apply foldUpdate_lookup_mem
    · rw [List.map_map]
      convert storeKeysNodup using 2
      funext n
      simp only [Function.comp_apply]
      split <;> rfl
    · refine List.mem_map.mpr ⟨name, member, ?_⟩
      split <;> rename_i h <;> simp [h, MemVal.memVal]
  have bitmapBaseLookup : T0.store.lookup .bitmapBase =
      some (.word (bp >>> wordShiftAmount width)) := by
    have := storeVal .bitmapBase (by decide)
    simpa [storeInit, MemVal.memVal, holFapply_of_lookup t3,
      StackSemRegisterTransfers.storeOfSyntax] using this
  have currLookup : T0.store.lookup .currHeap = some (.word p2) := by
    have := storeVal .currHeap (by decide)
    simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
      StackSemRegisterTransfers.storeOfSyntax] using this
  have bitmapBack : (bp >>> wordShiftAmount width) <<< wordShiftAmount width = bp :=
    alignedShift good bp albp
  -- the initial stack
  set base := reg3 + bytesInWord width * BitVec.ofNat width storeList.length with hbase
  have lastAddr : base + bytesInWord width * BitVec.ofNat width restValues.length =
      p4 - bytesInWord width := by
    rw [rlen, hbase, sl48, endEq, lastWordAddress reg3 stackLength (by omega)]
  have stackHeap : Misc.wordList base (restValues ++ [.word 0]) =
      SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0)) := by
    rw [StackHeap.wordListAppend, wordListSingleton, lastAddr]
  have stackSp : T0.stackSpace = stackLength - (storeList.length + 1) := by
    simp only [hT0, InitReduce.initReduce]
    erw [stackPtr, basePtr, stackSpace]
  have stackVal : T0.stack = restValues ++ [.word 0] := by
    have read := InitReadMemory.wordListImpReadMem t.memory D (restValues ++ [.word 0]) base
      (SetSep.star (SetSep.star NS P0) H) (by
        rw [stackHeap]
        rw [show SetSep.star (SetSep.star (SetSep.star NS P0) H)
          (SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0))) =
          SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
            (SetSep.one (p4 - bytesInWord width, .word 0))) H by ac_rfl]
        exact tHeapLast)
    have lenEq : (restValues ++ [WordLocW.word 0]).length = T0.stackSpace + 1 := by
      rw [stackSp]; simp [rlen]
    rw [lenEq] at read
    simp only [hT0, InitReduce.initReduce] at read ⊢
    erw [stackPtr, basePtr] at read ⊢
    exact read
  have baseNat : base.toNat = reg3.toNat + storeList.length * (width / 8) :=
    addWordsNat good reg3 storeList.length (by
      have := p4.isLt
      have : storeList.length * (width / 8) ≤ stackLength * (width / 8) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  refine ⟨⟨p2, p3, p4, read2, al2, tk2, read4, al4, ?lt, tk, ?impl, read3⟩, ?rel, ffiEq, ?prop,
    mdomEq.symm, shmEq.symm, ?mem⟩
  case lt =>
    rw [BitVec.lt_def]; omega
  case impl =>
    rintro ⟨lo, hi, hm, hb⟩
    rw [tk1, ← thirdInRange good maxHeap p2 p3 p4 lo hi hm hb]
  case mem =>
    have agree : ∀ a, addresses p2 heapLength a → s.memory a = t.memory a := by
      intro a member
      obtain ⟨i, hi, rfl⟩ := (mem_addresses heapLength p2 a).mp member
      rw [BitVec.mul_comm]
      rw [(framedListRead _ p2 heapValues s.memory D headerSplit i (by omega)).1,
        (framedListRead _ p2 heapValues t.memory D tHeapLast i (by omega)).1]
    funext entry
    rcases entry with ⟨a, v⟩
    apply propext
    rw [SetSep.fun2SetThm, SetSep.fun2SetThm, heapDom]
    constructor
    · rintro ⟨eq, dom⟩; exact ⟨(agree a dom).symm.trans eq, dom⟩
    · rintro ⟨eq, dom⟩; exact ⟨(agree a dom).trans eq, dom⟩
  case rel =>
    have memEq : memoryHOL T0.memory (fun a => T0.mdomain a = true) = H := by
      have domEq : (fun a => T0.mdomain a = true) = addresses p2 heapLength := by
        funext a; exact propext (heapDom a)
      rw [domEq]
      have framed : SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
          (SetSep.one (p4 - bytesInWord width, .word 0))) H) SetSep.emp
          (SetSep.fun2Set (t.memory, D)) := by
        rw [SetSep.starComm _ SetSep.emp, StackHeap.starEmptyLeft]; exact tHeapLast
      have inMem := WordListMemory.wordListInMemory p2 heapValues _ _ t.memory D
        ⟨framed, good, by
          rw [hlen, bnat]
          have := p4.isLt
          have : heapLength * (width / 8) ≤ heapLength * (width / 8) + stackLength * (width / 8) :=
            Nat.le_add_right _ _
          omega⟩
      rw [hlen] at inMem
      exact inMem
    have storeEq : wordStoreHOL base T0.store = NS := by
      unfold wordStoreHOL
      rw [hNS, WordListReverse.wordListEqRev]
      simp only [List.length_map, List.length_reverse]
      rw [BitVec.mul_comm (BitVec.ofNat width storeList.length)]
      congr 1
    have stackEq : Misc.wordList base T0.stack =
        SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0)) := by
      rw [stackVal, stackHeap]
    have positionEq : T0.dataBuffer.position = bp + bytesInWord width *
        BitVec.ofNat width bitmaps.length := by
      simp only [hT0, InitReduce.initReduce]
      erw [holFapply_of_lookup t3]
      exact congrArg (· + _) bitmapBack
    unfold stateRelHOL
    refine ⟨by simp [hT0, InitReduce.initReduce], by simp [hT0, InitReduce.initReduce],
      flagsT.1.trans noStack, flagsT.2.1.trans noStore, flagsT.2.2.trans noAlloc,
      by simp [hT0, InitReduce.initReduce], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      oracleT.trans oracleEq, oracleBound, good, fun _ _ => rfl, codeEq ▸ codeRel,
      codeEq ▸ errLab, tk2.trans currLookup.symm, saveT ▸ saveRegs,
      by rw [bitmapBaseLookup]; rfl, InitReduce.initReduceStackSpace _ _ _ _ _ _ _ _ t, ?_⟩
    rw [bitmapBaseLookup]
    simp only [Option.map_some, wordLocWToGeneric, theSomeWord, bitmapBack]
    refine ⟨by rw [positionEq]; rfl, ?_⟩
    rw [tk1]
    simp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [baseNat, regEqN]; simp only [maxStackAlloc] at heapLow ⊢
      have : 255 * (width / 8) ≤ (heapLength + storeList.length) * (width / 8) :=
        Nat.mul_le_mul_right _ heapLow
      rw [Nat.add_mul] at this; omega
    · rw [stackVal, baseNat, bnat]
      simp only [List.length_append, List.length_singleton, rlen]
      have := p4.isLt
      have split : stackLength = storeList.length + (stackLength - (storeList.length + 1)) + 1 := by
        omega
      have : (width / 8) * (stackLength - (storeList.length + 1) + 1) +
          storeList.length * (width / 8) = stackLength * (width / 8) := by
        conv => rhs; rw [split]
        ring
      omega
    · rw [tk, stackSp, ← rlen, lastAddr]
    · rw [memEq, stackEq, storeEq, mdomEq]
      simp only [hT0, InitReduce.initReduce, List.append_nil]
      rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star H
          (Misc.wordList bp (bitmaps.map WordLocW.word)))
          (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
            dataSpace)) NS) (SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0))) =
        SetSep.star NS (SetSep.star (SetSep.star (SetSep.star P0 H) R)
          (SetSep.one (p4 - bytesInWord width, .word 0))) by rw [hP0]; ac_rfl]
      exact tHeap
  case prop =>
    have half := halfHeapWord good p2 reg3 heapLength regEqN even
    have pointers : InitLimits.readPointers s = (p2, p3, p4) := by
      simp [InitLimits.readPointers, read2, read3, read4, holThe, wordSemTheWord]
    have limits : InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s) =
        (stackLength - storeList.length, heapLength / 2) := by
      rw [pointers, getStackHeapLimit_eq, ← hreg3, InitLimitsDouble.getStackHeapLimitDouble,
        endEqN, regEqN]
      have d2 : p2.toNat / (width / 8) * (width / 8) = p2.toNat := Nat.div_mul_cancel
        (Nat.dvd_of_mod_eq_zero a2)
      rw [Nat.add_mul_div_right _ _ bpos, Nat.add_mul_div_right _ _ bpos]
      congr 1 <;> omega
    have stackLen : T0.stack.length = stackLength - storeList.length := by
      rw [stackVal]; simp [rlen]; omega
    have word2 : p2 + bytesInWord width + bytesInWord width = p2 + 2 * bytesInWord width := by
      ring
    have word3 : p2 + bytesInWord width + bytesInWord width + bytesInWord width =
        p2 + 3 * bytesInWord width := by ring
    have word4 : p2 + bytesInWord width + bytesInWord width + bytesInWord width +
        bytesInWord width = p2 + 4 * bytesInWord width := by ring
    rw [word2, mem2] at t6; rw [word3, mem3] at t7; rw [word4, mem4] at t1; rw [mem1] at t4
    have halfX := half
    rw [hreg3] at halfX
    have positionEq : T0.dataBuffer.position = bp + bytesInWord width *
        BitVec.ofNat width bitmaps.length := by
      simp only [hT0, InitReduce.initReduce]
      erw [holFapply_of_lookup t3]
      exact congrArg (· + _) bitmapBack
    have look : ∀ name, name ∈ StoreName.currHeap :: storeList →
        T0.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) =
          some (MemVal.memVal t.regs (storeInit generateGc pointer name)) := storeVal
    -- the bitmap/data lists fit in the address space
    have fits : bitmaps.length + dataSpace + 1 < 2 ^ width := by
      set X := SetSep.star (SetSep.star (SetSep.star H S) R)
        (SetSep.one (p4 - bytesInWord width, last)) with hX
      have pre : SetSep.star (SetSep.star X (Misc.wordList bp (bitmaps.map WordLocW.word)))
          (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
            dataSpace) (SetSep.fun2Set (s.memory, D)) := by
        rw [show SetSep.star (SetSep.star X (Misc.wordList bp (bitmaps.map WordLocW.word)))
          (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
            dataSpace) =
          SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
            (SetSep.one (p4 - bytesInWord width, last)) by rw [hX, hP0]; ac_rfl]
        exact split
      obtain ⟨ds, dlen, listed⟩ := (starWordListExists _ _ _ _).mp pre
      have joined : SetSep.star X (Misc.wordList bp (bitmaps.map WordLocW.word ++ ds))
          (SetSep.fun2Set (s.memory, D)) := by
        rw [StackHeap.wordListAppend, List.length_map, SetSep.starAssoc]
        exact listed
      have bound := wordListNoWrap good X bp _ s.memory D joined
      simp only [List.length_append, List.length_map, dlen] at bound
      have : 2 ^ width / (width / 8) ≤ 2 ^ width / 4 :=
        Nat.div_le_div_left (by rcases good with h | h <;> subst h <;> decide) (by decide)
      have : 2 ^ width / 4 + 1 < 2 ^ width := by
        rcases good with h | h <;> subst h <;> norm_num
      omega
    have spaceLeft : T0.dataBuffer.spaceLeft = dataSpace := by
      simp [hT0, InitReduce.initReduce]
    have bufferNil : T0.dataBuffer.buffer = [] := by simp [hT0, InitReduce.initReduce]
    have cbT0 : T0.codeBuffer = s.codeBuffer := cbEq
    have stackSpEq : T0.stack.length = T0.stackSpace + 1 := by
      rw [stackLen, stackSp]; omega
    have heapHalf : SetSep.star (Misc.wordListExists p2 (heapLength / 2))
        (Misc.wordListExists (p2 + (reg3 - p2) >>> (1 : Nat)) (heapLength / 2))
        (SetSep.fun2Set (T0.memory, fun a => T0.mdomain a = true)) := by
      have domEq : (fun a => T0.mdomain a = true) = addresses p2 heapLength := by
        funext a; exact propext (heapDom a)
      rw [domEq, half, BitVec.mul_comm, ← WordListMemory.wordListExistsAdd,
        show heapLength / 2 + heapLength / 2 = heapLength by omega]
      exact WordListMemory.wordListExistsAddresses T0.memory heapLength p2
        ⟨by rw [Nat.mul_comm]; have := reg3.isLt; omega, good⟩
    unfold InitProp.initProp
    refine ⟨p2, p2 + (reg3 - p2) >>> (1 : Nat), bp >>> wordShiftAmount width, heapLength / 2,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
        StackSemRegisterTransfers.storeOfSyntax] using look .currHeap (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
        StackSemRegisterTransfers.storeOfSyntax] using look .nextFree (by decide)
    · cases generateGc <;>
        simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2, holFapply_of_lookup t2,
          StackSemRegisterTransfers.storeOfSyntax] using look .triggerGC (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t2,
        StackSemRegisterTransfers.storeOfSyntax] using look .endOfHeap (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t2,
        StackSemRegisterTransfers.storeOfSyntax] using look .otherHeap (by decide)
    · exact bitmapBaseLookup
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t5, halfX,
        StackSemRegisterTransfers.storeOfSyntax] using look .heapLength (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .progStart (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .allocSize (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .globals (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
        StackSemRegisterTransfers.storeOfSyntax] using look .globReal (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .handler (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .genStart (by decide)
    · rw [cbT0]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t7,
        StackSemRegisterTransfers.storeOfSyntax] using look .codeBuffer (by decide)
    · rw [cbT0]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t1,
        StackSemRegisterTransfers.storeOfSyntax] using look .codeBufferEnd (by decide)
    · rw [positionEq]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t4,
        StackSemRegisterTransfers.storeOfSyntax] using look .bitmapBuffer (by decide)
    · rw [positionEq, spaceLeft]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t6,
        StackSemRegisterTransfers.storeOfSyntax] using look .bitmapBufferEnd (by decide)
    · rw [limits]
      refine ⟨?_, ?_, stackLen.symm⟩
      · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t5, halfX,
          StackSemRegisterTransfers.storeOfSyntax] using look .heapLength (by decide)
      · show heapLength / 2 * (width / 8) < 2 ^ width
        have := reg3.isLt
        have : heapLength / 2 * (width / 8) ≤ heapLength * (width / 8) :=
          Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
        omega
    · rw [cbT0]; exact cbEmpty
    · exact bufferNil
    · simp [hT0, InitReduce.initReduce]
    · simp [hT0, InitReduce.initReduce]
    · exact t0
    · exact fits
    · rw [stackLen]; have := p4.isLt
      have : stackLength ≤ stackLength * (width / 8) := Nat.le_mul_of_pos_right _ bpos
      omega
    · rw [half, BitVec.mul_comm]
    · exact al2
    · rw [stackVal]; exact holLast_append_singleton _ _
    · exact stackSpEq
    · rw [stackLen]; have := p4.isLt
      have : (stackLength - storeList.length) * (width / 8) ≤ stackLength * (width / 8) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
    · omega
    · exact heapHalf

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect
