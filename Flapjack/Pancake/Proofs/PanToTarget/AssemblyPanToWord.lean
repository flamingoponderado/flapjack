import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory
import Flapjack.Pancake.Proofs.PanToTarget.InitHelpers
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
import Mathlib.Data.BitVec
import Mathlib.Tactic.Abel
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordLemmas
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyInitMemory

/-!
# `pan_to_target_compile_semantics` assembly, pan_to_word stage

The step of the HOL proof of `pan_to_target_compile_semantics`
(`pan_to_targetProofScript.sml:2041-2284`) that applies
`pan_to_wordProof$state_rel_imp_semantics` to the source-code word state
`wst0 = (make_init ... sss ...) with code := fromAList (pan_to_word$compile_prog ...)`,
and the heap-length shift arithmetic it uses. Intermediate steps of the single HOL
proof, so untagged; the facts about the stack state are stated as hypotheses that the
memory-setup stage derives from the original premises.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-- The heap-length shift of the HOL proof (lines 2041-2054): adding the
`store_list` words to the heap span and subtracting their count after division by
the word size, provided the extended span does not wrap. -/
theorem heapLengthShift {width : Nat} [NeZero width] (good : goodDimindex width)
    (w2 w3 : BitVec width) (len : Nat)
    (hbound : (-1 * w2 + w3).toNat + len * (width / 8) < 2 ^ width) :
    (-1 * w2 + w3 + StackRemove.bytesInWord width * BitVec.ofNat width len).toNat /
        (width / 8) - len =
      (-1 * w2 + w3).toNat / (width / 8) := by
  have hd : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  have hlen : (StackRemove.bytesInWord width * BitVec.ofNat width len).toNat =
      len * (width / 8) := by
    rw [BitVec.toNat_mul, bytesInWord_toNat good, BitVec.toNat_ofNat]
    have : len < 2 ^ width := by
      have := Nat.le_mul_of_pos_right len hd; omega
    rw [Nat.mod_eq_of_lt this, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, hlen, Nat.mod_eq_of_lt hbound, Nat.add_mul_div_right _ _ hd,
    Nat.add_sub_cancel]

/-- The pan_to_word stage of the HOL proof (lines 2103-2284): `state_rel_imp_semantics`
for the source-code word state built by `word_to_stackProof$make_init` from the stack
state `sst`. The `make_init` projections (memory, domains, `be`, `ffi`, the store
without `Handler`, `locals = insert 0 (Loc 1 0)`) are discharged here; the
stack-state memory and store facts are the hypotheses the memory-setup stage
provides, and the remaining hypotheses are those of the top theorem. -/
theorem panToTargetPanToWordStage {width : Nat} [NeZero width] {C σ : Type}
    (ac : AsmConfigExact width) (k : Nat) (sst : StackSemStateFiniteExact width C σ)
    (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize : Nat)
    (heapLen : BitVec width)
    (hmem : ∀ a, s.memaddrs a → sst.memory a = wlabWlocExact (s.memory a))
    (hnolab : noLabelsHOL sst.memory (fun a => sst.mdomain a = true))
    (hmdomain : (fun a => sst.mdomain a = true) =
      (fun a => s.memaddrs a ∨ StackRemove.addresses s.topAddr globalsSize a))
    (hshmdomain : (fun a => sst.shMdomain a = true) = s.shMemaddrs)
    (hbe : sst.be = s.be) (hffi : sst.ffi = s.ffi)
    (hcurr : sst.store.lookup .currHeap = some (.word s.baseAddr))
    (hheap : sst.store.lookup .heapLength = some (.word heapLen))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (htop : s.topAddr = s.baseAddr + (2 : BitVec width) * heapLen -
      panBytesInWord width * BitVec.ofNat width globalsSize)
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halign : panGlobalsByteAlignedHOL s.topAddr)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty) (good : goodDimindex width)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail) :
    let wst := WordToStack.Native.Initialization.makeInit ac k sst wcode worac
    let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    WordSemStateFiniteExact.semantics wst0 BvlToBvi.initGlobalsLocation =
      PanSemStateFiniteExact.semanticsDecls s start panCode := by
  intro wst wst0
  rw [InitGlobals_location_eq_first_name]
  exact PanToWord.StateRelImpSemantics.panToWordStateRelImpSemantics s wst0 isa panCode start
    globalsSize heapLen
    ⟨hmem, hnolab, hstart, hsize, hparams, hmdomain, hshmdomain, hbe, hffi,
      by simpa [wst0, wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hcurr,
      by simpa [wst0, wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hheap,
      htop, hnodup, halign, halloc, hcode, rfl, hglobals, hlocals, heids, heshapes,
      by simp [wst0, wst, WordToStack.Native.Initialization.makeInit, sptLookup],
      good, hfail⟩

/-- The memory-domain split of the HOL proof (lines 2161-2216): the `n` heap words
from `a` are the first `n - g` words together with the `g` words ending at
`a + bytes_in_word * n2w n` (the globals area below the top of the heap). -/
theorem addressesSplitGlobals {width : Nat} [NeZero width] (good : goodDimindex width)
    (a : BitVec width) (n g : Nat) (hg : g ≤ n) :
    (fun x => StackRemove.addresses a (n - g) x ∨
      StackRemove.addresses (a + StackRemove.bytesInWord width * BitVec.ofNat width n -
        BitVec.ofNat width (g * width / 8)) g x) = StackRemove.addresses a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + g := ⟨n - g, by omega⟩
  have hsub : m + g - g = m := by omega
  have htop : BitVec.ofNat width (g * width / 8) =
      BitVec.ofNat width g * StackRemove.bytesInWord width := by
    rw [good_dimindex_div_mul width g good, StackRemove.bytesInWord, BitVec.ofNat_mul]
  have key : ∀ j : Nat, a + StackRemove.bytesInWord width * BitVec.ofNat width (m + g) -
      BitVec.ofNat width (g * width / 8) + BitVec.ofNat width j * StackRemove.bytesInWord width =
      a + BitVec.ofNat width (m + j) * StackRemove.bytesInWord width := by
    intro j
    rw [htop, BitVec.ofNat_add, BitVec.ofNat_add]
    generalize StackRemove.bytesInWord width = b
    generalize BitVec.ofNat width m = mm
    generalize BitVec.ofNat width g = gg
    generalize BitVec.ofNat width j = jj
    rw [BitVec.mul_comm b, BitVec.add_mul, BitVec.add_mul]; abel
  funext x
  apply propext
  simp only [StackRemove.mem_addresses, hsub]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨m + j, by omega, key j⟩
  · rintro ⟨i, hi, rfl⟩
    by_cases him : i < m
    · exact .inl ⟨i, him, rfl⟩
    · refine .inr ⟨i - m, by omega, ?_⟩
      rw [key, show m + (i - m) = i by omega]

open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs in
/-- The heap limit of `get_stack_heap_limit` under `init_code_thm`'s pointer facts
(HOL proof lines 2216-2240, `init_prop`'s heap length against the top theorem's
`heap_len`): twice the heap component is the heap span in words. -/
theorem panToTargetHeapLimitSnd {width : Nat} [NeZero width]
    (hgood : goodDimindex width) (maxHeap : Nat) (w2 w3 w4 : BitVec width)
    (hw2 : holByteAligned w2 = true) (hlt : w2 < w3)
    (hlo : w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width)
    (hheap : (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat)
    (hheapLt : (bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * w2) = true) :
    2 * (InitLimits.getStackHeapLimit maxHeap (w2, w3, w4)).2 =
      (-1 * w2 + w3).toNat / (width / 8) := by
  have h2 := Compiler.Backend.BackendProof.byteAlignedMOD hgood w2 hw2
  have hal := (holAligned_iff _ _).1 halign
  have hcomm : -1 * w2 + w3 = w3 + -1 * w2 := BitVec.add_comm _ _
  simp only [InitLimits.getStackHeapLimit, InitLimits.getStackHeapLimitPrime,
    InitLimitsDouble.getStackHeapLimitDouble, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlo' : w2 + bytesInWord width * BitVec.ofNat width maxStackAlloc ≤ w3 := by
    rwa [BitVec.mul_comm]
  have hhi' : w3 ≤ w4 - bytesInWord width * BitVec.ofNat width maxStackAlloc := by
    rwa [BitVec.mul_comm]
  have hmh : maxHeap * (bytesInWord width).toNat < 2 ^ width := by
    rwa [Nat.mul_comm] at hheapLt
  simp only [hlo', hhi', and_self, if_true, hmh]
  have hnlt : ¬ bytesInWord width * BitVec.ofNat width maxHeap < -1 * w2 + w3 := by
    rw [BitVec.lt_def, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := maxHeap)
      (by rcases hgood with h | h <;> subst h <;> simp [bytesInWord] at hheapLt ⊢ <;> omega),
      Nat.mod_eq_of_lt (by rwa [Nat.mul_comm] at hheapLt ⊢)]
    rw [Nat.mul_comm] at hheap
    omega
  simp only [hnlt, if_false]
  rw [hcomm, Compiler.Backend.DataToWord.Proofs.Gc.lsrLsl _ _ halign]
  have hneg : -1 * w2 = -w2 := by
    rw [BitVec.neg_mul]; exact congrArg _ (BitVec.one_mul w2)
  have hw3 : w2 + (w3 + -w2) = w3 := by
    rw [BitVec.add_comm w3, ← BitVec.add_assoc, BitVec.add_right_neg, BitVec.zero_add]
  rw [hneg, hw3]
  rw [hneg] at hal
  have hle : w2.toNat ≤ w3.toNat := Nat.le_of_lt hlt
  clear hlo hhi hheap hheapLt halign hlo' hhi' hmh hnlt hcomm hneg hw3 hw2 hlt
  rcases hgood with h | h <;> subst h <;>
    simp [wordShiftAmount, BitVec.toNat_add, BitVec.toNat_neg] at hal h2 ⊢ <;> omega

/-- Word-aligned addresses are fixed points of Pancake's `byte_align` under
`good_dimindex` (Flapjack infrastructure for HOL's `byte_aligned` in
`pan_to_word$state_rel_imp_semantics`). -/
theorem panGlobalsByteAligned_of_mod {width : Nat} [NeZero width] (good : goodDimindex width)
    (x : BitVec width) (h : x.toNat % (width / 8) = 0) : panGlobalsByteAlignedHOL x := by
  unfold panGlobalsByteAlignedHOL panByteAlignHOL
  apply BitVec.eq_of_toNat_eq
  rcases good with rfl | rfl
  · have hl : Nat.log2 (32 / 8) = 2 := by decide
    simp only [hl, BitVec.toNat_ofNat]
    have := x.isLt
    simp at h ⊢; omega
  · have hl : Nat.log2 (64 / 8) = 3 := by decide
    simp only [hl, BitVec.toNat_ofNat]
    have := x.isLt
    simp at h ⊢; omega

/-- The heap words from a word-aligned base are word aligned (Flapjack
infrastructure; HOL's `addresses_thm` with `byte_aligned_mult`). -/
theorem addresses_mod {width : Nat} [NeZero width] (good : goodDimindex width)
    (base : BitVec width) (hbase : base.toNat % (width / 8) = 0) (n : Nat) (a : BitVec width)
    (ha : StackRemove.addresses base n a) : a.toNat % (width / 8) = 0 := by
  rw [StackRemove.mem_addresses] at ha
  obtain ⟨i, -, rfl⟩ := ha
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, bytesInWord_toNat good]
  rcases good with rfl | rfl <;> simp at hbase ⊢ <;> omega

open StackToLab.Proofs.FullMakeInitSemantics in
/-- `read_pointers` of the stack-names state `s2` are the lab state's initial
`len`/`ptr2`/`len2` registers (HOL proof lines 1924-1929, `find_name` of
registers 2, 3, 4 under `full_make_init_semantics`' register-name facts). -/
theorem readPointers_s2 {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {t : LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    {w2 w3 w4 : BitVec width} (h2 : t.regs t.lenReg = .word w2)
    (h3 : t.regs t.ptr2Reg = .word w3) (h4 : t.regs t.len2Reg = .word w4) :
    StackRemove.Proofs.InitLimits.readPointers
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = (w2, w3, w4) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n4, n3, n2, -, -, hbij⟩ := id hA
  simp only [StackRemove.Proofs.InitLimits.readPointers, s2_regs_lookup hbij (.inl rfl),
    s2_regs_lookup hbij (.inr (.inl rfl)), s2_regs_lookup hbij (.inr (.inr rfl)), n2, n3, n4,
    h2, h3, h4, holThe, wordSemTheWord]

open StackToLab.Proofs.FullMakeInitSemantics in
/-- The pan_to_word stage of the HOL proof (lines 2103-2284) with its stack-state
premises discharged: on a successful `full_make_init` from the lab state `t`
(under `full_make_init_semantics`' hypotheses), the source-code word state built by
`word_to_stack`'s `make_init` runs as the Pancake program. The facts about `t` are
those of `lab_to_target$make_init` over `pan_installed`'s memory `m` (heap words,
the source memory on `s.memaddrs`, shared domain, endianness, FFI) and its initial
`len`/`ptr2`/`len2` registers; the rest are the top theorem's hypotheses, with
HOL's `byte_aligned s.top_addr` and the `HeapLength` value derived here. -/
theorem panToTargetPanToWordFromInit {width : Nat} [NeZero width] {C σ : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {t : LabSem.State width C σ}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C σ}
    (ac : AsmConfigExact width) (k : Nat) (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize heapLen : Nat)
    (w3 w4 : BitVec width)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle = (sst, some x))
    (h2 : t.regs t.lenReg = .word s.baseAddr) (h3 : t.regs t.ptr2Reg = .word w3)
    (h4 : t.regs t.len2Reg = .word w4) (hlt : s.baseAddr < w3)
    (hlo : s.baseAddr + BitVec.ofNat width StackRemove.maxStackAlloc *
      StackRemove.bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width StackRemove.maxStackAlloc *
      StackRemove.bytesInWord width)
    (hheap : (-1 * s.baseAddr + w3).toNat ≤ maxHeap * (StackRemove.bytesInWord width).toNat)
    (hheapLt : (StackRemove.bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * s.baseAddr) = true)
    (htmem : ∀ a, s.memaddrs a → t.memory a = wlabWlocExact (s.memory a))
    (htword : ∀ a, a.toNat % (width / 8) = 0 → ∃ w, t.memory a = .word w)
    (htsh : (fun a => t.sharedMemDomain a = true) = s.shMemaddrs)
    (htbe : t.be = s.be) (htffi : t.ffi = s.ffi)
    (hheapLen : heapLen = (w3 + -1 * s.baseAddr).toNat / (width / 8))
    (hglobLe : globalsSize ≤ heapLen)
    (hmemaddrs : s.memaddrs = StackRemove.addresses s.baseAddr (heapLen - globalsSize))
    (htop : s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heapLen -
      BitVec.ofNat width (globalsSize * width / 8))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail) :
    let wst := WordToStack.Native.Initialization.makeInit ac k sst wcode worac
    let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    WordSemStateFiniteExact.semantics wst0 BvlToBvi.initGlobalsLocation =
      PanSemStateFiniteExact.semanticsDecls s start panCode := by
  classical
  intro wst wst0
  have good : goodDimindex width := hA.1
  have hd : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  -- init_code_thm's alignment of the heap base
  obtain ⟨t', v2, -, -, -, g2, -, -, a2, -⟩ := panToTargetInitCodeRun hA
  rw [h2] at g2; cases g2
  have hbase : s.baseAddr.toNat % (width / 8) = 0 :=
    (holByteAligned_iff_mod good _).1 a2
  -- the store
  obtain ⟨w2, g2', hcurr, hheapLW⟩ :=
    panToTargetWordInitStore (ac := ac) (k := k) (wcode := wcode) (worac := worac) hA hfmi
  rw [h2] at g2'; cases g2'
  rw [readPointers_s2 hA h2 h3 h4] at hheapLW
  have hsnd := panToTargetHeapLimitSnd good maxHeap s.baseAddr w3 w4 a2 hlt hlo hhi hheap
    hheapLt halign
  rw [BitVec.add_comm (-1 * s.baseAddr), ← hheapLen] at hsnd
  -- the memory domain
  have hmd := panToTargetWordInitMdomain (ac := ac) (k := k) (wcode := wcode) (worac := worac)
    s.baseAddr w3 w4 hA hfmi h2 h3 h4 hlo hhi hheap hheapLt halign
  rw [← hheapLen] at hmd
  have hmdP : (fun a => wst.mdomain a = true) = StackRemove.addresses s.baseAddr heapLen := by
    funext a; rw [hmd a, decide_eq_true_eq]
  obtain ⟨hffi, hbe, hsh, hmem⟩ := panToTargetWordInitMemory (ac := ac) (k := k)
    (wcode := wcode) (worac := worac) hA hfmi
  have hin : ∀ a, s.memaddrs a → wst.mdomain a = true := by
    intro a ha
    have : StackRemove.addresses s.baseAddr heapLen a := by
      rw [← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe]
      exact .inl (hmemaddrs ▸ ha)
    rw [← hmdP] at this; exact this
  -- byte_aligned s.top_addr
  have htopAl : panGlobalsByteAlignedHOL s.topAddr := by
    apply panGlobalsByteAligned_of_mod good
    rw [htop, good_dimindex_div_mul width globalsSize good]
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, bytesInWord_toNat good]
    simp only [BitVec.toNat_ofNat]
    rcases good with h | h <;> subst h <;> simp at hbase ⊢ <;> omega
  refine panToTargetPanToWordStage ac k sst wcode worac s isa panCode start globalsSize
    (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit maxHeap
      (s.baseAddr, w3, w4)).2 * StackRemove.bytesInWord width)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstart hsize hparams ?_ hnodup htopAl halloc hcode hglobals hlocals
    heids heshapes good hfail
  · intro a ha
    exact (hmem a (hin a ha)).trans (htmem a ha)
  · intro a ha
    have hadr : StackRemove.addresses s.baseAddr heapLen a := by
      rw [← hmdP]; exact ha
    obtain ⟨w, hw⟩ := htword a (addresses_mod good s.baseAddr hbase heapLen a hadr)
    exact ⟨w, (hmem a ha).trans hw⟩
  · show (fun a => wst.mdomain a = true) = _
    rw [hmdP, ← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe, hmemaddrs,
      htop]
  · show (fun a => wst.shMdomain a = true) = _
    rw [hsh]; exact htsh
  · exact hbe.trans htbe
  · exact hffi.trans htffi
  · simpa [wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hcurr
  · simpa [wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hheapLW
  · rw [htop, good_dimindex_div_mul width globalsSize good]
    have e1 : (2 : BitVec width) * (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit
        maxHeap (s.baseAddr, w3, w4)).2 * StackRemove.bytesInWord width) =
        StackRemove.bytesInWord width * BitVec.ofNat width heapLen := by
      rw [← hsnd, BitVec.ofNat_mul, BitVec.mul_comm (StackRemove.bytesInWord width),
        ← BitVec.mul_assoc]
      rfl
    have e2 : BitVec.ofNat width (globalsSize * (width / 8)) =
        panBytesInWord width * BitVec.ofNat width globalsSize := by
      rw [BitVec.ofNat_mul, BitVec.mul_comm]; rfl
    rw [e1, e2]

end Flapjack.Pancake.Proofs.PanToTarget
