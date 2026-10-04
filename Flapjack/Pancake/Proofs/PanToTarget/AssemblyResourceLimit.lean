import Flapjack.Pancake.Proofs.PanToTarget.StackSizeConst
import Flapjack.Compiler.Backend.WordDepthProof.CallGraph
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.BackendProof.WordToStackSfs
import Flapjack.Misc.Sptree.MapiWf
import Flapjack.Misc.Sptree.MapiLookup
import Flapjack.Misc.Sptree.Wf
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordLemmas
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization

/-!
# `pan_to_target_compile_semantics` assembly, stage G (resource limit)

Intermediate steps of the single HOL proof of `pan_to_target_compile_semantics`
(`pan_to_targetProofScript.sml:2285-2506`): the resource-limit implication
`option_lt stack_max (SOME (FST (read_limits ...))) ⇒ word_lang_safe_for_space wst
InitGlobals_location`. They are not HOL theorems, so they are untagged.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordDepth
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepthProof
open Flapjack.Compiler.Encoders.Asm

/-- Stage G, depth half (HOL lines 2292-2312 with `max_depth_Call_NONE` and
`evaluate_stack_size_limit_const_panLang`): an entry call that never errors and
whose call-graph depth `m` over code `funs ⊆ wst.code` lies strictly below the
initial stack limit is safe for space.  `wst.stack = []` and
`wst.stackMax = stack_size []` are the word `make_init` fields; the
`no_install`/`no_alloc` code facts are those HOL obtains from
`word_to_word_compile_no_install_no_alloc`. -/
theorem panToTargetSafeForSpaceOfDepth {width : Nat} [NeZero width] {C F : Type}
    (wst : WordSemStateFiniteExact width C F) (start : Nat)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (m : Nat)
    (hstack : wst.stack = [])
    (hmax : wst.stackMax = wordSemStackSize ([] : List (WordSemStackFrame width)))
    (hsub : sptSubspt funs wst.code)
    (hni : WordProps.noInstallCode wst.code) (hna : WordProps.noAllocCode wst.code)
    (hnoerr : ∀ k res t,
      evaluate (.call none (some start) [0] none) { wst with clock := k } = (res, t) →
        res ≠ some .error)
    (hdepth : maxDepth wst.stackSize (fullCallGraph start funs) = some m)
    (hlt : m < wst.stackLimit) :
    wordLangSafeForSpace wst start := by
  intro k res t h
  have hle := maxDepthCallNONE start [0] { wst with clock := k } res t funs
    ⟨h, hnoerr k res t h, hsub⟩
  have hconst := evaluate_stack_size_limit_const_panLang _ { wst with clock := k } res t
    ⟨h, by simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp], hni,
      by simp [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp], hna⟩
  simp only [hstack, hmax, hdepth, wordSemStackSize, List.foldr, optionMap₂] at hle
  rcases ht : t.stackMax with _ | x
  · rw [ht] at hle; simp [optionLe] at hle
  · rw [ht] at hle
    simp only [optionLe] at hle
    refine ⟨x, rfl, ?_⟩
    rw [hconst.2]
    simp only
    omega

private theorem sptAListLookup_map_snd {α β : Type} (g : α → β) (key : Nat) :
    ∀ entries : List (Nat × α),
      sptAListLookup key (entries.map fun kv => (kv.1, g kv.2)) =
        (sptAListLookup key entries).map g
  | [] => rfl
  | (other, value) :: entries => by
      by_cases h : key = other <;>
        simp [sptAListLookup, h, sptAListLookup_map_snd g key entries]

/-- Stage G, frame sizes (HOL lines 2336-2365, via `compile_word_to_stack_sfs_aux`,
`mapi_Alist`, `map_fromAList` and `fromAList_toAList`): the word `make_init`
stack-size table `mapi (λ_ (argc,prog). FST (SND (compile_prog ...))) (fromAList wprog)`
is the `stack_frame_size` of the `word_to_stack` configuration, so `stack_max` of
`compile_prog_max` is the call-graph depth over `wst.stackSize`. -/
theorem panToTargetStackSizeEqFrameSize {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    sptMapi (fun _ (ap : Nat × WordLangProgHOL (BitVec width)) =>
        (Compiler.Backend.WordToStack.Native.compileProgNative conf false ap.2 ap.1
          (conf.regCount - (5 + conf.avoidRegs.length)) (.nil, 0)).2.1)
        (sptFromAList wprog) =
      (Compiler.Backend.WordToStack.Native.compileNative conf false wprog).2.1.stackFrameSize := by
  simp only [Compiler.Backend.WordToStack.Native.compileNative]
  generalize hc : Compiler.Backend.WordToStack.Native.compileWordToStackNative conf false
    (conf.regCount - (5 + conf.avoidRegs.length)) wprog
    (if false = true then (.list [16], 1) else (.list [4], 1)) = r
  obtain ⟨bodies, frames, bitmaps⟩ := r
  have hsfs := Compiler.Backend.BackendProof.compileWordToStackSfsAux conf false
    (conf.regCount - (5 + conf.avoidRegs.length)) wprog _ bodies frames bitmaps ⟨hc, rfl⟩
  simp only
  rw [← hsfs]
  refine ((sptEqThm _ _ ⟨sptWfMapi _ _, sptWfFromAList _⟩).2 fun n => ?_)
  rw [sptLookupMapi, sptLookup_sptFromAList, sptLookup_sptFromAList,
    sptAListLookup_map_snd (fun ap : Nat × WordLangProgHOL (BitVec width) =>
      (Compiler.Backend.WordToStack.Native.compileProgNative conf false ap.2 ap.1
        (conf.regCount - (5 + conf.avoidRegs.length)) (.nil, 0)).2.1)]

open Flapjack.Compiler.Backend.WordToStack.Native in
/-- Stage G assembled over the word `make_init` state (HOL lines 2285-2365):
for `wst = make_init conf k sst (fromAList wprog) coracle` with the
`word_to_stack` register count `k`, `stack_max = max_depth c''.stack_frame_size
(full_call_graph start (fromAList wprog))` as in `compile_prog_max`, and any limit
`lim ≤ LENGTH sst.stack`, `option_lt stack_max (SOME lim)` implies
`word_lang_safe_for_space wst start`.  The remaining premises are the
`no_install`/`no_alloc` code facts and the no-`Error` fact that HOL derives from
`semantics wst start ≠ Fail`. -/
theorem panToTargetSafeForSpaceOfLimit {width : Nat} [NeZero width] {C F : Type}
    (conf : AsmConfigExact width) (sst : StackSemStateFiniteExact width C F)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start lim : Nat) (stackMax : Option Nat)
    (hmax : stackMax = maxDepth (compileNative conf false wprog).2.1.stackFrameSize
      (fullCallGraph start (sptFromAList wprog)))
    (hlim : lim ≤ sst.stack.length)
    (hni : WordProps.noInstallCode (sptFromAList wprog))
    (hna : WordProps.noAllocCode (sptFromAList wprog))
    (hnoerr : ∀ k res t,
      evaluate (.call none (some start) [0] none)
          { Initialization.makeInit conf (conf.regCount - (5 + conf.avoidRegs.length)) sst
              (sptFromAList wprog) coracle with clock := k } = (res, t) →
        res ≠ some .error) :
    optionLt stackMax (some lim) = true →
      wordLangSafeForSpace
        (Initialization.makeInit conf (conf.regCount - (5 + conf.avoidRegs.length)) sst
          (sptFromAList wprog) coracle) start := by
  intro hlt
  rcases hm : stackMax with _ | m
  · rw [hm] at hlt; simp [optionLt] at hlt
  · rw [hm] at hlt
    simp only [optionLt, decide_eq_true_eq] at hlt
    rw [← panToTargetStackSizeEqFrameSize] at hmax
    exact panToTargetSafeForSpaceOfDepth _ start (sptFromAList wprog) m rfl rfl
      (fun _ h => ⟨h, rfl⟩) hni hna hnoerr (hm ▸ hmax).symm (by
        simp only [Initialization.makeInit]; omega)

open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs in
/-- Stage G, limits (HOL lines 2311-2335 and 2366-2506): for the pointer facts
`init_code_thm` exposes (`w2`/`w3`/`w4` are the initial `len`/`ptr2`/`len2`
registers), the stack limit of `get_stack_heap_limit max_heap (w2, w3, w4)` is at
most the length `stack_sp + 1` of the stack that `init_reduce` reads, whose
pointers `init_code_thm` gives as `w4 - bytes_in_word` and the rounded heap end
plus the store area. -/
theorem panToTargetStackLimitLeLength {width : Nat} [NeZero width]
    (hgood : goodDimindex width) (maxHeap : Nat) (w2 w3 w4 : BitVec width)
    (hw2 : holByteAligned w2 = true) (hw4 : holByteAligned w4 = true)
    (hlo : w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width)
    (hheap : (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat)
    (hheapLt : (bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * w2) = true) :
    (InitLimits.getStackHeapLimit maxHeap (w2, w3, w4)).1 ≤
      ((w4 - bytesInWord width) -
          ((((w3 + -1 * w2) >>> (wordShiftAmount width + 1)) <<<
              (wordShiftAmount width + 1)) + w2 +
            bytesInWord width * BitVec.ofNat width storeList.length)).toNat /
          (width / 8) + 1 := by
  have h2 := Compiler.Backend.BackendProof.byteAlignedMOD hgood w2 hw2
  have h4 := Compiler.Backend.BackendProof.byteAlignedMOD hgood w4 hw4
  have hal := (holAligned_iff _ _).1 halign
  have hcomm : -1 * w2 + w3 = w3 + -1 * w2 := BitVec.add_comm _ _
  rw [Compiler.Backend.DataToWord.Proofs.Gc.lsrLsl _ _ halign]
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
  have hb : w3 + -w2 + w2 + bytesInWord width * BitVec.ofNat width storeList.length =
      w3 + bytesInWord width * BitVec.ofNat width storeList.length := by
    rw [BitVec.add_assoc w3, BitVec.add_comm (-w2), BitVec.add_right_neg, BitVec.add_zero]
  rw [hneg, hw3, hb]
  rw [hneg] at hal
  have hsl : storeList.length = 48 := by decide
  rw [hsl]
  clear hlo hhi hheap hheapLt halign hlo' hhi' hmh hnlt hcomm hneg hw3 hb hsl hw2 hw4
  rcases hgood with h | h <;> subst h <;>
    simp [bytesInWord, wordShiftAmount, BitVec.toNat_sub, BitVec.toNat_add,
      BitVec.toNat_neg] at hal h2 h4 ⊢ <;> omega

end Flapjack.Pancake.Proofs.PanToTarget
