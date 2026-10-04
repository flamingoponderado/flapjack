import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory
import Flapjack.Pancake.Proofs.PanToTarget.InitHelpers
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
import Mathlib.Data.BitVec
import Mathlib.Tactic.Abel
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordLemmas
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
import Flapjack.Compiler.Backend.BackendProof.MachineInit

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

end Flapjack.Pancake.Proofs.PanToTarget
