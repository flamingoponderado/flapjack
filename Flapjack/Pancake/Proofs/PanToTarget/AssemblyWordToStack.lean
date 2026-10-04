import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import Flapjack.Compiler.Backend.Proofs.WordConventions
import Flapjack.Pancake.Proofs.PanToWord.LabPres
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileBitmaps

/-!
# `pan_to_target_compile_semantics` assembly, word-to-stack stage facts

Facts that the HOL proof of `pan_to_target_compile_semantics`
(`pan_to_targetProofScript.sml:1606-1622`) establishes before applying
`word_to_stackProof$compile_semantics`. Intermediate steps of the single HOL proof,
so untagged; premises are hypotheses of the top theorem or reviewed pass results.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang

/-- `ALOOKUP` misses a key absent from the list's keys (Flapjack infrastructure). -/
theorem panPropsALookupEq_eq_none {κ α : Type} [DecidableEq κ] (key : κ) :
    ∀ (l : List (κ × α)), (∀ e ∈ l, e.1 ≠ key) → panPropsALookupEq key l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro h
    obtain ⟨k, v⟩ := e
    simp only [panPropsALookupEq]
    have hk : k ≠ key := h (k, v) (by simp)
    simp only [hk, decide_false, Bool.false_eq_true, if_false]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- The word program has no entries at the two stub locations (HOL proof lines
1606-1622: `pan_to_word_compile_prog_lab_min` and the key equation of
`compile_to_word_conventions2`). -/
theorem panToTargetStubLocationsFree {width : Nat} [NeZero width]
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hisa : ac.isa ≠ .ag32)
    (hwtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, wprog)) :
    panPropsALookupEq raiseStubLocation wprog = none ∧
      panPropsALookupEq storeConstsStubLocation wprog = none := by
  have hconv := BackendProof.compileToWordConventions2 wc ac _ col wprog hwtw
    (fun _ _ => Or.inr hisa)
  have hkeys := hconv.1
  have hmin := PanToWord.pan_to_word_compile_prog_lab_min ac.isa panCode _ rfl
  have hge : ∀ e ∈ wprog, 60 ≤ e.1 := by
    intro e he
    have : e.1 ∈ wprog.map Prod.fst := List.mem_map_of_mem he
    rw [hkeys] at this
    obtain ⟨e', he', heq⟩ := List.mem_map.mp this
    rw [← heq]; exact hmin e' he'
  constructor
  · exact panPropsALookupEq_eq_none _ _ (fun e he h => by
      have := hge e he; rw [h] at this
      simp [raiseStubLocation, wordNumStubs, stackNumStubs] at this)
  · exact panPropsALookupEq_eq_none _ _ (fun e he h => by
      have := hge e he; rw [h] at this
      simp [storeConstsStubLocation, wordNumStubs, stackNumStubs] at this)

/-- A successful `full_make_init` keeps the supplied bitmaps and installs the stack
program as the code (HOL proof lines 1563-1585: `make_init_opt`, `make_init_any`,
`init_reduce`). -/
theorem fullMakeInit_bitmaps_code {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × StackLang.HolProg width)) (s4 : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width))
    (s x : StackSemStateFiniteExact width C F)
    (h : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code s4
      saveRegs dataSp coracle = (s, some x)) :
    s.bitmaps = bitmaps ∧ s.code = sptFromAList code := by
  unfold StackToLab.Proofs.FullMakeInit.fullMakeInit at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, hopt⟩ := h
  constructor
  · simp only [StackAlloc.makeInit, StackRemove.Proofs.InitMake.makeInitAny, hopt]
    unfold StackRemove.Proofs.InitMake.makeInitOpt at hopt
    split at hopt
    · cases hopt
    · split at hopt
      · cases hopt; rfl
      · cases hopt
  · rfl

/-- `init_state_ok` for the stack state of `full_make_init` with the proof's empty
word oracle (HOL proof lines 1624-1647, via `IMP_init_state_ok`). -/
theorem panToTargetInitStateOk {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (c'' : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg width)) (cfg : C)
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap stk : Nat)
    (stoff : BitVec width × BitVec width) (labSt : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (sst xxx : StackSemStateFiniteExact width C F)
    (good : goodDimindex width) (hregs : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (hwts : WordToStack.Native.compileNative ac false wprog = (bitmaps, c'', fs, p))
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit scc dc maxHeap stk stoff bitmaps p labSt
      saveRegs dataSp (fun _ => (cfg, [], [])) = (sst, some xxx)) :
    WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount - (ac.avoidRegs.length + 5)) sst
      (fun _ => ((bitmaps.length, cfg), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))) := by
  have hbm := (WordToStack.Native.compileWordToStackBitmaps ac wprog bitmaps c'' (fs, p) hwts).1
  obtain ⟨t, rfl⟩ : ∃ t, bitmaps = 4 :: t := by
    cases bitmaps with
    | nil => exact absurd hbm id
    | cons h t => exact ⟨t, by simp_all⟩
  apply StackToLab.Proofs.EncodingInitState.impInitStateOk (labSt := labSt) (saveRegs := saveRegs)
    (dataSp := dataSp) (xxx := xxx) (scc := scc) (dc := dc) (maxHeap := maxHeap) (stk := stk)
    (stoff := stoff) (p6 := p)
  refine ⟨by omega, rfl, good, fun n => ?_, ?_, hfmi⟩
  · simp
  · funext n
    simp [WordToStack.Native.compileWordToStackNative, appListAppend, appendAux]

end Flapjack.Pancake.Proofs.PanToTarget
