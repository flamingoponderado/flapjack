import Flapjack.Compiler.Backend.Semantics.StackSem.LeafTransfers
import Flapjack.Compiler.Backend.Semantics.StackSem.RegisterTransfers
import Flapjack.Compiler.Backend.Semantics.StackSem.LocValueCase
import Flapjack.Compiler.Backend.Semantics.StackSem.FixedStackCases
import Flapjack.Compiler.Backend.Semantics.StackSem.DynamicStackCases
import Flapjack.Compiler.Backend.Semantics.StackSem.SizeBitmapCases
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateAllocCase
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConstsCase
import Flapjack.Compiler.Backend.Semantics.StackSem.ShMemOpCase
import Flapjack.Compiler.Backend.Semantics.StackSem.Install
import Flapjack.Compiler.Backend.Semantics.StackSem.BufferWrites
import Flapjack.Compiler.Backend.Semantics.StackSem.Ffi
import Flapjack.Compiler.Backend.Semantics.StackSem.InstCase
import Flapjack.Compiler.Backend.Semantics.StackSem.JumpLower
import Flapjack.Compiler.Backend.Semantics.StackSem.RawCall
import Flapjack.Compiler.Backend.Semantics.StackSem.Call
import Flapjack.Compiler.Backend.Semantics.StackSem.ControlCases
import Flapjack.Compiler.Backend.Semantics.StackSem.Measure.CallSites

/-! Total StackSem `evaluate` over the exact `HolProg`/`StackSemStateFiniteExact`
carriers, assembled from the per-clause fragments of
`cakeml/compiler/backend/semantics/stackSemScript.sml:773-1027`.

The definition recurses on HOL's clock-first lexicographic measure
(`stackSemMeasure`, `inv_image (measure I LEX measure prog_size)`). Each
recursive fragment (`Seq`, `If`, `Loop`, `JumpLower`, `RawCall`, `Call`) is
handed `ev`, the evaluator restricted to arguments of strictly smaller measure.
The restriction's fallback is unreachable: the `evaluate_*` clause equations
below show that every argument a fragment can pass satisfies the guard, so each
clause equals its fragment applied to `evaluateHOL` itself, with no evaluator
callback, success or simulation premise. Non-recursive clauses delegate to the
partial fragments, each of which handles its constructor (`some`); the
`getD` fallback is likewise never reached. This module is untagged; the
HOL-shaped `evaluate_def` equations are stated separately. -/

namespace Flapjack.StackSemEvaluate

open Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemMeasure StackSemStateOps
open StackSemLeafTransfers StackSemRegisterTransfers StackSemLocValueCase
open StackSemFixedStackCases StackSemDynamicStackCases StackSemSizeBitmapCases
open StackSemEvaluateAlloc StackSemStoreConsts StackSemShMemOpCase StackSemInstall
open StackSemBufferWrites StackSemFfi StackSemInstCase StackSemJumpLower StackSemRawCall
open StackSemCall StackSemControlCases

/-- Read a partial fragment's result for a constructor it handles. -/
def fromFragment {width : Nat} [NeZero width] {C F : Type}
    (o : Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F))
    (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  o.getD (some .error, s)

open Classical in
/-- The assembled total StackSem evaluator. -/
noncomputable def evaluateHOL {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  let ev : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
    fun p' s' =>
      if _h : LexNat (stackSemMeasure p' s') (stackSemMeasure p s) then evaluateHOL p' s'
      else (some .error, s')
  match p with
  | .skip | .halt _ | .tick | .ret _ | .raise _ | .break _ | .continue _ =>
      fromFragment (evaluateLeaf p s) s
  | .inst _ => fromFragment (evaluateInst p s) s
  | .get _ _ | .set _ _ | .opCurrHeap _ _ _ => fromFragment (evaluateRegister p s) s
  | .alloc n => evaluateAllocCase n s
  | .storeConsts t1 t2 stub => evaluateStoreConsts t1 t2 stub s
  | .seq a b => StackSemControlCases.evaluateSeq ev a b s
  | .ite cmp r ri a b => StackSemControlCases.evaluateIf ev cmp r ri a b s
  | .loop body => StackSemControlCases.evaluateLoop ev body s
  | .jumpLower r1 r2 dest => evaluateJumpLower ev r1 r2 dest s
  | .rawCall dest => evaluateRawCall ev dest s
  | .call ret dest handler => evaluateCall ev ret dest handler s
  | .install _ _ _ _ _ => fromFragment (evaluateInstall p s) s
  | .shMemOp _ _ _ => fromFragment (evaluateShMemOp p s) s
  | .codeBufferWrite _ _ | .dataBufferWrite _ _ => fromFragment (evaluateBufferWrite p s) s
  | .ffi _ _ _ _ _ _ => fromFragment (evaluateFfi p s) s
  | .locValue r l1 l2 => locValue r l1 l2 s
  | .stackAlloc n => stackAlloc n s
  | .stackFree n => stackFree n s
  | .stackLoad r n => stackLoad r n s
  | .stackLoadAny r rn => stackLoadAny r rn s
  | .stackStore r n => stackStore r n s
  | .stackStoreAny r rn => stackStoreAny r rn s
  | .stackGetSize r => stackGetSize r s
  | .stackSetSize r => stackSetSize r s
  | .bitmapLoad r v => bitmapLoad r v s
termination_by stackSemMeasure p s
decreasing_by all_goals exact _h

theorem evaluateHOL_seq {width : Nat} [NeZero width] {C F : Type}
    (a b : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.seq a b) s = StackSemControlCases.evaluateSeq evaluateHOL a b s := by
  rw [evaluateHOL]
  simp only [StackSemControlCases.evaluateSeq, dif_pos (seq_first_measure_lt a b s)]
  have h2 := seq_second_measure_lt a b s (evaluateHOL a s)
  rcases hfx : StackSemControl.fixClock s (evaluateHOL a s) with ⟨res, s1⟩
  rw [hfx] at h2
  cases res with
  | none => simp only [dif_pos h2]
  | some r => rfl

theorem evaluateHOL_ite {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.ite cmp r ri a b) s =
      StackSemControlCases.evaluateIf evaluateHOL cmp r ri a b s := by
  rw [evaluateHOL]
  simp only [StackSemControlCases.evaluateIf, dif_pos (if_first_measure_lt cmp r ri a b s),
    dif_pos (if_second_measure_lt cmp r ri a b s)]

theorem evaluateHOL_loop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.loop body) s = StackSemControlCases.evaluateLoop evaluateHOL body s := by
  rw [evaluateHOL]
  simp only [StackSemControlCases.evaluateLoop, dif_pos (loop_body_measure_lt body s)]
  have h2 := fun hne => loop_reentry_measure_lt body s (evaluateHOL body s) hne
  rcases hfx : StackSemControl.fixClock s (evaluateHOL body s) with ⟨res, s1⟩
  rw [hfx] at h2
  dsimp only
  by_cases hc : StackSemControl.contLoop res
  · by_cases h0 : s1.clock = 0
    · simp [hc, h0]
    · simp [hc, h0, dif_pos (h2 h0)]
  · simp [hc]

theorem evaluateHOL_jumpLower {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.jumpLower r1 r2 dest) s = evaluateJumpLower evaluateHOL r1 r2 dest s := by
  rw [evaluateHOL]
  simp only [evaluateJumpLower]
  split
  · split
    · split
      · rfl
      · rename_i prog _
        by_cases h0 : s.clock = 0
        · simp [h0]
        · simp [h0, dif_pos (callee_measure_lt prog (.jumpLower r1 r2 dest) s h0)]
    · rfl
  · rfl

theorem evaluateHOL_rawCall {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.rawCall dest) s = evaluateRawCall evaluateHOL dest s := by
  rw [evaluateHOL]
  simp only [evaluateRawCall]
  split
  · rfl
  · split
    · rename_i body _
      by_cases h0 : s.clock = 0
      · simp [h0]
      · simp [h0, dif_pos (callee_measure_lt body (.rawCall dest) s h0)]
    · rfl

theorem evaluateHOL_call {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.call ret dest handler) s = evaluateCall evaluateHOL ret dest handler s := by
  rw [evaluateHOL]
  simp only [evaluateCall]
  cases ret with
  | none =>
      dsimp only
      split
      · rfl
      · rename_i prog _
        split
        · rfl
        · by_cases h0 : s.clock = 0
          · simp [h0]
          · simp [h0, dif_pos (callee_measure_lt prog (.call none dest none) s h0)]
  | some rr =>
      obtain ⟨retH, link, l1, l2⟩ := rr
      dsimp only
      split
      · rfl
      · rename_i prog _
        by_cases h0 : s.clock = 0
        · simp [h0]
        · simp only [h0, if_false]
          have hs' : (setVar link (.loc l1 l2) s).clock ≠ 0 := by simpa [setVar] using h0
          have hpar : stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler)
              (setVar link (.loc l1 l2) s) =
              stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s := by
            simp [stackSemMeasure, setVar]
          have hcallee := callee_measure_lt prog (.call (some (retH, link, l1, l2)) dest handler)
            (setVar link (.loc l1 l2) s) hs'
          rw [hpar] at hcallee
          rw [dif_pos hcallee]
          have hk := fun cont => call_continuation_measure_lt cont
            (.call (some (retH, link, l1, l2)) dest handler) s link l1 l2
            (evaluateHOL prog (decClock (setVar link (.loc l1 l2) s))) h0
          rcases hfx : StackSemControl.fixClock
              (decClock (setVar link (.loc l1 l2) s))
              (evaluateHOL prog (decClock (setVar link (.loc l1 l2) s))) with
            ⟨res, s2⟩
          rw [hfx] at hk
          rcases res with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
          all_goals first
            | rfl
            | simp [dif_pos (hk _)]

/-! Unfolding equations of the non-recursive clauses: each is the clause's fragment. -/

theorem evaluateHOL_skip {width : Nat} [NeZero width] {C F : Type} 
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.skip : HolProg width) s = fromFragment (evaluateLeaf .skip s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_halt {width : Nat} [NeZero width] {C F : Type} (v : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.halt v : HolProg width) s = fromFragment (evaluateLeaf (.halt v) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_tick {width : Nat} [NeZero width] {C F : Type} 
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.tick : HolProg width) s = fromFragment (evaluateLeaf .tick s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_ret {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.ret n : HolProg width) s = fromFragment (evaluateLeaf (.ret n) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_raise {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.raise n : HolProg width) s = fromFragment (evaluateLeaf (.raise n) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_break {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.break n : HolProg width) s = fromFragment (evaluateLeaf (.break n) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_continue {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.continue n : HolProg width) s = fromFragment (evaluateLeaf (.continue n) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_inst {width : Nat} [NeZero width] {C F : Type} (i : HolInst width)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.inst i : HolProg width) s = fromFragment (evaluateInst (.inst i) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_get {width : Nat} [NeZero width] {C F : Type} (v : Nat) (name : StoreName)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.get v name : HolProg width) s = fromFragment (evaluateRegister (.get v name) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_set {width : Nat} [NeZero width] {C F : Type} (name : StoreName) (v : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.set name v : HolProg width) s = fromFragment (evaluateRegister (.set name v) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_opCurrHeap {width : Nat} [NeZero width] {C F : Type} (op : HolBinop) (v src : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.opCurrHeap op v src : HolProg width) s = fromFragment (evaluateRegister (.opCurrHeap op v src) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_alloc {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.alloc n : HolProg width) s = evaluateAllocCase n s := by
  rw [evaluateHOL]

theorem evaluateHOL_storeConsts {width : Nat} [NeZero width] {C F : Type} (t1 t2 : Nat) (stub : Option Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.storeConsts t1 t2 stub : HolProg width) s = evaluateStoreConsts t1 t2 stub s := by
  rw [evaluateHOL]

theorem evaluateHOL_install {width : Nat} [NeZero width] {C F : Type} (a b c d e : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.install a b c d e : HolProg width) s = fromFragment (evaluateInstall (.install a b c d e) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_shMemOp {width : Nat} [NeZero width] {C F : Type} (op : HolMemop) (r : Nat) (a : HolAddr width)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.shMemOp op r a : HolProg width) s = fromFragment (evaluateShMemOp (.shMemOp op r a) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_codeBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.codeBufferWrite r1 r2 : HolProg width) s = fromFragment (evaluateBufferWrite (.codeBufferWrite r1 r2) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_dataBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.dataBufferWrite r1 r2 : HolProg width) s = fromFragment (evaluateBufferWrite (.dataBufferWrite r1 r2) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_ffi {width : Nat} [NeZero width] {C F : Type} (f : Basis.Pure.MlString.MlString) (a b c d e : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.ffi f a b c d e : HolProg width) s = fromFragment (evaluateFfi (.ffi f a b c d e) s) s := by
  rw [evaluateHOL]

theorem evaluateHOL_locValue {width : Nat} [NeZero width] {C F : Type} (r l1 l2 : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.locValue r l1 l2 : HolProg width) s = locValue r l1 l2 s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackAlloc {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackAlloc n : HolProg width) s = stackAlloc n s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackFree {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackFree n : HolProg width) s = stackFree n s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackLoad {width : Nat} [NeZero width] {C F : Type} (r n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackLoad r n : HolProg width) s = stackLoad r n s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackLoadAny {width : Nat} [NeZero width] {C F : Type} (r rn : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackLoadAny r rn : HolProg width) s = stackLoadAny r rn s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackStore {width : Nat} [NeZero width] {C F : Type} (r n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackStore r n : HolProg width) s = stackStore r n s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackStoreAny {width : Nat} [NeZero width] {C F : Type} (r rn : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackStoreAny r rn : HolProg width) s = stackStoreAny r rn s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackGetSize {width : Nat} [NeZero width] {C F : Type} (r : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackGetSize r : HolProg width) s = stackGetSize r s := by
  rw [evaluateHOL]

theorem evaluateHOL_stackSetSize {width : Nat} [NeZero width] {C F : Type} (r : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.stackSetSize r : HolProg width) s = stackSetSize r s := by
  rw [evaluateHOL]

theorem evaluateHOL_bitmapLoad {width : Nat} [NeZero width] {C F : Type} (r v : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateHOL (.bitmapLoad r v : HolProg width) s = bitmapLoad r v s := by
  rw [evaluateHOL]

end Flapjack.StackSemEvaluate
