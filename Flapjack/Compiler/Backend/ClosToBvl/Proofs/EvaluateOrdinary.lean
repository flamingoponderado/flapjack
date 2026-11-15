module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateRejected
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateInteger
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateWord
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateConstant
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockBoolean
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockInspect
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCompare
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCons
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockExtend
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockList
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockEqual
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateGlobal
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryLength
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryByte
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryEl
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryBounds
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteBounds
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteVectorRead
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryAlloc
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryUpdate
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteToList
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteStringCmp
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteConstruct
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteCopy
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteXor
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryConfig
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateFfi
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateThunk

@[expose] public section

/-! Assembly of ordinary operator cases for the candidate simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

namespace DoAppSuccessCarrier
/-- Closure state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- BVL state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end DoAppSuccessCarrier

/-- Successful primitive operations outside the original exclusions preserve the relations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "do_app"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, BvlSem.State.refs, f])]
theorem doAppSuccess {C F : Type} (op : ClosLang.Op) (xs : List ClosSem.Value) (s1 s2 : ClosSem.State C F)
    (v : ClosSem.Value) (f : HolFiniteMapExact Nat Nat) (t1 : BvlSem.State C F)
    (ys : List BvlSem.Value)
    (premises : ClosSem.doApp op xs s1 = .val (v,s2) ∧ stateRel f s1 t1 ∧
      List.Forall₂ (vRel s1.maxApp f t1.refs t1.code) xs ys ∧
      op ≠ .memOp .ref ∧ op ≠ .memOp .update ∧ op ≠ .memOp .xorByte ∧
      op ≠ .memOp .refArray ∧ (∀ b, op ≠ .memOp (.refByte b)) ∧
      op ≠ .memOp .updateByte ∧ op ≠ .memOp .fromListByte ∧ op ≠ .memOp .concatByteVec ∧
      (∀ b, op ≠ .memOp (.copyByte b)) ∧ (∀ c, op ≠ .blockOp (.constant c)) ∧
      (∀ n, op ≠ .ffi n) ∧ (∀ t, op ≠ .thunkOp t)) :
    ∃ w t2, BvlSem.doApp (compileOp op) ys t1 = .val (w,t2) ∧
      vRel s1.maxApp f t1.refs t1.code v w ∧ stateRel f s2 t2 ∧
      t1.refs = t2.refs ∧ t1.code = t2.code := by
  obtain ⟨run, states, related, noRef, noUpdate, noXor, noArray, noRefByte, noUpdateByte,
    noFromList, noConcat, noCopy, noConstant, noFfi, noThunk⟩ := premises
  have finish (h : ∃ w, BvlSem.doApp (compileOp op) ys t1 = .val (w,t1) ∧
      s2 = s1 ∧ vRel s1.maxApp f t1.refs t1.code v w) :
      ∃ w t2, BvlSem.doApp (compileOp op) ys t1 = .val (w,t2) ∧
        vRel s1.maxApp f t1.refs t1.code v w ∧ stateRel f s2 t2 ∧
        t1.refs = t2.refs ∧ t1.code = t2.code := by
    obtain ⟨w, target, rfl, rel⟩ := h
    exact ⟨w, t1, target, rel, states, rfl, rfl⟩
  cases op with
  | ffi name => exact False.elim (noFfi name rfl)
  | thunkOp t => exact False.elim (noThunk t rfl)
  | label n => simp [ClosSem.doApp] at run
  | install => simp [ClosSem.doApp] at run
  | intOp i =>
    cases app : ClosSem.doIntApp i xs with
    | none => simp [ClosSem.doApp, ClosSem.applyNumeric, app] at run
    | some value =>
      have equal : value = v ∧ s1 = s2 := by simpa [ClosSem.doApp, ClosSem.applyNumeric, app] using run
      obtain ⟨rfl, rfl⟩ := equal
      obtain ⟨w, target, rel⟩ := doIntApp_related i xs ys related value app
      exact ⟨w, t1, by simp [compileOp, BvlSem.doApp, BvlSem.applyNumeric, target], rel, states, rfl, rfl⟩
  | wordOp i =>
    cases app : ClosSem.doWordApp i xs with
    | none => simp [ClosSem.doApp, ClosSem.applyNumeric, app] at run
    | some value =>
      have equal : value = v ∧ s1 = s2 := by simpa [ClosSem.doApp, ClosSem.applyNumeric, app] using run
      obtain ⟨rfl, rfl⟩ := equal
      obtain ⟨w, target, rel⟩ := doWordApp_related i xs ys related value app
      exact ⟨w, t1, by simp [compileOp, BvlSem.doApp, BvlSem.applyNumeric, target], rel, states, rfl, rfl⟩
  | blockOp operation =>
    cases operation with
    | cons tag =>
      simp [ClosSem.doApp, ClosSem.applyBlock] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.block (BackendCommon.closTagShift tag) ys, t1, by simp [compileOp, BvlSem.doApp, BvlSem.applyBlock],
        .block related, states, rfl, rfl⟩
    | elemAt n => apply finish; simpa [BlockInspect.op] using blockInspect_dispatch (.elemAt n) xs ys s1 s2 t1 related v run
    | tagLenEq tag n => apply finish; simpa [BlockInspect.op] using blockInspect_dispatch (.tagLengthEq tag n) xs ys s1 s2 t1 related v run
    | lenEq n => apply finish; simpa [BlockInspect.op] using blockInspect_dispatch (.lengthEq n) xs ys s1 s2 t1 related v run
    | tagEq tag => apply finish; simpa [BlockInspect.op] using blockInspect_dispatch (.tagEq tag) xs ys s1 s2 t1 related v run
    | lengthBlock => apply finish; simpa [BlockInspect.op] using blockInspect_dispatch .length xs ys s1 s2 t1 related v run
    | boolTest x => apply finish; simpa [BlockBoolean.op] using blockBoolean_dispatch (.test x) xs ys s1 s2 t1 related v run
    | boolNot => apply finish; simpa [BlockBoolean.op] using blockBoolean_dispatch .not xs ys s1 s2 t1 related v run
    | boundsCheckBlock => apply finish; simpa [BlockCompare.op] using blockCompare_dispatch .bounds xs ys s1 s2 t1 related v run
    | consExtend tag => apply finish; simpa [compileOp] using blockExtend_dispatch tag xs ys s1 s2 t1 related v run
    | fromList tag => apply finish; simpa [BlockListOp.op] using blockList_dispatch (.fromList tag) xs ys s1 s2 t1 related v run
    | listAppend => apply finish; simpa [BlockListOp.op] using blockList_dispatch .append xs ys s1 s2 t1 related v run
    | constant c => exact False.elim (noConstant c rfl)
    | equal => apply finish; simpa [compileOp] using blockEqual_dispatch xs ys s1 s2 t1 states related v run
    | equalConst part =>
      cases part with
      | int n => apply finish; simpa [BlockCompare.op] using blockCompare_dispatch (.intEq n) xs ys s1 s2 t1 related v run
      | str x => apply finish; simpa [BlockCompare.op] using blockCompare_dispatch (.stringEq x) xs ys s1 s2 t1 related v run
      | w64 x => apply finish; simpa [BlockCompare.op] using blockCompare_dispatch (.wordEq x) xs ys s1 s2 t1 related v run
      | con tag fields => simp [ClosSem.doApp, ClosSem.applyBlock] at run
    | build parts => simp [ClosSem.doApp, ClosSem.applyBlock] at run
  | globOp operation =>
    cases operation with
    | global index =>
      apply finish
      simpa [compileOp] using global_read_dispatch index xs ys s1 s2 t1 states related v run
    | setGlobal index =>
      obtain ⟨stored, argsEq, empty, valueEq, stateEq⟩ := global_set_success index xs s1 s2 v run
      subst xs
      cases related with
      | cons storedRel tail =>
        cases tail
        obtain ⟨targetApp, nextState⟩ := global_set_related s1 t1 states index stored _ storedRel empty
        subst v
        subst s2
        exact ⟨BvlSem.unitValue, _, by simpa [compileOp] using targetApp, .block .nil, nextState, rfl, rfl⟩
    | allocGlobal =>
      obtain ⟨count, argsEq, nonnegative, valueEq, stateEq⟩ := global_alloc_success xs s1 s2 v run
      subst xs
      have targetEq := vRel_numbers_inv [count] ys related
      have allocation := global_alloc_related s1 t1 states count nonnegative
      subst v
      subst s2
      subst ys
      exact ⟨BvlSem.unitValue, _, by simpa [compileOp] using allocation.2.1,
        allocation.2.2.1, allocation.2.2.2, rfl, rfl⟩
    | globalsPtr | setGlobalsPtr => simp [ClosSem.doApp, ClosSem.applyGlobal] at run
  | memOp operation =>
    cases operation with
    | ref => exact False.elim (noRef rfl)
    | update => exact False.elim (noUpdate rfl)
    | xorByte => exact False.elim (noXor rfl)
    | refArray => exact False.elim (noArray rfl)
    | refByte b => exact False.elim (noRefByte b rfl)
    | updateByte => exact False.elim (noUpdateByte rfl)
    | fromListByte => exact False.elim (noFromList rfl)
    | concatByteVec => exact False.elim (noConcat rfl)
    | copyByte b => exact False.elim (noCopy b rfl)
    | el => apply finish; simpa [compileOp] using memoryEl_dispatch xs ys s1 s2 t1 states related v run
    | length => apply finish; simpa [compileOp, MemoryLength.op] using memoryLength_dispatch .array xs ys s1 s2 t1 states related v run
    | lengthByte => apply finish; simpa [compileOp, MemoryLength.op] using memoryLength_dispatch .bytes xs ys s1 s2 t1 states related v run
    | derefByte => apply finish; simpa [compileOp] using memoryByte_dispatch xs ys s1 s2 t1 states related v run
    | toListByte => apply finish; simpa [compileOp] using byteToList_dispatch xs ys s1 s2 t1 related v run
    | lengthByteVec => apply finish; simpa [compileOp, ByteVectorRead.sourceOp, ByteVectorRead.targetOp] using byteVectorRead_dispatch .length xs ys s1 s2 t1 related v run
    | derefByteVec => apply finish; simpa [compileOp, ByteVectorRead.sourceOp, ByteVectorRead.targetOp] using byteVectorRead_dispatch .deref xs ys s1 s2 t1 related v run
    | stringCmp fast cmp => apply finish; simpa [compileOp] using byteStringCmp_dispatch fast cmp xs ys s1 s2 t1 related v run
    | boundsCheckArray => apply finish; simpa [compileOp] using memoryBoundsArray_dispatch xs ys s1 s2 t1 states related v run
    | boundsCheckByte b => apply finish; simpa [compileOp] using memoryBoundsByte_dispatch b xs ys s1 s2 t1 states related v run
    | configGC => apply finish; simpa [compileOp] using configGC_dispatch xs ys s1 s2 t1 related v run
    | mutCons a b => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | updateCons => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | finaliseCons => simp [ClosSem.doApp, ClosSem.applyMemory] at run

/-- Ordinary operators preserve simulation under a shared source clock bound. -/
theorem expressionSimulationBelow_ordinary {C F : Type} (clockBound : Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args)
    (notForce : op ≠ .thunkOp .forceThunk) (notInstall : op ≠ .install) :
    expressionSimulationBelow (C := C) (F := F) clockBound [.op trace op args] := by
  cases op with
  | label index => exact expressionSimulationBelow_rejected clockBound trace (.label index) args argsIH
  | ffi name => exact expressionSimulationBelow_ffi clockBound trace name args argsIH
  | intOp operation => exact expressionSimulationBelow_int clockBound trace operation args argsIH
  | wordOp operation => exact expressionSimulationBelow_word clockBound trace operation args argsIH
  | install => exact False.elim (notInstall rfl)
  | thunkOp operation =>
    cases operation with
    | allocThunk mode => exact expressionSimulationBelow_allocThunk clockBound trace mode args argsIH
    | updateThunk mode => exact expressionSimulationBelow_updateThunk clockBound trace mode args argsIH
    | forceThunk => exact False.elim (notForce rfl)
  | globOp operation =>
    cases operation with
    | global index => exact expressionSimulationBelow_global clockBound trace index args argsIH
    | setGlobal index => exact expressionSimulationBelow_setGlobal clockBound trace index args argsIH
    | allocGlobal => exact expressionSimulationBelow_alloc clockBound trace args argsIH
    | globalsPtr => exact expressionSimulationBelow_rejected clockBound trace .globalsPtr args argsIH
    | setGlobalsPtr => exact expressionSimulationBelow_rejected clockBound trace .setGlobalsPtr args argsIH
  | blockOp operation =>
    cases operation with
    | cons tag => exact expressionSimulationBelow_consBlock clockBound trace tag args argsIH
    | elemAt index => exact expressionSimulationBelow_inspect clockBound trace (.elemAt index) args argsIH
    | tagLenEq tag len => exact expressionSimulationBelow_inspect clockBound trace (.tagLengthEq tag len) args argsIH
    | lenEq len => exact expressionSimulationBelow_inspect clockBound trace (.lengthEq len) args argsIH
    | tagEq tag => exact expressionSimulationBelow_inspect clockBound trace (.tagEq tag) args argsIH
    | lengthBlock => exact expressionSimulationBelow_inspect clockBound trace .length args argsIH
    | boolTest test => exact expressionSimulationBelow_boolean clockBound trace (.test test) args argsIH
    | boolNot => exact expressionSimulationBelow_boolean clockBound trace .not args argsIH
    | boundsCheckBlock => exact expressionSimulationBelow_compare clockBound trace .bounds args argsIH
    | consExtend tag => exact expressionSimulationBelow_extend clockBound trace tag args argsIH
    | fromList tag => exact expressionSimulationBelow_listOp clockBound trace (.fromList tag) args argsIH
    | listAppend => exact expressionSimulationBelow_listOp clockBound trace .append args argsIH
    | constant constant => exact expressionSimulationBelow_constant clockBound trace constant args argsIH
    | equal => exact expressionSimulationBelow_equal clockBound trace args argsIH
    | equalConst part =>
      cases part with
      | int n => exact expressionSimulationBelow_compare clockBound trace (.intEq n) args argsIH
      | str text => exact expressionSimulationBelow_compare clockBound trace (.stringEq text) args argsIH
      | w64 word => exact expressionSimulationBelow_compare clockBound trace (.wordEq word) args argsIH
      | con tag fields => exact expressionSimulationBelow_rejected clockBound trace (.equalCon tag fields) args argsIH
    | build parts => exact expressionSimulationBelow_rejected clockBound trace (.build parts) args argsIH
  | memOp operation =>
    cases operation with
    | ref => exact expressionSimulationBelow_ref clockBound trace args argsIH
    | update => exact expressionSimulationBelow_updateArray clockBound trace args argsIH
    | el => exact expressionSimulationBelow_memoryEl clockBound trace args argsIH
    | length => exact expressionSimulationBelow_memoryLength clockBound trace .array args argsIH
    | lengthByte => exact expressionSimulationBelow_memoryLength clockBound trace .bytes args argsIH
    | refByte flag =>
      cases flag with
      | false => exact expressionSimulationBelow_refByte clockBound trace args argsIH
      | true => exact expressionSimulationBelow_refByteTrue clockBound trace args argsIH
    | refArray => exact expressionSimulationBelow_refArray clockBound trace args argsIH
    | derefByte => exact expressionSimulationBelow_memoryByte clockBound trace args argsIH
    | updateByte => exact expressionSimulationBelow_updateByte clockBound trace args argsIH
    | concatByteVec => exact expressionSimulationBelow_byteConstruct clockBound trace .concat args argsIH
    | fromListByte => exact expressionSimulationBelow_byteConstruct clockBound trace .fromList args argsIH
    | toListByte => exact expressionSimulationBelow_byteToList clockBound trace args argsIH
    | lengthByteVec => exact expressionSimulationBelow_byteVectorRead clockBound trace .length args argsIH
    | derefByteVec => exact expressionSimulationBelow_byteVectorRead clockBound trace .deref args argsIH
    | stringCmp fast comparison => exact expressionSimulationBelow_byteStringCmp clockBound trace fast comparison args argsIH
    | xorByte => exact expressionSimulationBelow_xorByte clockBound trace args argsIH
    | copyByte fresh =>
      cases fresh with
      | false => exact expressionSimulationBelow_copyByteInto clockBound trace args argsIH
      | true => exact expressionSimulationBelow_copyByteNew clockBound trace args argsIH
    | boundsCheckArray => exact expressionSimulationBelow_memoryBoundsArray clockBound trace args argsIH
    | boundsCheckByte loose => exact expressionSimulationBelow_memoryBoundsByte clockBound trace loose args argsIH
    | mutCons tag size => exact expressionSimulationBelow_rejected clockBound trace (.mutCons tag size) args argsIH
    | updateCons => exact expressionSimulationBelow_rejected clockBound trace .updateCons args argsIH
    | finaliseCons => exact expressionSimulationBelow_rejected clockBound trace .finaliseCons args argsIH
    | configGC => exact expressionSimulationBelow_configGC clockBound trace args argsIH


end Flapjack.Compiler.Backend.ClosToBvl
