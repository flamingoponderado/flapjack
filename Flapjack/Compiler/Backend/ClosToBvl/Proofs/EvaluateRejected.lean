import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence

/-! Source-rejected primitive cases of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Operations with no successful source dispatcher clause. -/
inductive RejectedOp where
  | label : Nat → RejectedOp
  | globalsPtr
  | setGlobalsPtr
  | build : List ClosLang.ConstPart → RejectedOp
  | equalCon : Nat → List Nat → RejectedOp
  | mutCons : Nat → Nat → RejectedOp
  | updateCons
  | finaliseCons

/-- The closure-language operation for a source-rejected primitive. -/
def RejectedOp.op : RejectedOp → ClosLang.Op
  | .label index => .label index
  | .globalsPtr => .globOp .globalsPtr
  | .setGlobalsPtr => .globOp .setGlobalsPtr
  | .build parts => .blockOp (.build parts)
  | .equalCon tag fields => .blockOp (.equalConst (.con tag fields))
  | .mutCons tag size => .memOp (.mutCons tag size)
  | .updateCons => .memOp .updateCons
  | .finaliseCons => .memOp .finaliseCons

/-- The current closure dispatcher rejects these operations for every argument
list. This is a statement about the candidate source evaluator; it is not
itself a port of a HOL correctness theorem. -/
theorem rejectedOp_typeError {C F : Type} (op : RejectedOp)
    (args : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.doApp op.op args s = .err (.abort .typeError) := by
  cases op <;> cases args <;> simp [RejectedOp.op, ClosSem.doApp, ClosSem.applyGlobal,
    ClosSem.applyBlock, ClosSem.applyMemory]

/-- Argument errors propagate through a compiled source-rejected operation. -/
theorem evaluatePost_rejected_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (op : RejectedOp) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value) (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (compileOp op.op) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- These source-rejected operations satisfy the expression simulation when
their arguments do, including propagation of argument errors. -/
theorem expressionSimulation_rejected {C F : Type} (trace : BackendCommon.Tra)
    (op : RejectedOp) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace op.op args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace op.op args] aux =
        ([.op (compileOp op.op) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      cases op <;> simp [compileExpListHOL, compileExpHOL, argsCompile, RejectedOp.op]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_rejected_error s sMiddle t targetEnv f op targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        cases op <;> simp [RejectedOp.op, ClosSem.doApp, ClosSem.applyGlobal,
          ClosSem.applyBlock, ClosSem.applyMemory] at run <;> exact False.elim (noTypeError run.1.symm)

end Flapjack.Compiler.Backend.ClosToBvl
