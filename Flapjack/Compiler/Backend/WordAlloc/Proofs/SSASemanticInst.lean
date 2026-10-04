import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstCommon
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstConst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstBinop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstShift
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstDiv
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLongMul
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLongDiv
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstAddCarry
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstAddOverflow
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstSubOverflow
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLoad
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLoad8
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLoad32
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstStore
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstStore8
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstStore32

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstWitnesses

/-- Full original Inst case of native SSA correctness. Exhaustive case analysis
assembles all34 native constructors using their source-reviewed case proofs.
All six original premises and complete Error-exempt permutation/result/fullframe/
result-sensitive locals are retained, with no target evaluation, successful-source,
post-state or induction premise. Evaluator/FP proofs inherit reals_as_rational_cuts
(SOUNDNESS item 8), including choice rounding/quiet NaNs. This is the Inst case;
full program correctness remains separate. -/
theorem ssaCcTransCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (instruction : WordLangInst (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst instruction) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst instruction) source target ssa next tables := by
  cases instruction with
  | skip => apply ssaCcTransCorrectInstSkip; exact h
  | const name word => apply ssaCcTransCorrectInstConst; exact h
  | arith operation =>
    cases operation with
    | binop arg0 arg1 arg2 arg3 => apply ssaCcTransCorrectInstBinop; exact h
    | shift arg0 arg1 arg2 arg3 => apply ssaCcTransCorrectInstShift; exact h
    | div arg0 arg1 arg2 => apply ssaCcTransCorrectInstDiv; exact h
    | longMul arg0 arg1 arg2 arg3 => apply ssaCcTransCorrectInstLongMul; exact h
    | longDiv arg0 arg1 arg2 arg3 arg4 => apply ssaCcTransCorrectInstLongDiv; exact h
    | addCarry arg0 arg1 arg2 arg3 => apply ssaCcTransCorrectInstAddCarry; exact h
    | addOverflow arg0 arg1 arg2 arg3 => apply ssaCcTransCorrectInstAddOverflow; exact h
    | subOverflow arg0 arg1 arg2 arg3 => apply ssaCcTransCorrectInstSubOverflow; exact h
  | mem operation data address =>
    cases address with
    | addr base offset =>
      cases operation with
      | load => apply ssaCcTransCorrectInstLoad; exact h
      | load8 => apply ssaCcTransCorrectInstLoad8; exact h
      | load16 => apply ssaCcTransCorrectInstLoad16; exact h
      | load32 => apply ssaCcTransCorrectInstLoad32; exact h
      | store => apply ssaCcTransCorrectInstStore; exact h
      | store8 => apply ssaCcTransCorrectInstStore8; exact h
      | store16 => apply ssaCcTransCorrectInstStore16; exact h
      | store32 => apply ssaCcTransCorrectInstStore32; exact h
end Flapjack.Compiler.Backend.WordAlloc
