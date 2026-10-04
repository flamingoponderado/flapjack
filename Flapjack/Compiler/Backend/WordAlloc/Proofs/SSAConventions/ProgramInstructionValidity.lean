import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.PrimitiveInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.InstInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.ShareInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.AllocationInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.ControlInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.CallInstructionValidity

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Flapjack factoring of the generalized native structural induction motive;
no separately named HOL original. -/
private def programValid {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
    everyVarHOL (fun x => decide (x < next)) prog = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config prog = true →
      fullInstOkLessExact config (ssaCcTrans prog ssa next tables).1 = true

/-- Complete original SSA instruction-validity theorem, assembled by native mutual
structural induction including both nested return and exception handlers.
Retains the original source variable bound, allocation class, SSA map invariant
and source instruction-validity hypotheses; no remaining induction premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) prog = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config prog = true) :
    fullInstOkLessExact config (ssaCcTrans prog ssa next tables).1 = true := by
  have all : ∀ (p : WordLangProgHOL (BitVec width)), programValid config p := by
    intro p
    apply WordLangProgHOL.rec
      (motive_1 := programValid config)
      (motive_2 := fun ret => match ret with | none => True | some r => programValid config r.2.2.1)
      (motive_3 := fun exc => match exc with | none => True | some r => programValid config r.2.1)
      (motive_4 := fun r => programValid config r.2.2.1)
      (motive_5 := fun r => programValid config r.2.1)
      (motive_6 := fun r => programValid config r.2.1)
      (motive_7 := fun r => programValid config r.1) (t := p)
    case skip =>
      exact ssaCcTrans_fullInstSkip config
    case move =>
      intro priority moves
      exact ssaCcTrans_fullInstMove config priority moves
    case inst =>
      intro instruction
      exact ssaCcTrans_fullInstInst config instruction
    case assign =>
      intro name exp
      exact ssaCcTrans_fullInstAssign config name exp
    case get =>
      intro destination store
      exact ssaCcTrans_fullInstGet config destination store
    case set =>
      intro store exp
      exact ssaCcTrans_fullInstSet config store exp
    case store =>
      intro exp name
      exact ssaCcTrans_fullInstStore config exp name
    case alloc =>
      intro destination cutsets
      exact ssaCcTrans_fullInstAlloc config destination cutsets
    case storeConsts =>
      intro a b c d ws
      exact ssaCcTrans_fullInstStoreConsts config a b c d ws
    case raise =>
      intro name
      exact ssaCcTrans_fullInstRaise config name
    case «return» =>
      intro label values
      exact ssaCcTrans_fullInstReturn config label values
    case «break» =>
      intro label
      exact ssaCcTrans_fullInstBreak config label
    case «continue» =>
      intro label
      exact ssaCcTrans_fullInstContinue config label
    case tick =>
      exact ssaCcTrans_fullInstTick config
    case opCurrHeap =>
      intro operator destination source
      exact ssaCcTrans_fullInstOpCurrHeap config operator destination source
    case locValue =>
      intro destination source
      exact ssaCcTrans_fullInstLocValue config destination source
    case install =>
      intro ptr len dptr dlen cutsets
      exact ssaCcTrans_fullInstInstall config ptr len dptr dlen cutsets
    case codeBufferWrite =>
      intro address value
      exact ssaCcTrans_fullInstCodeBufferWrite config address value
    case dataBufferWrite =>
      intro address value
      exact ssaCcTrans_fullInstDataBufferWrite config address value
    case ffi =>
      intro function configuration configurationLength array arrayLength cutsets
      exact ssaCcTrans_fullInstFFI config function configuration configurationLength array arrayLength cutsets
    case shareInst =>
      intro operator destination exp
      exact ssaCcTrans_fullInstShareInst config operator destination exp
    case mustTerminate =>
      intro body bodyIH
      exact ssaCcTrans_fullInstMustTerminate config body bodyIH
    case seq =>
      intro first second firstIH secondIH
      exact ssaCcTrans_fullInstSeq config first second firstIH secondIH
    case ite =>
      intro cmp condition right yes no yesIH noIH
      exact ssaCcTrans_fullInstIf config cmp condition right yes no yesIH noIH
    case loop =>
      intro names body exitNames bodyIH
      exact ssaCcTrans_fullInstLoop config names exitNames body bodyIH
    case call =>
      intro returns dest args handler retIH excIH
      cases returns with
      | none => exact ssaCcTrans_fullInstTailCall config dest args handler
      | some ret =>
        rcases ret with ⟨ret, cutsets, retHandler, l1, l2⟩
        apply ssaCcTrans_fullInstReturningCall config ret cutsets retHandler l1 l2 dest args handler retIH
        cases handler with
        | none => exact True.intro
        | some exc =>
          rcases exc with ⟨name, body, l1, l2⟩
          exact excIH
    case none => exact True.intro
    case some => intro value ih; exact ih
    case none => exact True.intro
    case some => intro value ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro body rest ih; exact ih
  exact all prog ssa next tables h

end Flapjack.WordAlloc
