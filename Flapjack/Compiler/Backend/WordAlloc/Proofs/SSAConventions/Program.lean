import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Primitives
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Instructions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Control
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Calls

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the generalized native structural induction motive;
no separately named HOL original. -/
private def programPre {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
    isAllocVar next ∧ ssaMapOK next ssa →
      preAllocConventionsHOL (ssaCcTrans prog ssa next tables).1 = true

/-- Complete original SSA pre-convention theorem, assembled by native mutual
structural induction including both nested return and exception handlers.
Only the original input allocation class and SSA map invariant are premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_preAllocConventions {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans prog ssa next tables).1 = true := by
  have all : ∀ (p : WordLangProgHOL (BitVec width)), programPre p := by
    intro p
    apply WordLangProgHOL.rec
      (motive_1 := programPre)
      (motive_2 := fun ret => match ret with | none => True | some r => programPre r.2.2.1)
      (motive_3 := fun exc => match exc with | none => True | some r => programPre r.2.1)
      (motive_4 := fun r => programPre r.2.2.1)
      (motive_5 := fun r => programPre r.2.1)
      (motive_6 := fun r => programPre r.2.1)
      (motive_7 := fun r => programPre r.1) (t := p)
    case skip =>
      exact ssaCcTrans_preAllocSkip
    case move =>
      intro priority moves
      exact ssaCcTrans_preAllocMove priority moves
    case inst =>
      intro instruction
      exact ssaCcTrans_preAllocInst instruction
    case assign =>
      intro name exp
      exact ssaCcTrans_preAllocAssign name exp
    case get =>
      intro destination store
      exact ssaCcTrans_preAllocGet destination store
    case set =>
      intro store exp
      exact ssaCcTrans_preAllocSet store exp
    case store =>
      intro exp name
      exact ssaCcTrans_preAllocStore exp name
    case alloc =>
      intro destination cutsets
      exact ssaCcTrans_preAllocAlloc destination cutsets
    case storeConsts =>
      intro a b c d ws
      exact ssaCcTrans_preAllocStoreConsts a b c d ws
    case raise =>
      intro name
      exact ssaCcTrans_preAllocRaise name
    case «return» =>
      intro label values
      exact ssaCcTrans_preAllocReturn label values
    case «break» =>
      intro label
      exact ssaCcTrans_preAllocBreak label
    case «continue» =>
      intro label
      exact ssaCcTrans_preAllocContinue label
    case tick =>
      exact ssaCcTrans_preAllocTick
    case opCurrHeap =>
      intro operator destination source
      exact ssaCcTrans_preAllocOpCurrHeap operator destination source
    case locValue =>
      intro destination source
      exact ssaCcTrans_preAllocLocValue destination source
    case install =>
      intro ptr len dptr dlen cutsets
      exact ssaCcTrans_preAllocInstall ptr len dptr dlen cutsets
    case codeBufferWrite =>
      intro address value
      exact ssaCcTrans_preAllocCodeBufferWrite address value
    case dataBufferWrite =>
      intro address value
      exact ssaCcTrans_preAllocDataBufferWrite address value
    case ffi =>
      intro function configuration configurationLength array arrayLength cutsets
      exact ssaCcTrans_preAllocFFI function configuration configurationLength array arrayLength cutsets
    case shareInst =>
      intro operator destination exp
      exact ssaCcTrans_preAllocShareInst operator destination exp
    case mustTerminate =>
      intro body bodyIH
      exact ssaCcTrans_preAllocMustTerminate body bodyIH
    case seq =>
      intro first second firstIH secondIH
      exact ssaCcTrans_preAllocSeq first second firstIH secondIH
    case ite =>
      intro cmp condition right yes no yesIH noIH
      exact ssaCcTrans_preAllocIf cmp condition right yes no yesIH noIH
    case loop =>
      intro names body exitNames bodyIH
      exact ssaCcTrans_preAllocLoop names exitNames body bodyIH
    case call =>
      intro returns dest args handler retIH excIH
      cases returns with
      | none => exact ssaCcTrans_preAllocTailCall dest args handler
      | some ret =>
        rcases ret with ⟨ret, cutsets, retHandler, l1, l2⟩
        apply ssaCcTrans_preAllocReturningCall ret cutsets retHandler l1 l2 dest args handler retIH
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
