import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsMove
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsAllocation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsLoopControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsCalls
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsPrimitives
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsControl

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the universally quantified induction motive; no
independent HOL declaration. The final theorem spells out the original result. -/
private def programInvariant {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat),
    ssaCcTrans prog ssa next tables = (output, ssaOut, nextOut) →
    ssaMapOK next ssa ∧ isAllocVar next →
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut

/-- Complete original native SSA compiler invariant. Every constructor case is
assembled by native datatype induction, including nested return/exception
handler programs. Only the original compiler equality and input invariant are
premises; all output invariants are conclusions. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransProps {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans prog ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  have all : ∀ (p : WordLangProgHOL (BitVec width)), programInvariant p := by
    intro p
    apply WordLangProgHOL.rec
      (motive_1 := programInvariant)
      (motive_2 := fun ret => match ret with | none => True | some r => programInvariant r.2.2.1)
      (motive_3 := fun exc => match exc with | none => True | some r => programInvariant r.2.1)
      (motive_4 := fun r => programInvariant r.2.2.1)
      (motive_5 := fun r => programInvariant r.2.1)
      (motive_6 := fun r => programInvariant r.2.1)
      (motive_7 := fun r => programInvariant r.1) (t := p)
    case skip =>
      exact ssaCcTransPropsSkip
    case move =>
      intro priority moves
      exact ssaCcTransPropsMove priority moves
    case inst =>
      intro instruction
      exact ssaCcTransPropsInst instruction
    case assign =>
      intro name exp
      exact ssaCcTransPropsAssign name exp
    case get =>
      intro destination store
      exact ssaCcTransPropsGet destination store
    case set =>
      intro store exp
      exact ssaCcTransPropsSet store exp
    case store =>
      intro exp name
      exact ssaCcTransPropsStore exp name
    case alloc =>
      intro destination cutsets
      exact ssaCcTransPropsAlloc destination cutsets
    case storeConsts =>
      intro a b c d ws
      exact ssaCcTransPropsStoreConsts a b c d ws
    case raise =>
      intro name
      exact ssaCcTransPropsRaise name
    case «return» =>
      intro label values
      exact ssaCcTransPropsReturn label values
    case «break» =>
      intro label
      exact ssaCcTransPropsBreak label
    case «continue» =>
      intro label
      exact ssaCcTransPropsContinue label
    case tick =>
      exact ssaCcTransPropsTick
    case opCurrHeap =>
      intro operator destination source
      exact ssaCcTransPropsOpCurrHeap operator destination source
    case locValue =>
      intro destination source
      exact ssaCcTransPropsLocValue destination source
    case install =>
      intro ptr len dptr dlen cutsets
      exact ssaCcTransPropsInstall ptr len dptr dlen cutsets
    case codeBufferWrite =>
      intro address value
      exact ssaCcTransPropsCodeBufferWrite address value
    case dataBufferWrite =>
      intro address value
      exact ssaCcTransPropsDataBufferWrite address value
    case ffi =>
      intro function configuration configurationLength array arrayLength cutsets
      exact ssaCcTransPropsFFI function configuration configurationLength array arrayLength cutsets
    case shareInst =>
      intro operator destination exp
      exact ssaCcTransPropsShareInst operator destination exp
    case mustTerminate =>
      intro body bodyIH ssa next tables output ssaOut nextOut produced h
      exact ssaCcTransPropsMustTerminate body ssa next tables
        (fun bodyOut treeOut counterOut eq valid => bodyIH ssa next tables bodyOut treeOut counterOut eq valid)
        output ssaOut nextOut produced h
    case seq =>
      intro first second firstIH secondIH ssa next tables output ssaOut nextOut produced h
      apply ssaCcTransPropsSeq first second ssa next tables ?_ output ssaOut nextOut produced h
      constructor
      · intro firstOut firstTree firstCounter _ bodyOut treeOut counterOut eq valid
        exact secondIH firstTree firstCounter tables bodyOut treeOut counterOut eq valid
      · exact firstIH ssa next tables
    case ite =>
      intro cmp condition right yes no yesIH noIH ssa next tables output ssaOut nextOut produced h
      apply ssaCcTransPropsIf cmp condition right yes no ssa next tables ?_
        output ssaOut nextOut produced h
      constructor
      · intro conditionOut rightOut yesOut yesTree yesCounter _ bodyOut treeOut counterOut eq valid
        exact noIH ssa yesCounter tables bodyOut treeOut counterOut eq valid
      · intro conditionOut rightOut _ bodyOut treeOut counterOut eq valid
        exact yesIH ssa next tables bodyOut treeOut counterOut eq valid
    case loop =>
      intro names body exitNames bodyIH ssa next tables output ssaOut nextOut produced h
      apply ssaCcTransPropsLoop names body exitNames ssa next tables ?_
        output ssaOut nextOut produced h
      intro setupProg refreshed counter ssaNames ssaExit bodyMap _ bodyOut treeOut counterOut eq valid
      exact bodyIH bodyMap counter ((refreshed, names, exitNames) :: tables)
        bodyOut treeOut counterOut eq valid
    case call =>
      intro returns dest args handler retIH excIH ssa next tables output ssaOut nextOut produced h
      cases returns with
      | none => exact ssaCcTransPropsTailCall dest args handler ssa next tables output ssaOut nextOut produced h
      | some ret =>
        rcases ret with ⟨ret, cutsets, retHandler, l1, l2⟩
        apply ssaCcTransPropsReturningCall ret cutsets retHandler l1 l2 dest args handler ssa next tables ?_
          output ssaOut nextOut produced h
        constructor
        · intro allNames ls stackMov stackTree stackCounter stackSet names convArgs moveArgs
            cutTree retMov retTree retCounter retRegisters retInputTree retInputCounter
            renRetHandler retOutTree retOutCounter regs movRetHandler v n v2 excHandler v4 excL1 excL2
            freshLabel freshTree freshCounter guards bodyOut treeOut counterOut eq valid
          rcases guards with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, handlerEq, vEq, v2Eq, v4Eq, _⟩
          rw [vEq, v2Eq, v4Eq] at handlerEq
          rw [handlerEq] at excIH
          exact excIH freshTree freshCounter tables bodyOut treeOut counterOut eq valid
        · intro allNames ls stackMov stackTree stackCounter stackSet names convArgs moveArgs
            cutTree retMov retTree retCounter retRegisters retInputTree retInputCounter _
            bodyOut treeOut counterOut eq valid
          exact retIH retInputTree retInputCounter tables bodyOut treeOut counterOut eq valid
    case none => exact True.intro
    case some => intro value ih; exact ih
    case none => exact True.intro
    case some => intro value ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro body rest ih; exact ih
  exact all prog ssa next tables output ssaOut nextOut produced h

end Flapjack.Compiler.Backend.WordAlloc
