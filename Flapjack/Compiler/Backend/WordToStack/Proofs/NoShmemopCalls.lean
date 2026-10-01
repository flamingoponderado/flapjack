import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemop.Handlers
import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers
import Flapjack.Pancake.WordConvs.PredicateEquations
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopReturn

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original tail Call case. The optional source handler remains arbitrary
and its original source guard is retained even though this compiler branch
ignores that handler. No induction hypothesis for ignored code is required. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopTailCall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (destination : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL (.call none destination args handler) = true)
    (compiled : compNative conf perf (.call none destination args handler) bs frame =
      (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  cases destination with
  | some label =>
      simp only [callDestNative, noShmemop, Bool.true_and]
      unfold seqStackFreeNative
      split <;> rfl
  | none =>
      by_cases empty : args.length = 0
      · simp only [callDestNative, dif_pos empty, noShmemop, Bool.true_and]
        unfold seqStackFreeNative
        split <;> rfl
      · simp only [callDestNative, dif_neg empty, noShmemop, wStackLoadNoShmemop,
          Bool.true_and]
        unfold seqStackFreeNative
        split <;> rfl


/-- Flapjack-specific projection of the accepted full guard equations. Other
constructor binders are specialized because they do not occur in this Call
projection; every actual Call binder remains arbitrary. No separate HOL original. -/
private theorem callNoShareClause {width : Nat} [NeZero width]
    (returns : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (destination : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    noShareInstSubprogsHOL (.call returns destination args handler) =
      ((match returns with | none => true | some (_,_,body,_,_) => noShareInstSubprogsHOL body) &&
       (match handler with | none => true | some (_,body,_,_) => noShareInstSubprogsHOL body)) := by
  have clauses := noShareInstDef
    (p := .skip)
    (p1 := .skip)
    (p2 := .skip)
    (c := .skip)
    (names := .ln)
    (exitNames := .ln)
    (v0 := .equal)
    (v1 := 0)
    (v2 := .reg 0)
    (r := returns)
    (dest := destination)
    (args := args)
    (h := handler)
    (v3 := 0)
    (v4 := (.ln, .ln))
    (v5 := 0)
    (l := 0)
    (v6 := .load)
    (v7 := 0)
    (v8 := (.var 0))
    (v9 := 0)
    (v10 := 0)
    (v11 := 0)
    (v12 := 0)
    (v13 := (.ln, .ln))
    (v18 := 0)
    (v19 := [])
    (v20 := .skip)
    (v21 := 0)
    (v22 := (.var 0))
    (v23 := 0)
    (v24 := .currHeap)
    (v25 := .currHeap)
    (v26 := (.var 0))
    (v27 := (.var 0))
    (v28 := 0)
    (v46 := 0)
    (v47 := 0)
    (v48 := 0)
    (v49 := 0)
    (v50 := [])
    (v51 := 0)
    (v52 := 0)
    (v53 := [])
    (v54 := 0)
    (v55 := 0)
    (v56 := .add)
    (v57 := 0)
    (v58 := 0)
    (v66 := 0)
    (v67 := 0)
    (v68 := 0)
    (v69 := 0)
    (v70 := (.implode []))
    (v71 := 0)
    (v72 := 0)
    (v73 := 0)
    (v74 := 0)
    (v75 := (.ln, .ln))
  exact clauses.2.2.2.2.1

/-- Flapjack-specific component property of the accepted call destination
compiler, without a separate original HOL declaration. -/
private theorem callDestNoShmemop {width : Nat} [NeZero width]
    (destination : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    noShmemop (callDestNative (width := width) destination args frame).1 = true := by
  cases destination with
  | some label => rfl
  | none =>
      by_cases empty : args.length = 0
      · simp only [callDestNative, dif_pos empty]; rfl
      · simp only [callDestNative, dif_neg empty, wStackLoadNoShmemop]; rfl

/-- Full original returning Call case with no handler, preserving bitmap
threading and only the genuine return-body induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopReturningCall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (values : List Nat) (live : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (label1 label2 : Nat)
    (destination : Option Nat) (args : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL
      (.call (some (values,live,retCode,label1,label2)) destination args none) = true)
    (compiled : compNative conf perf
      (.call (some (values,live,retCode,label1,label2)) destination args none) bs frame =
      (output, residual))
    (ihReturn : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL retCode = true →
      compNative conf perf retCode subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true := by
  have retGuard : noShareInstSubprogsHOL retCode = true := by
    simpa only [callNoShareClause, Bool.and_true] using guard
  have retSafe := ihReturn (wLiveNative live bs frame).2 frame
    (compNative conf perf retCode (wLiveNative live bs frame).2 frame).1
    (compNative conf perf retCode (wLiveNative live bs frame).2 frame).2 retGuard rfl
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  cases perf <;>
    simp [noShmemop, callDestNoShmemop, wLiveNoShmemop, stackArgsNative,
      stackMoveNoShmemop, copyRetNoShmemop, retSafe,
      perfCallPrefixNoShmemop, perfCallSuffixNoShmemop]


/-- Full original returning Call with a handler. The return compilation's
residual bitmap feeds the handler compiler, and only the two original child
induction hypotheses are used. All source handler payloads remain arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopHandledCall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (values : List Nat) (live : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (label1 label2 : Nat)
    (destination : Option Nat) (args : List Nat)
    (handleValue : Nat) (handleCode : WordLangProgHOL (BitVec width)) (handleLabel1 handleLabel2 : Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL
      (.call (some (values,live,retCode,label1,label2)) destination args
        (some (handleValue,handleCode,handleLabel1,handleLabel2))) = true)
    (compiled : compNative conf perf
      (.call (some (values,live,retCode,label1,label2)) destination args
        (some (handleValue,handleCode,handleLabel1,handleLabel2))) bs frame = (output,residual))
    (ihReturn : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL retCode = true →
      compNative conf perf retCode subBs subFrame = (subOutput,subResidual) →
      noShmemop subOutput = true)
    (ihHandler : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL handleCode = true →
      compNative conf perf handleCode subBs subFrame = (subOutput,subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true := by
  have guards : noShareInstSubprogsHOL retCode = true ∧
      noShareInstSubprogsHOL handleCode = true := by
    apply Bool.and_eq_true_iff.mp
    simpa only [callNoShareClause] using guard
  have retSafe := ihReturn (wLiveNative live bs frame).2 frame
    (compNative conf perf retCode (wLiveNative live bs frame).2 frame).1
    (compNative conf perf retCode (wLiveNative live bs frame).2 frame).2 guards.1 rfl
  have handlerSafe := ihHandler
    (compNative conf perf retCode (wLiveNative live bs frame).2 frame).2 frame
    (compNative conf perf handleCode
      (compNative conf perf retCode (wLiveNative live bs frame).2 frame).2 frame).1
    (compNative conf perf handleCode
      (compNative conf perf retCode (wLiveNative live bs frame).2 frame).2 frame).2 guards.2 rfl
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  cases perf <;>
    simp [noShmemop, callDestNoShmemop, wLiveNoShmemop, pushHandlerNoShmemop,
      stackHandlerArgsNoShmemop, popHandlerNoShmemop, copyRetNoShmemop,
      retSafe, handlerSafe, perfCallPrefixNoShmemop, perfCallSuffixNoShmemop]

end Flapjack.Compiler.Backend.WordToStack.Native
