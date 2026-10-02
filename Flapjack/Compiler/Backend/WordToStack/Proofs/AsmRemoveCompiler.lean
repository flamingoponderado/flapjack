import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveHelpers

namespace Flapjack.WordToStackProofs.AsmRemoveCompiler
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.WordToStackProofs.AsmRemoveHelpers

/-- Flapjack-specific implication between the two full native predicates.
No separate HOL declaration names this stronger uniform transport; it discharges
only register-name obligations that the complete register bound already checks. -/
private theorem removeOfBound {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width]
    (conf : AsmConfigExact configWidth) (program : HolProg width) (bound : Nat)
    (bounded : regBound program bound)
    (room : bound ≤ conf.regCount - conf.avoidRegs.length) : stackAsmRemove conf program := by
  cases program with
  | seq first second =>
      simp only [stackAsmRemove]
      exact ⟨removeOfBound conf first bound bounded.1 room,
        removeOfBound conf second bound bounded.2 room⟩
  | loop body => exact removeOfBound conf body bound bounded room
  | ite cmp register right first second =>
      exact ⟨removeOfBound conf first bound bounded.2.2.1 room,
        removeOfBound conf second bound bounded.2.2.2 room⟩
  | call returns target handler =>
      cases returns with
      | none => trivial
      | some record =>
          match hRet : record with
          | (body,register,l1,l2) =>
              unfold regBound at bounded
              have bodySafe := removeOfBound conf body bound bounded.2.1 room
              cases handler with
              | none => simpa only [stackAsmRemove, and_true] using bodySafe
              | some record =>
                  match hHandle : record with
                  | (handlerBody,h1,h2) =>
                      exact ⟨bodySafe, removeOfBound conf handlerBody bound bounded.2.2.2 room⟩
  | _ => simp_all [stackAsmRemove, regName, regBound] <;> omega
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

/-- Flapjack-only instruction calculation: removal checks introduced loads
and stores, without the original instruction's register-bound obligations. -/
private theorem instRemove {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (i : HolInst width) (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length) :
    stackAsmRemove conf (wInstNative i frame) := by
  cases i with
  | arith a =>
      cases a <;> try (rename_i op d src ri; cases ri)
      all_goals simp only [wInstNative, wRegWrite1Native, wReg1, wReg2]
      all_goals try split_ifs
      all_goals simp only [stackAsmRemove, wStackLoadNative, List.append_nil,
        List.nil_append, List.cons_append, regName]
      all_goals repeat' apply And.intro
      all_goals first | trivial | omega
  | mem op d addr =>
      cases addr
      cases op
      all_goals simp only [wInstNative, wRegWrite1Native, wReg1, wReg2]
      all_goals try split_ifs
      all_goals simp only [stackAsmRemove, wStackLoadNative, List.append_nil,
        List.nil_append, List.cons_append, regName]
      all_goals repeat' apply And.intro
      all_goals first | trivial | omega
  | fp f =>
      cases f
      all_goals by_cases hw : width = 64
      all_goals simp only [wInstNative, hw, if_true, if_false,
        wRegWrite1Native, wRegWrite2Native, wReg1, wReg2]
      all_goals try split_ifs
      all_goals simp only [stackAsmRemove, wStackLoadNative, List.append_nil,
        List.nil_append, List.cons_append, regName]
      all_goals repeat' apply And.intro
      all_goals first | trivial | omega
  | const n w =>
      simp only [wInstNative, wRegWrite1Native]
      split_ifs <;> simp_all [stackAsmRemove, regName] <;> omega
  | skip => trivial

/-- Entire original compiler removal theorem, with exactly its reduced-count
room guard and false-performance premise. All recursive hypotheses are internal.
The original explicitly shares configuration and source-program word dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_remove_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmRemove {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (plain : perf = false) :
    stackAsmRemove conf (compNative conf perf program bs frame).1 := by
  subst perf
  cases program with
  | inst i =>
      simp only [compNative]
      exact instRemove conf (HolInst.ofWordLangInst i) frame room
  | move priority moves =>
      simp only [compNative, wMoveNative]
      exact removeOfBound conf _ (frame.1 + 2)
        (RegisterBoundFlat.formattedMovesBound _ frame) (by omega)
  | mustTerminate body =>
      simp only [compNative]
      exact wordToStackStackAsmRemove conf false body bs frame room rfl
  | seq first second =>
      simp only [compNative, stackAsmRemove]
      exact ⟨wordToStackStackAsmRemove conf false first bs frame room rfl,
        wordToStackStackAsmRemove conf false second
          (compNative conf false first bs frame).2 frame room rfl⟩
  | loop liveIn body liveOut =>
      simp only [compNative, stackAsmRemove]
      exact wordToStackStackAsmRemove conf false body bs frame room rfl
  | alloc r live =>
      simp only [compNative, stackAsmRemove]
      exact ⟨wLiveStackAsmRemove conf live bs frame _ _ room rfl, by trivial⟩
  | set name exp =>
      cases name <;> cases exp
      all_goals simp only [compNative, wReg1]
      all_goals try split_ifs
      all_goals simp_all [stackAsmRemove, wStackLoadNative, regName, storeNameOfWord] <;> omega
  | shareInst op v exp =>
      simp only [compNative]
      cases addressEq : expToAddrHOL exp with
      | none => trivial
      | some addr =>
          exact removeOfBound conf _ (frame.1 + 2)
            (RegisterBoundInstructions.shareBound op v (HolAddr.ofWordLangAddr addr) frame) (by omega)
  | ite cmp r ri first second =>
      have ha (next : AppList (BitVec width) × Nat) :=
        wordToStackStackAsmRemove conf false first next frame room rfl
      have hb (next : AppList (BitVec width) × Nat) :=
        wordToStackStackAsmRemove conf false second next frame room rfl
      simp only [compNative]
      cases ri <;> simp only [wReg1, wReg2]
      all_goals split_ifs
      all_goals simp only [stackAsmRemove, wStackLoadNative, List.append_nil,
        List.nil_append, List.cons_append, regName]
      all_goals repeat' apply And.intro
      all_goals first | apply ha | apply hb | trivial | omega
  | call returns dest args handler =>
      have hd := callDestStackAsmRemove conf dest args frame
        (callDestNative (width := width) dest args frame).1
        (callDestNative (width := width) dest args frame).2 room rfl
      have named : regName frame.1 conf := by simp only [regName]; omega
      have argumentSafe (destination : Sum Nat Nat) (count f f' : Nat) :
          stackAsmRemove conf (stackArgsNative destination count (frame.1,f,f') : HolProg width) :=
        removeOfBound conf _ (frame.1 + 2)
          (RegisterBoundRecursive.stackArgsBound destination count (frame.1,f,f')) (by omega)
      cases returns with
      | none =>
          simp only [compNative, seqStackFreeNative]
          split <;> simpa only [stackAsmRemove, and_true] using hd.1
      | some record =>
          match hReturn : record with
          | (values,live,retCode,l1,l2) =>
              have liveSafe := wLiveStackAsmRemove conf live bs frame
                (wLiveNative live bs frame).1 (wLiveNative live bs frame).2 room rfl
              have retSafe (next : AppList (BitVec width) × Nat) :=
                wordToStackStackAsmRemove conf false retCode next frame room rfl
              cases handler with
              | none =>
                  simp only [compNative, Bool.false_eq_true, if_false, stackAsmRemove]
                  simp only [copyRetStackAsmRemove conf false frame values _ named]
                  repeat' apply And.intro
                  all_goals first | exact hd.1 | exact liveSafe | apply argumentSafe | apply retSafe | trivial
              | some record =>
                  match hHandler : record with
                  | (handleValue,handleCode,h1,h2) =>
                      have handleSafe (next : AppList (BitVec width) × Nat) :=
                        wordToStackStackAsmRemove conf false handleCode next frame room rfl
                      have pushSafe : stackAsmRemove conf (pushHandlerNative false h1 h2 frame : HolProg width) := by
                        simp [pushHandlerNative, stackAsmRemove, named]
                      simp only [compNative, Bool.false_eq_true, if_false, stackAsmRemove]
                      simp only [copyRetStackAsmRemove conf true frame values _ named,
                        popHandlerNative, stackAsmRemove, named, true_and,
                        stackHandlerArgsNative]
                      repeat' apply And.intro
                      all_goals first | exact hd.1 | exact liveSafe | exact pushSafe | apply argumentSafe | apply retSafe | apply handleSafe | trivial
  | _ =>
      simp only [compNative, wRegWrite1Native, wReg1, wReg2, seqStackFreeNative]
      all_goals try split_ifs
      all_goals simp only [stackAsmRemove, wStackLoadNative, List.append_nil,
        List.nil_append, List.cons_append, regName]
      all_goals repeat' apply And.intro
      all_goals first | trivial | omega
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Flapjack.WordToStackProofs.AsmRemoveCompiler
