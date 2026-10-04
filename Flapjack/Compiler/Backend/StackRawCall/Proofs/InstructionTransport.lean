import Flapjack.Compiler.Backend.StackRawCall.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.StackSem.Inst

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack StackSemStateOps StackSemExpressions
open Flapjack.Compiler.Backend.StackLang

/-! Flapjack-specific transport support for the full original instruction
simulation. These lemmas derive independence from actual native definitions;
they have no separate HOL declaration and assume no target evaluation. -/

theorem getVars_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (registers : List Nat) (source : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) :
    StackSemStateOps.getVars registers { source with code := code } = StackSemStateOps.getVars registers source := by
  induction registers with
  | nil => rfl
  | cons register registers ih => simp only [StackSemStateOps.getVars, StackSemStateOps.getVar, ih]

theorem wordExp_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width))
    (expression : WordLangExpHOL (BitVec width)) :
    wordExp { source with code := code } expression = wordExp source expression := by
  induction expression using wordExp.induct source <;>
    simp_all [wordExp, memLoad]

theorem assign_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (expression : WordLangExpHOL (BitVec width))
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    assign register expression { source with code := code } =
      (assign register expression source).map (fun state => { state with code := code }) := by
  simp only [assign, wordExp_codeUpdate]
  split <;> rfl

theorem instInteger_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemIntegerInstructions.instInteger instruction { source with code := code } =
      (StackSemIntegerInstructions.instInteger instruction source).map
        (fun result => result.map (fun state => { state with code := code })) := by
  cases instruction <;>
    simp only [StackSemIntegerInstructions.instInteger, assign_codeUpdate,
      getVars_codeUpdate, wordExp_codeUpdate, getVar, memLoad, memStore, setVar]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

theorem instHOL_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemInst.instHOL instruction { source with code := code } =
      (StackSemInst.instHOL instruction source).map
        (fun state => { state with code := code }) := by
  cases instruction <;>
    simp only [StackSemInst.instHOL, instInteger_codeUpdate]
  all_goals cases StackSemIntegerInstructions.instInteger _ source <;> simp

theorem instHOL_code_eq {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width)
    (source result : StackSemStateFiniteExact width C F)
    (execution : StackSemInst.instHOL instruction source = some result) :
    result.code = source.code := by
  have transport := instHOL_codeUpdate instruction source source.code
  have unchanged : { source with code := source.code } = source := by
    cases source
    rfl
  rw [unchanged, execution] at transport
  simp only [Option.map_some, Option.some.injEq] at transport
  have projected := congrArg (fun state : StackSemStateFiniteExact width C F => state.code) transport
  exact projected

theorem instHOL_stateRel {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width) (info : Spt Nat)
    (source target result : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target)
    (execution : StackSemInst.instHOL instruction source = some result) :
    ∃ targetResult, stateRel info result targetResult ∧
      StackSemInst.instHOL instruction target = some targetResult := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have codeEq := instHOL_code_eq instruction source result execution
  refine ⟨{ result with code := code }, ?_, ?_⟩
  · refine ⟨code, ?_, rfl, ?_, ?_⟩
    · simpa only [codeEq] using domain
    · simpa only [codeEq] using frames
    · simpa only [codeEq] using entries
  · rw [instHOL_codeUpdate, execution]
    rfl

end Flapjack.Compiler.Backend.StackRawCall
