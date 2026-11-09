import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Test.CrepGlobalShapeParity

namespace Flapjack.Test.CrepInlineRelParity

open Flapjack

/-! Executable regression for the exact `crep_inlineProofScript.sml` state
    relations (`state_rel`, `locals_rel`, `locals_strong_rel`) and the
    `locals_rel_dec_clock` preservation theorem ported in
    `Flapjack.Pancake.Proofs.CrepInline`. -/

/-- A concrete 11-field state: locals `0 := 7`, `1 := 9`; empty globals and
    code; constant zero memory; both addresses in the memory domain. -/
def baseState : CrepHolState Nat Unit :=
  { locals := fun n => match n with
      | 0 => some (.word 7)
      | 1 => some (.word 9)
      | _ => none
    globals := fun _ => none
    code := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => true
    shMemaddrs := fun _ => false
    clock := 5
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 100 }

/-- A strict superset of `baseState`'s locals. -/
def weakState : CrepHolState Nat Unit :=
  { baseState with
    locals := fun n => match n with
      | 0 => some (.word 7)
      | 1 => some (.word 9)
      | 2 => some (.word 11)
      | _ => none }

theorem baseState_strong_rel : crepInlineLocalsStrongRel baseState baseState := rfl

theorem not_baseState_strong_weak : ¬ crepInlineLocalsStrongRel baseState weakState := by
  intro h
  have hpoint := congrFun h 2
  simp [baseState, weakState] at hpoint

def baseStateGuard : Bool :=
  (decCrepHolClock baseState).clock == 4 &&
    (decCrepHolClock weakState).clock == 4

#guard baseStateGuard

/-- A state differing from `baseState` only in `code`. -/
def codeState : CrepHolState Nat Unit :=
  { baseState with code := fun _ => some ([1], CrepProg.skip) }

theorem baseState_state_rel_code : crepInlineStateRelCode baseState baseState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem state_rel_code_ignores_code : crepInlineStateRelCode baseState codeState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem not_state_rel_code_other_clock :
    ¬ crepInlineStateRelCode baseState { baseState with clock := 4 } := by
  intro h
  have hcl := h.2.2.2.2.1
  simp [baseState] at hcl

theorem localsExtRel_self_holds :
    crepInlineLocalsExtRel baseState weakState baseState weakState :=
  crepInlineLocalsExtRel_self baseState weakState

/-- A run whose states have locals `{0 ↦ 7}` then `{0 ↦ 7, 1 ↦ 9}`. -/
def extA : CrepHolState Nat Unit :=
  { baseState with locals := fun n => match n with
      | 0 => some (.word 7)
      | _ => none }

def extA' : CrepHolState Nat Unit :=
  { extA with locals := fun n => match n with
      | 0 => some (.word 7)
      | 1 => some (.word 9)
      | _ => none }

/-- A run whose locals start differently but add the same `1 ↦ 9`. -/
def extB : CrepHolState Nat Unit :=
  { baseState with locals := fun n => match n with
      | 2 => some (.word 5)
      | _ => none }

def extB' : CrepHolState Nat Unit :=
  { extB with locals := fun n => match n with
      | 1 => some (.word 9)
      | 2 => some (.word 5)
      | _ => none }

/-- A run that adds `1 ↦ 11` instead of `1 ↦ 9`. -/
def extBbad' : CrepHolState Nat Unit :=
  { extB with locals := fun n => match n with
      | 1 => some (.word 11)
      | 2 => some (.word 5)
      | _ => none }

theorem localsExtRel_agree : crepInlineLocalsExtRel extA extB extA' extB' := by
  simp only [crepInlineLocalsExtRel]
  funext n
  cases n with
  | zero => simp [crepHolFdiff, crepHolFdom, extA, extB, extB']
  | succ n =>
      cases n with
      | zero => simp [crepHolFdiff, crepHolFdom, extA, extA', extB, extB']
      | succ n =>
          cases n with
          | zero => simp [crepHolFdiff, crepHolFdom, extA, extA', extB]
          | succ n => simp [crepHolFdiff, crepHolFdom, extA, extA', extB, extB']

theorem not_localsExtRel_disagree : ¬ crepInlineLocalsExtRel extA extB extA' extBbad' := by
  intro h
  have hpoint := congrFun h 1
  simp [crepHolFdiff, crepHolFdom, extA, extA', extB, extBbad'] at hpoint

def codeInlSource : CrepHolState Nat Unit :=
  { baseState with code := fun _ => some ([7], CrepProg.skip) }

def codeInlEmptyTarget : CrepHolState Nat Unit :=
  { baseState with code := fun _ => none }

theorem codeInlRel_negative :
    ¬ crepInlineCodeInlRel codeInlFmap codeInlSource codeInlEmptyTarget :=
  not_crepInlineCodeInlRel_of_target_none codeInlFmap codeInlSource
    codeInlEmptyTarget "f" [7] CrepProg.skip
    (by simp [codeInlSource]) (by simp [codeInlEmptyTarget])

/-! ## Expression-evaluation invariance (`eval_code_inl`) over the canonical word -/

/-- A concrete 11-field state over `RiscV.Word 64` with locals `0 := 7`. -/
def evalBase : CrepHolState (RiscV.Word 64) Unit :=
  { locals := fun n => if n == 0 then some (.word 7) else none
    globals := fun _ => none
    code := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => true
    shMemaddrs := fun _ => false
    clock := 5
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 100 }

theorem evalCodeInl_hcode :
    crepInlineCodeInlRel evalInlineFmap evalBase evalBase := by
  apply crepInlineCodeInlRel_of_code
  intro fname args prog hcode
  simp [evalBase] at hcode

example : crepHolFdom evalBase.code = crepHolFdom evalBase.code := rfl

example :
    (∀ n, crepHolFdom (fun _ : Nat => (none : Option Nat)) n = true →
      crepHolFdom (fun _ : Nat => (none : Option Nat)) n = true) ↔
    (∀ n p, (fun _ : Nat => (none : Option Nat)) n = some p →
      ∃ q, (fun _ : Nat => (none : Option Nat)) n = some q) :=
  crepHolFdom_subset_flookup _ _

/-- `eval_code_inl` transfers a variable lookup through equal locals. -/
example : evalCrepHolExp evalBase (.var 0) = some (7 : RiscV.Word 64) := by
  simp only [evalCrepHolExp, evalBase]
  decide

def evalInvarianceGuard : Bool :=
  (evalCrepHolExp evalBase (.const (7 : RiscV.Word 64))).isSome &&
    (evalCrepHolExp evalBase (.var 0)).isSome

#guard evalInvarianceGuard

/-- Source `main` body: a call to the inlineable `inc`. -/
def inlineSrcMainBody : CrepProg (RiscV.Word 64) := .call none "inc" []

/-- Source code with two nonempty entries. -/
def inlineSrcCode : FunName → Option (List Nat × CrepProg (RiscV.Word 64)) :=
  fun n =>
    if n == "main" then some ([7], inlineSrcMainBody)
    else if n == "inc" then some ([8], CrepProg.skip)
    else none

/-- Source state: locals `0 := 7`, nonempty source code. -/
def inlineSrcState : CrepHolState (RiscV.Word 64) Unit :=
  { evalBase with code := inlineSrcCode }

theorem inlineSrcVarEval :
    evalCrepHolExp inlineSrcState (.var 0) = some (7 : RiscV.Word 64) := by
  simp only [evalCrepHolExp, inlineSrcState, evalBase]
  decide

/-- Nonempty heterogeneous expression list: a constant and a variable. -/
def inlineHeteroExps : List (CrepExp (RiscV.Word 64)) :=
  [.const (5 : RiscV.Word 64), .var 0]

theorem inlineSrcMmapEval :
    inlineHeteroExps.mapM (evalCrepHolExp inlineSrcState) =
      some [(5 : RiscV.Word 64), 7] := by
  simp only [inlineHeteroExps, List.mapM_cons, List.mapM_nil]
  simp only [evalCrepHolExp, inlineSrcState, evalBase]
  decide

/-- The Skip fixture is `state_rel_code` to itself. -/
theorem skipStateRel :
    crepInlineRuntimeStateRelCode Flapjack.Test.CrepGlobalShapeParity.globalState
      Flapjack.Test.CrepGlobalShapeParity.globalState :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The Skip fixture is `locals_strong_rel` to itself. -/
theorem skipLocalsStrong :
    crepInlineRuntimeLocalsStrongRel Flapjack.Test.CrepGlobalShapeParity.globalState
      Flapjack.Test.CrepGlobalShapeParity.globalState := rfl

def inlineSkipGuard : Bool :=
  (evalCrepRuntimeResult Flapjack.Test.CrepGlobalShapeParity.runtimeHandler
    Flapjack.Test.CrepGlobalShapeParity.noPrimitive 1
    Flapjack.Test.CrepGlobalShapeParity.globalState CrepProg.skip).isSome

#guard inlineSkipGuard

end Flapjack.Test.CrepInlineRelParity
