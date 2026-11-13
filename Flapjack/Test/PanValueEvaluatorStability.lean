module

public import Flapjack.PanValueEvaluatorStability
public import Flapjack.Pancake.Proofs.PanToCrep.EvalDistinctLists

-- Checks below run compiled code from these modules.
public meta import Flapjack.PanValueEvaluatorStability
public meta import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
@[expose] public section

namespace Flapjack.Test.PanValueEvaluatorStability

open Flapjack

/-! A concrete instance of Cake's `eval_distinct_lists_not_affect'` helper:
    installing a fresh local binding does not change an expression that does
    not mention that local.  The expected value is checked independently by
    reducing the original evaluator. -/

def expression : Exp Nat := .op .add [.const 1, .const 2]

def baseLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 7) else none

theorem fresh_local_stability_fixture :
    evalPanValueExp ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 expression none = some (.word 3) := by
  calc
    evalPanValueExp ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 expression none =
        evalPanValueExp ([] : StructContext) baseLocals (fun _ => none)
          (fun _ => none) 0 0 8 expression none := by
            exact evalPanValueExp_update_local_not_mem ([] : StructContext)
              baseLocals (fun _ => none) (fun _ => none) 0 0 8 expression none
              "fresh" (.word 99) (by
                simp [expression, expLocalVars, expLocalVars.expLocalVarsList])
    _ = some (.word 3) := by
      simp [expression, evalPanValueExp, evalPanValueExp.evalPanValueExps,
        evalPanBinOp]

def fields : List (FieldName × Exp Nat) :=
  [("left", .op .add [.const 1, .const 2]), ("right", .const 4)]

def namedStructs : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

theorem fresh_field_list_stability_fixture :
    evalPanValueExp.evalPanValueFields ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 fields none =
      some [("left", .word 3), ("right", .word 4)] := by
  calc
    evalPanValueExp.evalPanValueFields ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 fields none =
        evalPanValueExp.evalPanValueFields ([] : StructContext) baseLocals
          (fun _ => none) (fun _ => none) 0 0 8 fields none := by
            exact evalPanValueFields_update_local_not_mem ([] : StructContext)
              baseLocals (fun _ => none) (fun _ => none) 0 0 8 fields none
              "fresh" (.word 99) (by
                intro field hfield
                simp [fields] at hfield
                rcases hfield with rfl | rfl <;>
                  simp [expLocalVars, expLocalVars.expLocalVarsList])
    _ = some [("left", .word 3), ("right", .word 4)] := by
      simp [fields, evalPanValueExp, evalPanValueExp.evalPanValueFields,
        evalPanValueExp.evalPanValueExps, evalPanBinOp]

theorem fresh_named_struct_stability_fixture :
    evalPanValueExp namedStructs
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 (.nStruct "Pair" fields) none =
      evalPanValueExp namedStructs baseLocals (fun _ => none) (fun _ => none)
        0 0 8 (.nStruct "Pair" fields) none := by
  exact evalPanValueExp_nStruct_update_local_not_mem namedStructs baseLocals
    (fun _ => none) (fun _ => none) 0 0 8 "Pair" fields none "fresh"
    (.word 99) (by
      intro field hfield
      simp [fields] at hfield
      rcases hfield with rfl | rfl <;>
        simp [expLocalVars, expLocalVars.expLocalVarsList])

def freshBindings : List (VarName × PanValue Nat) :=
  [("fresh-left", .word 99), ("fresh-right", .word 101)]

def expressions : List (Exp Nat) :=
  [.op .add [.const 1, .const 2], .panOp .mul [.const 3, .const 4]]

theorem fresh_bindings_stability_fixture :
    evalPanValueExps ([] : StructContext)
        (updatePanValueMapList baseLocals freshBindings) (fun _ => none)
        (fun _ => none) 0 0 8 expressions none =
      some [.word 3, .word 12] := by
  simp [freshBindings, updatePanValueMapList, updatePanValueMap,
    expressions, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    evalPanValueExp, evalPanBinOp, evalPanOp]

def resultGuard : Bool := match evalPanValueExp ([] : StructContext)
    (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
    (fun _ => none) 0 0 8 expression none with
  | some (.word 3) => true
  | _ => false

#eval resultGuard
#guard resultGuard

/-! ## Exact-carrier fresh-binding fixtures

The production-carrier helpers retired above are replaced by the tagged exact
twins `evalDistinctListsNotAffectHOL` and `optMmapEvalDistinctListsNotAffectHOL`
in `Flapjack/Pancake/Proofs/PanToCrep/EvalDistinctLists.lean`. The fixtures
below are kernel checks over the reviewed exact `CrepSemHOLState` carrier:
installing fresh locals through `locals.updateListEq (vs.zip nvals)` leaves a
constant expression's value unchanged. -/

def word8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

def fixtureFfi : HolFfiState Unit where
  oracle := fun _ state _ _ => .ret state []
  ffiState := ()
  ioEvents := []

/-- Width-8 exact-carrier state with empty locals/globals/code maps and empty
    memory domains, so each fixture is independent of the environment. -/
def exactState : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => HolWordLab.word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := fixtureFfi
  baseAddr := word8 0
  topAddr := word8 100

local instance : DecidablePred exactState.memaddrs :=
  fun _ => isFalse (by simp [exactState])

/-- Fresh local numbers installed by the fixtures. -/
def freshVars : List Nat := [3]

/-- Fresh local values installed by the fixtures. -/
def freshVals : List (HolWordLab 8) := [HolWordLab.word (word8 99)]

/-- The constant expression whose value the fixtures observe. -/
def exactExpression : CrepExpHOL 8 := .const (word8 5)

/-- Two constant expressions for the `OPT_MMAP` fixture. -/
def exactExpressions : List (CrepExpHOL 8) :=
  [.const (word8 5), .const (word8 6)]

/-- Kernel check on the tagged exact `eval_distinct_lists_not_affect` twin:
    the fresh-binding installation does not change the constant's value. -/
example :
    evalCrepSemHOLExp
        { exactState with
          locals := exactState.locals.updateListEq (freshVars.zip freshVals) }
        exactExpression = some (HolWordLab.word (word8 5)) := by
  classical
  rw [evalDistinctListsNotAffectHOL freshVars exactState exactExpression
    (HolWordLab.word 0) freshVals ⟨rfl, by decide⟩]
  simp [evalCrepSemHOLExp, exactExpression]

/-- Kernel check on the tagged exact `opt_mmap_eval_distinct_lists_not_affect`
    twin: the `OPT_MMAP` of the two constants keeps its expected values. -/
example :
    exactExpressions.mapM
        (evalCrepSemHOLExp
          { exactState with
            locals := exactState.locals.updateListEq (freshVars.zip freshVals) }) =
      some [HolWordLab.word (word8 5), HolWordLab.word (word8 6)] := by
  classical
  rw [optMmapEvalDistinctListsNotAffectHOL exactExpressions exactState
    [HolWordLab.word (word8 5), HolWordLab.word (word8 6)] freshVars freshVals
    ⟨by simp [evalCrepSemHOLExp, exactExpressions], rfl, by decide⟩]

end Flapjack.Test.PanValueEvaluatorStability
