import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# `panSem$evaluate_decls` canonical finite-map parity

Direct original-HOL oracle rows for the canonical tagged finite-map evaluator
`PanSemStateFiniteExact.evaluateDeclsHOLFinite` (the Lean counterpart of HOL
`panSem$evaluate_decls_def`).  The oracle values are those recorded by
`scripts/hol-probes/pan_evaluate_decls_probe.out`, produced by running HOL
`panSem$evaluate_decls` on the concrete states in
`scripts/hol-probes/pan_evaluate_decls_probeScript.sml`.

The older `Flapjack/Test/PanSemEvaluateDeclsExactParity.lean` exercises the
unrestricted helper `evaluateDeclsHOLExact`; this module exercises the exact
tagged finite-map definition itself, as required for the
`fmap_as_finite_support` port.
-/

namespace Flapjack.Test.PanSemEvaluateDeclsFiniteParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL DeclHOL ProgHOL FunDeclHOL)
open Flapjack.PanSemStateFiniteExact

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

private abbrev emptyValues : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty

private abbrev emptyShapes : HolFiniteMapExact MlS ShapeHOL :=
  HolFiniteMapExact.empty

private abbrev emptyCode :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  HolFiniteMapExact.empty

abbrev state0 : PanSemStateFiniteExact 8 Unit :=
  { locals := emptyValues
    globals := emptyValues
    structs := []
    code := emptyCode
    eshapes := emptyShapes
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

abbrev stateLoad : PanSemStateFiniteExact 8 Unit :=
  { state0 with
    memory := fun a => if a = (0 : Word8) then .word 9 else .word 0
    memaddrs := fun a => a = 0 }

abbrev stateLoadByte : PanSemStateFiniteExact 8 Unit :=
  { state0 with
    memory := fun a => if a = (0 : Word8) then .word 1 else .word 0
    memaddrs := fun a => a = 0
    clock := 20
    be := false }

abbrev stateLocalX : PanSemStateFiniteExact 8 Unit :=
  { state0 with
    locals := emptyValues.update (ml "x", .val (.word 3)) }

abbrev stateOldFunction : PanSemStateFiniteExact 8 Unit :=
  { state0 with
    code := emptyCode.update (ml "f", ([], ProgHOL.skip, ShapeHOL.one)) }

abbrev stateExistingException : PanSemStateFiniteExact 8 Unit :=
  { state0 with
    eshapes := emptyShapes.update (ml "E", ShapeHOL.one) }

def functionDecl : FunDeclHOL 8 :=
  { name := ml "f"
    inline := false
    exported := false
    params := [(ml "x", ShapeHOL.one)]
    body := ProgHOL.skip
    returnShape := ShapeHOL.one }

def wordOfLocal (state : PanSemStateFiniteExact 8 Unit) (name : String) : Option Nat :=
  match state.locals.lookup (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def wordOfGlobal (state : PanSemStateFiniteExact 8 Unit) (name : String) : Option Nat :=
  match state.globals.lookup (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def eshapeIsOne (state : PanSemStateFiniteExact 8 Unit) (name : String) : Bool :=
  match state.eshapes.lookup (ml name) with
  | some ShapeHOL.one => true
  | _ => false

def codeIsExpected (state : PanSemStateFiniteExact 8 Unit) (name : String) : Bool :=
  match state.code.lookup (ml name) with
  | some (params, body, returnShape) =>
      (params.length == 1) &&
        (match params with
         | [(parameterName, parameterShape)] =>
             (parameterName == ml "x") &&
               (match parameterShape with | ShapeHOL.one => true | _ => false)
         | _ => false) &&
        (match body with | ProgHOL.skip => true | _ => false) &&
        (match returnShape with | ShapeHOL.one => true | _ => false)
  | none => false

/-- `evaluate_decls s [] = SOME s`. -/
def emptyGuard : Bool :=
  (evaluateDeclsHOLFinite state0 ([] : List (DeclHOL 8))).isSome

/-- Oracle `name_noop`: a `Name` declaration leaves the state unchanged. -/
def nameNoopGuard : Bool :=
  match evaluateDeclsHOLFinite state0 [DeclHOL.name (ml "S") []] with
  | some result =>
      (result.globals.lookup (ml "g")).isNone &&
        (result.locals.lookup (ml "x")).isNone &&
        (result.code.lookup (ml "f")).isNone && result.structs.isEmpty
  | none => false

/-- Oracle `decl_global_update`: `SOME (ValWord 7w), FEMPTY`. -/
def declGlobalUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite state0
      [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)] with
  | some result => wordOfGlobal result "g" == some 7 && (wordOfLocal result "x").isNone
  | none => false

/-- Oracle `decl_word_load_update`: `SOME (ValWord 9w)`. -/
def declWordLoadUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite stateLoad
      [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.load ShapeHOL.one (ExpHOL.const 0))] with
  | some result => wordOfGlobal result "g" == some 9
  | none => false

/-- Oracle `decl_byte_load_update`: `SOME (ValWord 1w), Word 1w`. -/
def declByteLoadUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite stateLoadByte
      [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.loadByte (ExpHOL.const 0))] with
  | some result => wordOfGlobal result "g" == some 1 && result.memory 0 == .word 1
  | none => false

/-- Oracle `decl_bad_load_shape`: the source load fails and the declaration is rejected. -/
def declBadLoadShapeGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.decl ShapeHOL.one (ml "g")
      (ExpHOL.load (ShapeHOL.named (ml "Missing")) (ExpHOL.const 0))]).isNone

/-- Oracle `decl_preserves_locals`: declaration evaluation leaves input locals unchanged. -/
def declPreservesLocalsGuard : Bool :=
  match evaluateDeclsHOLFinite stateLocalX
      [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)] with
  | some result => wordOfGlobal result "g" == some 7 && wordOfLocal result "x" == some 3
  | none => false

/-- Oracle `decl_left_to_right`: later declarations observe earlier global updates. -/
def declLeftToRightGuard : Bool :=
  match evaluateDeclsHOLFinite state0
      [ DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)
      , DeclHOL.decl ShapeHOL.one (ml "h") (ExpHOL.var .global (ml "g")) ] with
  | some result => wordOfGlobal result "g" == some 7 && wordOfGlobal result "h" == some 7
  | none => false

/-- Oracle `decl_empty_locals_failure`: expression evaluation uses empty locals. -/
def declEmptyLocalsFailureGuard : Bool :=
  (evaluateDeclsHOLFinite stateLocalX
    [DeclHOL.decl ShapeHOL.one (ml "g") (ExpHOL.var .local (ml "x"))]).isNone

/-- Oracle `decl_shape_failure`: mismatched declared shape fails. -/
def declShapeFailureGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.decl (ShapeHOL.named (ml "Missing")) (ml "g") (ExpHOL.const 7)]).isNone

/-- Oracle `function_code_update`: `SOME ([("x",One)],Skip,One)`. -/
def functionCodeUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite state0 [DeclHOL.function functionDecl] with
  | some result => codeIsExpected result "f"
  | none => false

/-- Oracle `function_code_replacement`: a function update replaces its prior code entry. -/
def functionCodeReplacementGuard : Bool :=
  match evaluateDeclsHOLFinite stateOldFunction [DeclHOL.function functionDecl] with
  | some result => codeIsExpected result "f"
  | none => false

/-- Oracle `function_bad_param_shape`: a bad parameter shape fails. -/
def functionBadParamShapeGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.function { functionDecl with
        params := [(ml "x", ShapeHOL.named (ml "Missing"))] }]).isNone

/-- Oracle `function_bad_return_shape`: an invalid return shape rejects the function. -/
def functionBadReturnShapeGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.function { functionDecl with
      returnShape := ShapeHOL.named (ml "Missing") }]).isNone

/-- Oracle `exn_shape_update`: `SOME One`. -/
def exnShapeUpdateGuard : Bool :=
  match evaluateDeclsHOLFinite state0 [DeclHOL.exnDecl (ml "E") ShapeHOL.one] with
  | some result => eshapeIsOne result "E"
  | none => false

/-- Oracle `exn_duplicate_failure`: an existing exception identifier is rejected. -/
def exnDuplicateFailureGuard : Bool :=
  (evaluateDeclsHOLFinite stateExistingException
    [DeclHOL.exnDecl (ml "E") ShapeHOL.one]).isNone

/-- Oracle `exn_bad_shape_failure`: a bad exception shape fails. -/
def exnBadShapeFailureGuard : Bool :=
  (evaluateDeclsHOLFinite state0
    [DeclHOL.exnDecl (ml "E") (ShapeHOL.named (ml "Missing"))]).isNone

def evaluateDeclsFiniteGuard : Bool :=
  emptyGuard && nameNoopGuard && declGlobalUpdateGuard && declWordLoadUpdateGuard &&
    declByteLoadUpdateGuard &&
    declBadLoadShapeGuard && declPreservesLocalsGuard && declLeftToRightGuard &&
    declEmptyLocalsFailureGuard && declShapeFailureGuard && functionCodeUpdateGuard &&
    functionCodeReplacementGuard && functionBadParamShapeGuard &&
    functionBadReturnShapeGuard && exnShapeUpdateGuard && exnDuplicateFailureGuard &&
    exnBadShapeFailureGuard

#eval emptyGuard
#eval nameNoopGuard
#eval declGlobalUpdateGuard
#eval declWordLoadUpdateGuard
#eval declByteLoadUpdateGuard
#eval declPreservesLocalsGuard
#eval declLeftToRightGuard
#eval functionCodeUpdateGuard
#eval exnShapeUpdateGuard

#guard emptyGuard
#guard nameNoopGuard
#guard declGlobalUpdateGuard
#guard declWordLoadUpdateGuard
#guard declByteLoadUpdateGuard
#guard declBadLoadShapeGuard
#guard declPreservesLocalsGuard
#guard declLeftToRightGuard
#guard declEmptyLocalsFailureGuard
#guard declShapeFailureGuard
#guard functionCodeUpdateGuard
#guard functionCodeReplacementGuard
#guard functionBadParamShapeGuard
#guard functionBadReturnShapeGuard
#guard exnShapeUpdateGuard
#guard exnDuplicateFailureGuard
#guard exnBadShapeFailureGuard
#guard evaluateDeclsFiniteGuard

def runChecks : IO Bool := do
  if evaluateDeclsFiniteGuard then
    IO.println "PASS canonical finite panSem evaluate_decls matches HOL oracle rows"
    pure true
  else
    IO.println "FAIL canonical finite panSem evaluate_decls matches HOL oracle rows"
    pure false

end Flapjack.Test.PanSemEvaluateDeclsFiniteParity
