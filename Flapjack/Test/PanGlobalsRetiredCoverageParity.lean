module

public import Flapjack.Pancake.PanGlobals
public import Flapjack.Pancake.PanGlobals.CompileExpExact
public import Flapjack.Pancake.PanGlobals.CompileTopExact
public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Pancake.Proofs.PanGlobals.DeclListLemmas
public import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
public import Flapjack.Pancake.Proofs.PanGlobals.FpermCode
public import Flapjack.Pancake.Proofs.PanToWord

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.PanGlobals
public meta import Flapjack.Pancake.PanGlobals.CompileExpExact
public meta import Flapjack.Pancake.PanGlobals.CompileTopExact
@[expose] public section

namespace Flapjack.Test.PanGlobalsRetiredCoverageParity

/-! Exact-twin replays for the checks retired with the Cake-carrier PanGlobals
layer (`30edc39ea1`) and the generic-α `dec_shapes`/`new_main_name` forms
(`24af969375`).  Every entry replays a probe row or an HOL theorem observation
that lost its test when those production forms were deleted; the coverage table
is recorded in the commit message. -/

open Flapjack
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)
open Flapjack.Pancake.PanLang
open Flapjack.PanGlobalsDeclListExact
open Flapjack.PanGlobalsCompileDecsStructural

/-! ## `pan_globals_fresh_name_probe.out` rows on the tagged exact twins

The five rows were previously replayed only through the production
`globalFreshName`.  Both tagged ports (`freshNameHOL` on `String` and
`freshNameMlS` on the exact `MlS` carrier) are replayed here. -/
def freshNameRows : Bool :=
  freshNameHOL "x" [] == "x" &&
  freshNameHOL "x" ["x"] == "x'" &&
  freshNameHOL "x" ["x", "x'", "x''"] == "x'''" &&
  freshNameHOL "x'" ["x'", "x''"] == "x'''" &&
  freshNameHOL "main" ["worker", "helper"] == "main" &&
  toStringOfBytes (freshNameMlS (ofString "x") []) == "x" &&
  toStringOfBytes (freshNameMlS (ofString "x") [ofString "x"]) == "x'" &&
  toStringOfBytes
      (freshNameMlS (ofString "x")
        [ofString "x", ofString "x'", ofString "x''"]) == "x'''" &&
  toStringOfBytes
      (freshNameMlS (ofString "x'") [ofString "x'", ofString "x''"]) == "x'''" &&
  toStringOfBytes
      (freshNameMlS (ofString "main") [ofString "worker", ofString "helper"]) == "main"

#eval freshNameRows
#guard freshNameRows

/-! Byte-rangedness observations that the retired
`PanGlobalsNameByteRangedParity` guarded. -/
def byteRangedBool (s : String) : Bool :=
  s.toList.all (fun c => decide (c.toNat < 256))

def functionDecl {width : Nat} [NeZero width] (name : MlS) : DeclHOL width :=
  .function
    { name := name
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def byteRangedRows : Bool :=
  byteRangedBool (freshNameHOL "x" ["x", "x'", "x''"]) &&
  byteRangedBool (freshNameHOL "x'" ["x'", "x''"]) &&
  byteRangedBool (toStringOfBytes (freshNameMlS (ofString "x") [ofString "x"])) &&
  byteRangedBool (toStringOfBytes
    (newMainNameHOL (width := 64)
      [functionDecl (width := 64) (ofString "main"),
       functionDecl (width := 64) (ofString "main'")])) &&
  byteRangedBool (toStringOfBytes
    (newMainNameHOL (width := 64) [functionDecl (width := 64) (ofString "worker")]))

#eval byteRangedRows
#guard byteRangedRows

example : Flapjack.Pancake.PanLang.NameRanged
    (freshNameHOL "x" ["x", "x'", "x''"]) :=
  holMlStringWitness_freshNameHOL "x" ["x", "x'", "x''"] (by
    unfold Flapjack.Pancake.PanLang.NameRanged
    decide)

example : Flapjack.Pancake.PanLang.NameRanged
    (globalFreshName "x" ["x", "x'", "x''"]) :=
  holMlStringWitness_globalFreshName "x" (by
    unfold Flapjack.Pancake.PanLang.NameRanged
    decide) ["x", "x'", "x''"]

example {width : Nat} {function : String}
    {configuration configurationLength array arrayLength : Flapjack.Exp (BitVec width)}
    (h : Flapjack.Pancake.PanLang.ProgByteRanged
      (Flapjack.Prog.extCall function configuration configurationLength array arrayLength :
        Flapjack.Prog (BitVec width))) :
    Flapjack.Pancake.PanLang.NameRanged function :=
  Flapjack.Pancake.PanLang.progByteRanged_extCall_name h

example {width : Nat} {fd : Flapjack.FunDecl (BitVec width)}
    (h : Flapjack.Pancake.PanLang.DeclByteRanged (Flapjack.Decl.function fd)) :
    Flapjack.Pancake.PanLang.NameRanged fd.name :=
  Flapjack.Pancake.PanLang.declByteRanged_function_name h

/-! ## Remaining `pan_globals_compile_decs_probe.out` rows

The probe also captured direct `compile_exp`/`compile` rows under two contexts
and one handled-Global full-program row; those were replayed through the
production `globalCompileDecs` forms and now run on the exact twins. -/
def baseContext : PanGlobalsContextExact 8 :=
  { globals := HolFiniteMapExact.empty
    globalsSize := 1
    maxGlobalsSize := 16 }

def contextWithGlobal : PanGlobalsContextExact 8 :=
  { globals :=
      (HolFiniteMapExact.empty.update
        ((ofString "g"), (.one, 7))).update ((ofString "r"), (.one, 7))
    globalsSize := 1
    maxGlobalsSize := 16 }

def nameIs (name : MlS) (expected : String) : Bool :=
  toStringOfBytes name == expected

def compileExpRows : Bool :=
  (match compileExpExactHOL baseContext (.topAddr : ExpHOL 8) with
   | .op .sub [.topAddr, .const address] => address == (16 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL baseContext (.var .global (ofString "g") : ExpHOL 8) with
   | .const value => value == (0 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL contextWithGlobal
      (.var .global (ofString "g") : ExpHOL 8) with
   | .load .one (.op .sub [.topAddr, .const address]) => address == (7 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL baseContext (.nstruct (ofString "S") [] : ExpHOL 8) with
   | .const value => value == (0 : BitVec 8)
   | _ => false)

def compileAssignRows : Bool :=
  (match compileProgExactHOL contextWithGlobal
      (.assign .global (ofString "g") (.const 5) : ProgHOL 8) with
   | .store (.op .sub [.topAddr, .const address]) (.const value) =>
       address == (7 : BitVec 8) && value == (5 : BitVec 8)
   | _ => false) &&
  (match compileProgExactHOL baseContext
      (.assign .global (ofString "g") (.const 5) : ProgHOL 8) with
   | .skip => true
   | _ => false)

def handledHandler : ProgHOL 8 :=
  .seq (.assign .local (ofString "x") (.const 1))
    (.assign .local (ofString "vn'") (.const 2))

def handledCall : ProgHOL 8 :=
  .call
    (some ((some ((VarKind.global, ofString "r"))),
      some (ofString "e", ofString "ev", handledHandler)))
    (ofString "f") [.var .global (ofString "g")]

def handlerBodyMatches (body : ProgHOL 8) : Bool :=
  match body with
  | .seq (.seq (.assign .local firstName (.const first))
          (.assign .local secondName (.const second)))
      (.assign .local flagName (.const flag)) =>
      nameIs firstName "x" && first == (1 : BitVec 8) &&
      nameIs secondName "vn'" && second == (2 : BitVec 8) &&
      nameIs flagName "vn''" && flag == (1 : BitVec 8)
  | _ => false

def handledRowGuard : Bool :=
  match compileProgExactHOL contextWithGlobal handledCall with
  | .dec destination .one (.const destinationValue) rest =>
      nameIs destination "" && destinationValue == (0 : BitVec 8) &&
      (match rest with
       | .dec flag .one (.const flagValue) body =>
           nameIs flag "vn''" && flagValue == (0 : BitVec 8) &&
           (match body with
            | .seq (.call info callName args) (.ite cond .skip handler) =>
                nameIs callName "f" &&
                (match info with
                 | some (destinationOpt, handlerOpt) =>
                     (match destinationOpt with
                      | some (kind, destination') =>
                          (match kind with | .local => true | _ => false) &&
                          nameIs destination' ""
                      | none => false) &&
                     (match handlerOpt with
                      | some (exception, valueName, handlerBody) =>
                          nameIs exception "e" && nameIs valueName "ev" &&
                          handlerBodyMatches handlerBody
                      | none => false)
                 | none => false) &&
                (match args with
                 | [.load .one (.op .sub [.topAddr, .const address])] =>
                     address == (7 : BitVec 8)
                 | _ => false) &&
                (match cond with
                 | .var .local name => nameIs name "vn''"
                 | _ => false) &&
                (match handler with
                 | .store (.op .sub [.topAddr, .const address])
                     (.var .local name) =>
                     address == (7 : BitVec 8) && nameIs name ""
                 | _ => false)
            | _ => false)
       | _ => false)
  | _ => false

/-! ## Remaining `pan_globals_compile_top_probe.out` rows

`missing_start`, `present_start` and `global_present` were replayed through the
deleted Cake top wrappers only; they now run on `compileTopExactHOL` at 64 bits
with the probe's own fixtures. -/
def originalMain : DeclHOL 64 :=
  .function
    { name := ofString "main"
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def missingStartRowGuard : Bool :=
  match compileTopExactHOL [originalMain] (ofString "absent") with
  | [] => true
  | _ => false

def mainEntryMatches (entry : DeclHOL 64) (expectedBody : ProgHOL 64) : Bool :=
  match entry with
  | .function fi =>
      nameIs fi.name "main" && !fi.inline && !fi.exported && fi.params.isEmpty &&
      (match fi.returnShape with | .one => true | _ => false) &&
      (match fi.body, expectedBody with
       | .seq .skip (.call none target []), .seq .skip (.call none expected []) =>
           nameIs target "main'" && nameIs expected "main'"
       | .seq (.seq (.store (.op .sub [.topAddr, .const address]) (.const value))
              .skip) (.call none target []),
         .seq (.seq (.store (.op .sub [.topAddr, .const expectedAddress])
              (.const expectedValue)) .skip) (.call none expected []) =>
           address == expectedAddress && value == expectedValue &&
           nameIs target "main'" && nameIs expected "main'"
       | _, _ => false)
  | _ => false

def renamedEntryMatches (entry : DeclHOL 64) : Bool :=
  match entry with
  | .function fi =>
      nameIs fi.name "main'" && !fi.inline && !fi.exported && fi.params.isEmpty &&
      (match fi.returnShape with | .one => true | _ => false) &&
      (match fi.body with | .skip => true | _ => false)
  | _ => false

def presentStartRowGuard : Bool :=
  let expected : ProgHOL 64 := .seq .skip (.call none (ofString "main'") [])
  match compileTopExactHOL [originalMain] (ofString "main") with
  | [entry, renamed] => mainEntryMatches entry expected && renamedEntryMatches renamed
  | _ => false

def globalPresentRowGuard : Bool :=
  let expected : ProgHOL 64 :=
    .seq (.seq (.store (.op .sub [.topAddr, .const 8]) (.const 7)) .skip)
      (.call none (ofString "main'") [])
  match compileTopExactHOL
      [.decl .one (ofString "g") (.const 7), originalMain] (ofString "main") with
  | [entry, renamed] => mainEntryMatches entry expected && renamedEntryMatches renamed
  | _ => false

def compileDecsExtraRows : Bool :=
  compileExpRows && compileAssignRows && handledRowGuard &&
    missingStartRowGuard && presentStartRowGuard && globalPresentRowGuard

#eval compileDecsExtraRows
#guard compileDecsExtraRows

/-! ## `dec_shapes` cluster rows on the tagged `decShapesHOL`

The retired `PanGlobalsDecShapesParity.clusterGuard` observed the
`pan_globalsProofScript.sml:2328-2361` cluster through the production
`globalDeclShapes`/`globalDeclsFilter`/`globalResortDecls` forms, and the
retired `PanGlobalsDecShapesClusterParity.decShapesClusterGuard` observed the
same compositions plus the `globalRenameDecls` row and a function-only
fixture.  Every one of those observations is replayed here on the exact twin,
with the production filters replaced by their exact-carrier predicates and
`globalRenameDecls` by `fpermDecsHOL`. -/
def clusterDecls : List (DeclHOL 64) :=
  [functionDecl (width := 64) (ofString "f"),
   .decl (.comb [.one, .named (ofString "S")]) (ofString "g") (.const 7),
   .name (ofString "S") [], .exnDecl (ofString "E") (.named (ofString "T")),
   .decl .one (ofString "h") (.const 9)]

def clusterFunctionOnly : List (DeclHOL 64) :=
  [functionDecl (width := 64) (ofString "f"),
   functionDecl (width := 64) (ofString "g")]

example : decShapesHOL (width := 64)
    (clusterDecls ++ [.decl .one (ofString "k") (.const 11)]) =
    [.comb [.one, .named (ofString "S")], .one, .one] := rfl

example : decShapesHOL (width := 64) clusterFunctionOnly = [] := rfl

example : decShapesHOL (width := 64)
    (clusterDecls.filter (fun declaration => !isFunctionHOL declaration)) =
    [.comb [.one, .named (ofString "S")], .one] := rfl

example : decShapesHOL (width := 64) (clusterDecls.filter isFunctionHOL) = [] := rfl

example : decShapesHOL (width := 64) (clusterDecls.filter isNameHOL) = [] := rfl

example : decShapesHOL (width := 64) (clusterDecls.filter isExnDeclHOL) = [] := rfl

example : decShapesHOL (width := 64) (clusterDecls.filter isDeclHOL) =
    [.comb [.one, .named (ofString "S")], .one] := rfl

example : decShapesHOL (width := 64) (resortDeclsHOL clusterDecls) =
    [.comb [.one, .named (ofString "S")], .one] := rfl

example : decShapesHOL (width := 64)
    (fpermDecsHOL (ofString "foo") (ofString "bar") clusterDecls) =
    [.comb [.one, .named (ofString "S")], .one] := by
  rw [dec_shapes_fperm_decsHOL]
  rfl


/-! ## Exact-twin theorem replays for the retired `dec_shapes`/`new_main_name`
observations

`PanGlobalsDecShapesParity` applied fifteen production-carrier theorems and
`PanGlobalsNewMainNameParity`/`PanGlobalsNameCorrectnessParity` applied
`new_main_name_correct`; those applications were the only test-side kernel
checks of the HOL results.  Each tagged exact twin is applied here at width 64
on `DeclHOL`/`ProgHOL`/`PanGlobalsContextExact` carriers. -/

example (code : List (DeclHOL 64)) :
    functionsHOL (resortDeclsHOL code) = functionsHOL code :=
  resort_decls_preserve_functionsHOL code

example (code : List (DeclHOL 64)) (ctxt : PanGlobalsContextExact 64) :
    ∀ (decs : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
      (ctxt' : PanGlobalsContextExact 64),
      compileDecsExactHOL ctxt code = (decs, funs, exns, ctxt') →
      (functionsHOL funs).map Prod.fst = (functionsHOL code).map Prod.fst :=
  fun decs funs exns ctxt' h =>
    compile_decs_preserve_functionsHOL code ctxt decs funs exns ctxt' h

example (ctxt : PanGlobalsContextExact 64) (code : List (DeclHOL 64)) :
    ∀ (decs : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
      (ctxt' : PanGlobalsContextExact 64),
      compileDecsExactHOL ctxt code = (decs, funs, exns, ctxt') →
      ∀ d ∈ funs, isFunctionHOL d = true :=
  fun decs funs exns ctxt' h =>
    compile_decs_EVERY_is_functionHOL ctxt code decs funs exns ctxt' h

example (ctxt : PanGlobalsContextExact 64) (code : List (DeclHOL 64)) :
    ∀ (decs : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
      (ctxt' : PanGlobalsContextExact 64),
      compileDecsExactHOL ctxt code = (decs, funs, exns, ctxt') ∧
        (∀ d ∈ code, ¬ isFunctionHOL d = true) →
      funs = [] :=
  fun decs funs exns ctxt' h =>
    compile_decs_decls_thmHOL ctxt code decs funs exns ctxt' h

example (ctxt : PanGlobalsContextExact 64) (code : List (DeclHOL 64)) :
    ∀ (decs : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
      (ctxt' : PanGlobalsContextExact 64),
      compileDecsExactHOL ctxt code = (decs, funs, exns, ctxt') →
      exns = code.filter isExnDeclHOL :=
  fun decs funs exns ctxt' h =>
    compile_decs_exns_are_exnsHOL ctxt code decs funs exns ctxt' h

example (ctxt : PanGlobalsContextExact 64) (code : List (DeclHOL 64)) :
    ∀ (decs : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
      (ctxt' : PanGlobalsContextExact 64),
      compileDecsExactHOL ctxt code = (decs, funs, exns, ctxt') →
      compileDecsExactHOL ctxt (code.filter isDeclHOL) = (decs, [], [], ctxt') :=
  fun decs funs exns ctxt' h =>
    compile_decs_FILTER_declsHOL ctxt code decs funs exns ctxt' h

example (P : DeclHOL 64 → Prop) (ctxt : PanGlobalsContextExact 64)
    (code : List (DeclHOL 64)) :
    ∀ (decs : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
      (ctxt' : PanGlobalsContextExact 64),
      compileDecsExactHOL ctxt code = (decs, funs, exns, ctxt') ∧
        (∀ d ∈ code, ∀ (fi : FunDeclHOL 64) (c : PanGlobalsContextExact 64),
          d = .function fi →
            P (.function { fi with body := compileProgExactHOL c fi.body })) →
      ∀ d ∈ funs, P d :=
  fun decs funs exns ctxt' h =>
    compile_decs_EVERYHOL P ctxt code decs funs exns ctxt' h

example := compile_decs_functions_thmHOL (width := 64)

example (f g : MlS) (xs ys : List (DeclHOL 64)) :
    fpermDecsHOL f g (xs ++ ys) = fpermDecsHOL f g xs ++ fpermDecsHOL f g ys :=
  fpermDecsHOL_append f g xs ys

example (x y : MlS) (code : List (DeclHOL 64)) :
    functionsHOL (fpermDecsHOL x y code) =
      (functionsHOL code).map (fun entry =>
        (fpermName x y entry.1, entry.2.1,
          fpermHOL x y entry.2.2.1, entry.2.2.2)) :=
  functionsFpermDecsHOL x y code

example (f g : MlS) (xs : List (DeclHOL 64)) :
    (∀ d ∈ xs, (!isFunctionHOL d) = true) → fpermDecsHOL f g xs = xs :=
  fperm_decs_declsHOL f g xs ()

example (f g : MlS) (decs : List (DeclHOL 64)) :
    fpermDecsHOL f g (decs.filter isFunctionHOL) =
      (fpermDecsHOL f g decs).filter isFunctionHOL :=
  fperm_decs_FILTER_is_functionHOL f g decs

example (x y : MlS) (code : List (DeclHOL 64)) :
    ((functionsHOL code).map Prod.fst).Nodup →
      ((functionsHOL (fpermDecsHOL x y code)).map Prod.fst).Nodup :=
  ALL_DISTINCT_fperm_decsHOL x y code

example (f g : MlS) (decs : List (DeclHOL 64)) :
    (∀ d ∈ decs, isFunctionHOL d = false → True) →
    (∀ d ∈ decs, ∀ fi : FunDeclHOL 64, d = .function fi → True) →
    ∀ d ∈ fpermDecsHOL f g decs, True :=
  EVERY_fperm_decsHOL f g (fun _ => True) decs

example (f g : MlS) (code : List (DeclHOL 64)) :
    (fpermDecsHOL f g code).filter (fun d => !isFunctionHOL d) =
      code.filter (fun d => !isFunctionHOL d) :=
  FILTER_decs_fperm_decsHOL f g code

example (code : List (DeclHOL 64)) :
    newMainNameHOL code ∈ (functionsHOL code).map Prod.fst → False :=
  new_main_name_correctHOL code

example (name : MlS) (names : List MlS) :
    freshNameMlS name names ∈ names → False :=
  freshNameMlS_correct name names

example (ds ds' : List (DeclHOL 64)) :
    exceptionsHOL (ds ++ ds') = exceptionsHOL ds ++ exceptionsHOL ds' :=
  exceptions_appendHOL ds ds'

example (decs : List (DeclHOL 64)) :
    exceptionsHOL (decs.filter isFunctionHOL) = [] ∧
      exceptionsHOL (decs.filter (fun d => !isFunctionHOL d)) = exceptionsHOL decs ∧
      exceptionsHOL (decs.filter isExnDeclHOL) = exceptionsHOL decs ∧
      exceptionsHOL (decs.filter isNameHOL) = [] ∧
      exceptionsHOL (decs.filter isDeclHOL) = [] :=
  exceptions_FILTER_is_functionHOL decs

example (x : DeclHOL 64) :
    (isNameHOL x = true → ¬ isFunctionHOL x = true) ∧
      (isDeclHOL x = true → ¬ isFunctionHOL x = true) ∧
      (isExnDeclHOL x = true → ¬ isFunctionHOL x = true) :=
  not_is_functionHOL x

example (x : DeclHOL 64) :
    ((isDeclHOL x = true ∧ isNameHOL x = true) ↔ False) ∧
      ((isDeclHOL x = true ∧ isFunctionHOL x = true) ↔ False) ∧
      ((isDeclHOL x = true ∧ isExnDeclHOL x = true) ↔ False) :=
  decl_distinctHOL x

example (decls : List (DeclHOL 64)) :
    functionsHOL (decls.filter (fun d => !isFunctionHOL d)) = [] :=
  functions_filter_nilHOL decls

example (pan_code : List (DeclHOL 64)) :
    decShapesHOL (panSimpDeclsHOL pan_code) = decShapesHOL pan_code :=
  decShapesCompileProgHOL pan_code

example (pan_code : List (DeclHOL 64)) :
    (functionsHOL (panSimpDeclsHOL pan_code)).map Prod.fst =
      (functionsHOL pan_code).map Prod.fst :=
  functionNamesCompileProgHOL pan_code

/-! The three `pan_to_word` observations retired with the same test also run on
their exact twins. -/
example (pan_code : List (DeclHOL 64)) :
    (∀ d ∈ pan_code,
        isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) →
      ∀ d ∈ panSimpDeclsHOL pan_code,
        isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true :=
  noNamesCompileProgHOL pan_code

example (prog : List (DeclHOL 64)) :
    sizeOfEidsHOL (Pancake.PanStructs.CompileShapeExact.compileTopExact prog) =
      sizeOfEidsHOL prog :=
  sizeOfEidsStructsCompileEqHOL prog

example (pan_code : List (DeclHOL 64)) (main : MlS)
    (args : List (MlS × ShapeHOL)) (body : ProgHOL 64) (rshape : ShapeHOL) :
    List.lookup main (functionsHOL pan_code) = some (args, body, rshape) →
      sizeOfEidsHOL (compileTopExactHOL pan_code main) = sizeOfEidsHOL pan_code :=
  sizeOfEidsCompileTopHOL pan_code main args body rshape

example (ctxt : PanGlobalsContextExact 64) (prog : List (DeclHOL 64)) :
    functionsHOL (compileDecsExactHOL ctxt prog).2.2.1 = [] :=
  functionsCompileDecsExnsHOL ctxt prog

def runChecks : IO Bool := do
  if freshNameRows && byteRangedRows && compileDecsExtraRows then
    IO.println "PASS pan_globals retired-check exact-twin coverage"
    pure true
  else
    IO.println "FAIL pan_globals retired-check exact-twin coverage"
    pure false
end Flapjack.Test.PanGlobalsRetiredCoverageParity
