module

public import Flapjack.Pancake.PanToCrep.Compile
public import Flapjack.Pancake.PanToCrep.CompileExact
public import Flapjack.Pancake.CrepToLoop
public import Flapjack.Pancake.LoopToWord
public import Flapjack.RiscV.WordToStack
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.Pancake.PanToCrep.CompileExact

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.Test.CompileToCrepeParity

open Flapjack
open Flapjack.Pancake.PanLang (DeclHOL FunDeclHOL MlS ShapeHOL ExpHOL ProgHOL functionsHOL)

private abbrev holMl (name : String) : MlS := Flapjack.Basis.Pure.MlString.ofString name

/-! Exact `duplicate_function_names` row from the direct HOL probe.  Both
same-name declarations remain in the returned list in source order, while the
call compiled for `g` uses the first `f` return shape and allocates two words. -/
private def exactDuplicateFunctionNameDecls : List (DeclHOL 8) :=
  [ .function
      { name := holMl "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .comb [.one, .one] }
  , .function
      { name := holMl "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one }
  , .function
      { name := holMl "g", inline := false, exported := false, params := [],
        body := .call (some (none, none)) (holMl "f") [], returnShape := .one }
  ]

private def exactDuplicateFunctionNameOracle : Bool :=
  match Flapjack.compileToCrepExactHOLW exactDuplicateFunctionNameDecls with
  | [ (first, [], .skip), (second, [], .skip),
      (caller, [], .dec 1 (.const zero1)
        (.dec 2 (.const zero2)
          (.call (some ([1, 2], none)) called []))) ] =>
      first == holMl "f" && second == holMl "f" && caller == holMl "g" &&
        called == holMl "f" && zero1 == (0 : BitVec 8) && zero2 == (0 : BitVec 8)
  | _ => false

#guard exactDuplicateFunctionNameOracle

private def exactRaiseConstDecls : List (DeclHOL 8) :=
  [ .exnDecl (holMl "E") ShapeHOL.one
  , .function
      { name := holMl "f", inline := false, exported := false,
        params := [(holMl "x", ShapeHOL.one)],
        body := .raise (holMl "E") (.const 7), returnShape := ShapeHOL.one }
  ]

private def exactRaiseConstOracle : Bool :=
  match Flapjack.compileToCrepExactHOLW exactRaiseConstDecls with
  | [(name, [0], .seq
       (.dec 1 (.const seven) (.seq (.storeGlob address (.var 1)) .skip))
       (.raise exceptionCode))] =>
      name == holMl "f" && seven == (7 : BitVec 8) &&
        address == (0 : BitVec 5) && exceptionCode == (0 : BitVec 8)
  | _ => false

#guard exactRaiseConstOracle

/-! Direct `raise_const` result from `compile_to_crep_probe.out`, now checked
at the exact HOL declaration-only boundary over a 64-bit word. The exception
declaration determines code zero internally; no compiler context is supplied. -/
def exactDeclarationOnlyProbe : List (DeclHOL 64) :=
  [.exnDecl (holMl "E") .one,
   .function
     { name := holMl "f", inline := false, exported := false,
       params := [(holMl "x", .one)],
       body := .raise (holMl "E") (.const 7), returnShape := .one }]

def exactDeclarationOnlyOracle : Bool :=
  match compileToCrepExactHOLW exactDeclarationOnlyProbe with
  | [(name, [0],
      .seq (.dec 1 (.const seven)
        (.seq (.storeGlob address (.var 1)) .skip))
        (.raise code))] =>
      name == holMl "f" && seven == (7 : BitVec 64) &&
        address == (0 : BitVec 5) && code == (0 : BitVec 64)
  | _ => false

#guard exactDeclarationOnlyOracle

/-! These declaration-only fixtures replay the `raise_pair` and
`handled_pair` rows from the direct HOL `compile_to_crep_probe.out` at its
concrete 8-bit word instantiation. They exercise the tagged exact
`compileToCrepExactHOLW` path; the retired production-carrier mirror was
`compileToCrepHOL`. -/
def exactPairRaiseProbe : List (DeclHOL 8) :=
  [.exnDecl (holMl "E") (.comb [.one, .one]),
   .function
     { name := holMl "f", inline := false, exported := false, params := [],
       body := .raise (holMl "E") (.rstruct [.const 7, .const 9]),
       returnShape := .one }]

def exactPairRaiseOracle : Bool :=
  match compileToCrepExactHOLW exactPairRaiseProbe with
  | [(name, [], .seq
      (.dec 1 (.const seven)
        (.dec 2 (.const nine)
          (.seq (.storeGlob first (.var 1))
            (.seq (.storeGlob second (.var 2)) .skip))))
      (.raise code))] =>
      name == holMl "f" && seven == (7 : BitVec 8) && nine == (9 : BitVec 8) &&
        first == (0 : BitVec 5) && second == (1 : BitVec 5) &&
        code == (0 : BitVec 8)
  | _ => false

#guard exactPairRaiseOracle

def exactLaterPairRaiseProbe : List (DeclHOL 8) :=
  [.exnDecl (holMl "E") (.comb [.one, .one]),
   .function
     { name := holMl "f", inline := false, exported := false, params := [],
       body := .dec (holMl "a") .one (.const 3)
         (.dec (holMl "b") .one (.const 5)
           (.raise (holMl "E") (.rstruct [.const 7, .const 9]))),
       returnShape := .one }]

def exactLaterPairRaiseOracle : Bool :=
  match compileToCrepExactHOLW exactLaterPairRaiseProbe with
  | [(name, [],
      .dec 1 (.const three)
        (.dec 2 (.const five)
          (.seq
            (.dec 3 (.const seven)
              (.dec 4 (.const nine)
                (.seq
                  (.storeGlob first (.var 3))
                  (.seq (.storeGlob second (.var 4)) .skip))))
            (.raise code))))] =>
      name == holMl "f" && three == (3 : BitVec 8) && five == (5 : BitVec 8) &&
        seven == (7 : BitVec 8) && nine == (9 : BitVec 8) &&
        first == (0 : BitVec 5) && second == (1 : BitVec 5) &&
        code == (0 : BitVec 8)
  | _ => false

#guard exactLaterPairRaiseOracle

def exactHandledPairProbe : List (DeclHOL 8) :=
  [.exnDecl (holMl "E") (.comb [.one, .one]),
   .function
     { name := holMl "f", inline := false, exported := false, params := [],
       body := .raise (holMl "E") (.rstruct [.const 7, .const 9]),
       returnShape := .comb [.one, .one] },
   .function
     { name := holMl "g", inline := false, exported := false,
       params := [(holMl "pair", .comb [.one, .one])],
       body := .call
         (some (some (.local, holMl "pair"),
           some (holMl "E", holMl "pair", .skip))) (holMl "f") [],
       returnShape := .one }]

def exactHandledPairOracle : Bool :=
  match compileToCrepExactHOLW exactHandledPairProbe with
  | [(fname, [], .seq
        (.dec 1 (.const seven)
          (.dec 2 (.const nine)
            (.seq (.storeGlob first (.var 1))
              (.seq (.storeGlob second (.var 2)) .skip))))
        (.raise raiseCode)),
     (gname, [0, 1], .call
        (some ([0, 1], some (handlerCode,
          .seq
            (.seq (.assign 0 (.loadGlob loadFirst))
              (.seq (.assign 1 (.loadGlob loadSecond)) .skip))
            .skip))) callee [])] =>
      fname == holMl "f" && gname == holMl "g" && callee == holMl "f" &&
        seven == (7 : BitVec 8) && nine == (9 : BitVec 8) &&
        first == (0 : BitVec 5) && second == (1 : BitVec 5) &&
        raiseCode == (0 : BitVec 8) && handlerCode == (0 : BitVec 8) &&
        loadFirst == (0 : BitVec 5) && loadSecond == (1 : BitVec 5)
  | _ => false

#guard exactHandledPairOracle

/-! HOL `alist_to_fmap` is a right fold: the first repeated name wins even
though `compile_to_crep` still emits both function declarations in order. -/
def holDuplicateMapOracle : Bool :=
  let declarations : List (DeclHOL 64) :=
    [.exnDecl (holMl "E") .one, .exnDecl (holMl "E") .one,
     .function
       { name := holMl "f", inline := false, exported := false,
         params := [], body := .skip, returnShape := .one },
     .function
       { name := holMl "f", inline := false, exported := false,
         params := [(holMl "x", .one)], body := .skip,
         returnShape := .comb [.one, .one] }]
  (getEidsFromDeclsHOL declarations).lookup (holMl "E") ==
      some (0 : BitVec 64) &&
    (match (makeFuncsExactHOL (functionsHOL declarations)).lookup (holMl "f") with
     | some ([], .one) => true
     | _ => false) &&
    (compileToCrepExactHOLW declarations).length == 2

#guard holDuplicateMapOracle

/-! Exact `duplicate_exceptions` row from the direct HOL
`compile_to_crep_probe.out`: the first repeated `E` keeps code zero, `F`
keeps code one, and both compiled Raise bodies use those codes. -/
def exactDuplicateExceptionDecls : List (DeclHOL 8) :=
  [.exnDecl (holMl "E") .one, .exnDecl (holMl "F") .one,
   .exnDecl (holMl "E") .one,
   .function
     { name := holMl "f", inline := false, exported := false, params := [],
       body := .raise (holMl "E") (.const 7), returnShape := .one },
   .function
     { name := holMl "g", inline := false, exported := false, params := [],
       body := .raise (holMl "F") (.const 9), returnShape := .one }]

def exactDuplicateExceptionOracle : Bool :=
  (getEidsFromDeclsHOL exactDuplicateExceptionDecls).lookup (holMl "E") ==
      some (0 : BitVec 8) &&
    (getEidsFromDeclsHOL exactDuplicateExceptionDecls).lookup (holMl "F") ==
      some (1 : BitVec 8) &&
    (match compileToCrepExactHOLW exactDuplicateExceptionDecls with
     | [(fname, [], .seq
          (.dec 1 (.const seven)
            (.seq (.storeGlob first (.var 1)) .skip)) (.raise ecode)),
        (gname, [], .seq
          (.dec 1 (.const nine)
            (.seq (.storeGlob second (.var 1)) .skip)) (.raise fcode))] =>
          fname == holMl "f" && gname == holMl "g" &&
            seven == (7 : BitVec 8) && nine == (9 : BitVec 8) &&
            first == (0 : BitVec 5) && second == (0 : BitVec 5) &&
            ecode == (0 : BitVec 8) && fcode == (1 : BitVec 8)
     | _ => false)

#guard exactDuplicateExceptionOracle

def compileToCrepeProbeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 0)],
    maxVar := 0, bytesInWord := 1 }

def compileToCrepeProbeDecls : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "f", inline := false, exported := false,
       params := [("x", .one)],
       body := .raise "E" (.const 7), returnShape := .one }]

/-! Direct `make_funcs_def` oracle: exception declarations are skipped and the
    function entry preserves both source parameters and return shape. -/
def makeFuncsOracle : Bool :=
  match panToCrepMakeFuncs compileToCrepeProbeDecls with
  | [("f", ([("x", .one)], .one))] => true
  | _ => false

#guard makeFuncsOracle

/-! Direct HOL `crep_vars_def` oracle (the `crep_vars_empty` and
    `crep_vars_nested` lines in `compile_to_crep_probe.out`): nested parameter
    shapes flatten in source order and receive consecutive slots. -/
def crepVarsOracle : Bool :=
  panToCrepVars [] == [] &&
    panToCrepVars [("left", .one), ("pair", .comb [.one, .one]),
      ("right", .one)] == [0, 1, 2, 3]

#guard crepVarsOracle

/-! Direct HOL `mk_ctxt_fields` oracle in `compile_to_crep_probe.out`:
    the constructor preserves all four fields in HOL's argument order. -/
def mkCtxtOracle : Bool :=
  let vars : HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
    HolFiniteMapExact.empty.updateEq (holMl "x", (.one, [0]))
  let funcs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL) :=
    HolFiniteMapExact.empty.updateEq (holMl "f", ([(holMl "x", .one)], .one))
  let eids : HolFiniteMapExact MlS (BitVec 8) :=
    HolFiniteMapExact.empty.updateEq (holMl "E", 2)
  let context := mkCtxtExactHOL vars funcs 3 eids
  context.vmax == 3 &&
    (context.vars.lookup (holMl "x")).isSome &&
    (context.funcs.lookup (holMl "f")).isSome &&
    context.eids.lookup (holMl "E") == some 2

#guard mkCtxtOracle

/-! Direct `make_vmap_def` oracle: shaped parameters receive consecutive
    flattened slots in source order. -/
def makeVmapOracle : Bool :=
  match panToCrepMakeVmap [("x", .one), ("pair", .comb [.one, .one])] with
  | [("pair", (.comb [.one, .one], [1, 2])), ("x", (.one, [0]))] => true
  | _ => false

#guard makeVmapOracle

/-! Direct HOL `make_vmap_shaped` and `make_vmap_duplicate_lookup` oracle:
    the finite-map production path allocates consecutive slots and its later
    duplicate parameter wins the lookup. -/
def makeVmapHOLOracle : Bool :=
  let shaped := panToCrepMakeVmapHOL
    [("x", .one), ("pair", .comb [.one, .one])]
  let duplicate := panToCrepMakeVmapHOL
    [("x", .one), ("x", .comb [.one, .one])]
  match FLOOKUP shaped "x", FLOOKUP shaped "pair", FLOOKUP duplicate "x" with
  | some (.one, [0]), some (.comb [.one, .one], [1, 2]),
      some (.comb [.one, .one], [1, 2]) => true
  | _, _, _ => false

#guard makeVmapHOLOracle

/-! Cake's `FEMPTY |++ ZIP` gives the later duplicate parameter the result of
    lookup.  This is deliberately a malformed direct compiler input: the
    source static checker rejects duplicate formal names, but the executable
    `make_vmap` boundary must still agree with the HOL definition. -/
def duplicateVmapOracle : Bool :=
  match lookupInfo "x" (panToCrepMakeVmap
      [("x", .one), ("x", .comb [.one, .one])]) with
  | some (.comb [.one, .one], [1, 2]) => true
  | _ => false

#guard duplicateVmapOracle

def duplicateFunctionDecls : List (Decl Nat) :=
  [.function
      { name := "dup", inline := false, exported := false, params := [],
        body := .return (.const 1), returnShape := .one },
   .function
      { name := "dup", inline := false, exported := false,
        params := [("x", .one)], body := .return (.var .local "x"),
        returnShape := .one }]

/-! `make_funcs_def` is the same first-binding finite-map construction as
    `ALOOKUP`; the first duplicate therefore remains visible. -/
def duplicateFuncsOracle : Bool :=
  match lookupInfo "dup" (functionInfos duplicateFunctionDecls) with
  | some ([], .one) => true
  | _ => false

#guard duplicateFuncsOracle

/-! Cake's `FEMPTY |++ ZIP` gives the later duplicate parameter binding to
    `FLOOKUP`; the list-backed source map therefore keeps the later slot first.
    The body probe makes the selected slot observable at the Crepe boundary. -/
def duplicateParameterLastWinsOracle : Bool :=
  match panToCrepMakeVmap [("x", .one), ("x", .one)] with
  | [("x", (.one, [1])), ("x", (.one, [0]))] =>
      match panToCrepCompFunc compileToCrepeProbeContext
          [("x", .one), ("x", .one)]
          (.return (.var .local "x")) with
      | .return [.var 1] => true
      | _ => false
  | _ => false

#guard duplicateParameterLastWinsOracle

/-! Direct `comp_func_def` oracle: the source-shaped wrapper uses the
    flattened parameter shape to choose `vmax` and preserves the compiled
    raise body from the Cake fixture. -/
def compFuncOracle : Bool :=
  match panToCrepCompFunc compileToCrepeProbeContext [("x", .one)]
      (.raise "E" (.const 7)) with
  | .seq (.dec 1 (.const 7) (.seq (.storeGlob 0 (.var 1)) .skip))
      (.raise 0) => true
  | _ => false

#guard compFuncOracle

def compileToCrepePairContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 0)],
    maxVar := 0, bytesInWord := 8 }

def compileToCrepePairDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "E" (.rStruct [.const 7, .const 9]),
       returnShape := .one }]

/-! Direct `raise_pair` result from `compile_to_crep_probe.out`.  In
    particular, the Crep global return area is word-indexed (0, 1), even when
    the target byte width is 8. -/
def pairRaiseOracle : Bool :=
  match compileToCrep compileToCrepePairContext compileToCrepePairDecls with
  | [{ name := "f", params := [],
       body := .seq
         (.dec 1 (.const 7)
           (.dec 2 (.const 9)
             (.seq (.storeGlob 0 (.var 1))
               (.seq (.storeGlob 1 (.var 2)) .skip))))
         (.raise 0),
       returnShape := .one }] => true
  | _ => false

#guard pairRaiseOracle

def laterPairDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .dec "a" .one (.const 3)
         (.dec "b" .one (.const 5)
           (.raise "E" (.rStruct [.const 7, .const 9]))),
       returnShape := .one }]

/-! Direct `raise_pair_later` result from `compile_to_crep_probe.out`.  Two
    ordinary declarations first consume the word-strided slots 1 and 2, so a
    two-word exception payload lowered afterwards must take the later,
    contiguous Temp slots 3 and 4 and store them at the one-word Crep global
    indices `0w`/`1w` (not byte-scaled), even at target byte width 8. -/
def laterPairOracle : Bool :=
  match compileToCrep compileToCrepePairContext laterPairDecls with
  | [{ name := "f", params := [],
       body := .dec 1 (.const 3)
         (.dec 2 (.const 5)
           (.seq
             (.dec 3 (.const 7)
               (.dec 4 (.const 9)
                 (.seq (.storeGlob 0 (.var 3))
                   (.seq (.storeGlob 1 (.var 4)) .skip))))
             (.raise 0))),
       returnShape := .one }] => true
  | _ => false

#guard laterPairOracle

/-! Follow the actual 64-bit declaration-only HOL compiler result through
`crep_to_loop`, `loop_to_word`, and `word_to_stack`. This checks that the
one-word Crep global indices from `raise_pair_later` survive as Stack Temp 0
and Temp 1. The original pass rules are `loop_to_wordScript.sml:93` and
`compiler/backend/word_to_stackScript.sml:491`. -/
def exactLaterPairRaiseProbe64 : List (DeclHOL 64) :=
  [.exnDecl (holMl "E") (.comb [.one, .one]),
   .function
     { name := holMl "f", inline := false, exported := false, params := [],
       body := .dec (holMl "a") .one (.const 3)
         (.dec (holMl "b") .one (.const 5)
           (.raise (holMl "E") (.rstruct [.const 7, .const 9]))),
       returnShape := .one }]

/-! Exact `raise_pair_later_64` row from the direct HOL probe: the ordinary
declarations use slots 1 and 2, the later two-word payload uses slots 3 and 4,
and its global return area uses the unscaled Temp-region indices 0 and 1. -/
def exactLaterPairRaiseOracle64 : Bool :=
  match compileToCrepExactHOLW exactLaterPairRaiseProbe64 with
  | [(name, [],
      .dec 1 (.const three)
        (.dec 2 (.const five)
          (.seq
            (.dec 3 (.const seven)
              (.dec 4 (.const nine)
                (.seq (.storeGlob first (.var 3))
                  (.seq (.storeGlob second (.var 4)) .skip))))
            (.raise code))))] =>
      name == holMl "f" && three == (3 : BitVec 64) && five == (5 : BitVec 64) &&
        seven == (7 : BitVec 64) && nine == (9 : BitVec 64) &&
        first == (0 : BitVec 5) && second == (1 : BitVec 5) &&
        code == (0 : BitVec 64)
  | _ => false

#guard exactLaterPairRaiseOracle64

def handledPairDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "E" (.rStruct [.const 7, .const 9]),
       returnShape := .comb [.one, .one] },
   .function
     { name := "g", inline := false, exported := false,
       params := [("pair", .comb [.one, .one])],
       body := .call
         (some (some (.local, "pair"), some ("E", "pair", .skip))) "f" [],
       returnShape := .one }]

/-! Direct `handled_pair` row in `compile_to_crep_probe.out`: the function
    raises a two-field RStruct payload, and the handled call carries both its
    two-word result slots and the exception handler that reloads both payload
    words from the Crep global return area. -/
def handledPairOracle : Bool :=
  match compileToCrep compileToCrepePairContext handledPairDecls with
  | [{ name := "f", params := [],
       body := .seq
         (.dec 1 (.const 7)
           (.dec 2 (.const 9)
             (.seq (.storeGlob 0 (.var 1))
               (.seq (.storeGlob 1 (.var 2)) .skip))))
         (.raise 0), returnShape := .comb [.one, .one] },
     { name := "g", params := [0, 1],
       body := .call
         (some ([0, 1], some (0,
           .seq (.seq (.assign 0 (.loadGlob 0))
             (.seq (.assign 1 (.loadGlob 1)) .skip)) .skip)))
         "f" [], returnShape := .one }] => true
  | _ => false

#guard handledPairOracle

def callOracleContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 0)],
    maxVar := 0, bytesInWord := 8 }

def globalDestinationDecls : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .comb [.one, .one] },
   .function
     { name := "g", inline := false, exported := false,
       params := [("pair", .comb [.one, .one])],
       body := .call (some (some (.global, "pair"), none)) "f" [],
       returnShape := .one }]

/-! Direct `global_dest` row in `compile_prog_probe.out`.  The source kind
    is ignored at this boundary; the global-tagged destination still receives
    the two flattened parameter slots. -/
def globalDestinationOracle : Bool :=
  match compileToCrep callOracleContext globalDestinationDecls with
  | [{ name := "f", params := [], body := .skip, returnShape := .comb [.one, .one] },
     { name := "g", params := [0, 1],
       body := .call (some ([0, 1], none)) "f" [],
       returnShape := .one }] => true
  | _ => false

#guard globalDestinationOracle

def handledMissingDestinationDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .comb [.one, .one] },
   .function
     { name := "g", inline := false, exported := false,
       params := [("pair", .comb [.one, .one])],
       body := .call
         (some (some (.local, "missing"), some ("E", "pair", .skip))) "f" [],
       returnShape := .one }]

/-! Direct `handled_missing_dest` row in `compile_prog_probe.out`. -/
def handledMissingDestinationOracle : Bool :=
  match compileToCrep callOracleContext handledMissingDestinationDecls with
  | [{ name := "f", params := [], body := .skip, returnShape := .comb [.one, .one] },
     { name := "g", params := [0, 1],
       body := .call (some ([], some (0,
         .seq (.seq (.assign 0 (.loadGlob 0))
           (.seq (.assign 1 (.loadGlob 1)) .skip)) .skip))) "f" [],
       returnShape := .one }] => true
  | _ => false

#guard handledMissingDestinationOracle

/-! The fixture is the direct HOL evaluation of
    `pan_to_crep$compile_to_crep` on the same exception/function declaration.
    `compileToCrep` preserves the source function name, flattened parameter
    slot, nested payload spill, and looked-up exception code. -/
theorem compile_to_crep_raise_const_parity :
    compileToCrep compileToCrepeProbeContext compileToCrepeProbeDecls =
      [{ name := "f", params := [0],
         body := .seq
           (.dec 1 (.const 7)
             (.seq (.storeGlob 0 (.var 1)) .skip))
           (.raise 0),
         returnShape := .one }] := by
  simp [compileToCrep, compileFunctionsSource, compileFunDeclSource,
    panToCrepCompFunc, panToCrepVars_eq, Shape.shapeSize,
    functionInfos, compileToCrepeProbeContext, compileToCrepeProbeDecls,
    compileProg, compileExp, freshNames, nestedDecs, storeGlobals,
    crepNestedSeq, lookupInfo]

def parityGuard : Bool :=
  match compileToCrep compileToCrepeProbeContext compileToCrepeProbeDecls with
  | [{ name := "f", params := [0],
       body := .seq
         (.dec 1 (.const 7) (.seq (.storeGlob 0 (.var 1)) .skip))
         (.raise 0), returnShape := .one }] => true
  | _ => false

#eval parityGuard
#guard
  parityGuard

end Flapjack.Test.CompileToCrepeParity
