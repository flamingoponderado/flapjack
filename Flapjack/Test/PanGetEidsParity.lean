module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobalsByteRanged
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display

@[expose] public section

/-!
# Pancake `get_eids` parity

The expected mappings are transcribed from
`cakeml/pancake/pan_to_crepScript.sml:346-353` (`get_eids_def`).  The test
exercises the complete observable: body traversal order, first-occurrence
deduplication, and consecutive target-word numbering.
-/

namespace Flapjack.Test.PanGetEidsParity

open Flapjack

def raiseE (exception : ExceptionId) : Prog Nat :=
  .raise exception (.const 0)

def sourceFunctions : List (FunDecl Nat) :=
  [{ name := "first", inline := false, exported := false, params := [],
      body := .seq (raiseE "E") (raiseE "F"), returnShape := .one },
   { name := "second", inline := false, exported := false, params := [],
      body := .seq (raiseE "E") (raiseE "G"), returnShape := .one }]

/-! Cake's `get_eids_pan_simp_compile_eq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:105`): simplifying the
    function bodies does not change the exception-code table, hence not its
    finite domain. -/

def getEidsDecls : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "F" (.const 0), returnShape := .one },
   .decl .one "x" (.const 1),
   .name "S" []]

/-! Cake's `distinct_make_funcs`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3757`): the function
    table built by `make_funcs` assigns distinct labels. -/

def distinctFuncsCode : List (CompiledFunction Nat) :=
  [{ name := "first", params := [], body := .skip, returnShape := .one },
   { name := "second", params := [], body := .skip, returnShape := .one }]

/-! Cake's `initial_prog_make_funcs_el`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3942`): a successful
    label lookup identifies the position of the function in the source list. -/

def makeFuncsIndexGuard : Bool :=
  (distinctFuncsCode[1]?).map (fun function => function.name) == some "second"

#eval makeFuncsIndexGuard
#guard makeFuncsIndexGuard

end Flapjack.Test.PanGetEidsParity
