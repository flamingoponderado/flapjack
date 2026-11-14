module

public import Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams
public import Flapjack.Pancake.PanToCrep.CompileExact

import all Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams
import all Flapjack.Pancake.PanToCrep.CompileExact
public meta import Flapjack.Pancake.PanToCrep.CompileExact
public meta import Flapjack.Pancake.PanLang
public meta import Flapjack.Pancake.PanLang.Decl
public meta import Flapjack.Pancake.PanToCrep.Compile

@[expose] public section

namespace Flapjack.Test.CompileProgParamsParity

open Flapjack
open Flapjack.Pancake.PanLang (DeclHOL functionsHOL)
open Flapjack.Basis.Pure.MlString

/-! Direct `params_two_words` result from the original HOL
    `compile_prog_probe.out`: the structured parameter occupies slots 0, 1. -/
def twoWordParamDecls : List (DeclHOL 8) :=
  [.function
     { name := ofString "pair", inline := false, exported := false,
       params := [(ofString "p", .comb [.one, .one])],
       body := .skip, returnShape := .one }]

def twoWordParamParity : Bool :=
  match compileProgDeclsHOLW twoWordParamDecls with
  | [(name, [0, 1], .skip)] => name == ofString "pair"
  | _ => false

#guard twoWordParamParity

end Flapjack.Test.CompileProgParamsParity
