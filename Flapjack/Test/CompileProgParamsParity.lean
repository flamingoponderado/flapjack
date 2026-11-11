module

public import Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams

import all Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams
public meta import Flapjack.Pancake.PanLang
public meta import Flapjack.Pancake.PanLang.Decl
public meta import Flapjack.Pancake.PanToCrep.Compile

@[expose] public section

namespace Flapjack.Test.CompileProgParamsParity

open Flapjack

/-! Direct `params_two_words` result from the original HOL
    `compile_prog_probe.out`: the structured parameter occupies slots 0, 1. -/
def twoWordParamDecls : List (Decl (BitVec 8)) :=
  [.function
     { name := "pair", inline := false, exported := false,
       params := [("p", .comb [.one, .one])],
       body := .skip, returnShape := .one }]

def twoWordParamParity : Bool :=
  match compileProgTopHOL twoWordParamDecls with
  | [("pair", [0, 1], .skip)] => true
  | _ => false

#guard twoWordParamParity

end Flapjack.Test.CompileProgParamsParity
