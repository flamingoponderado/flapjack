module

public import Flapjack.Compiler.Backend.Bvl.Syntax
public import Flapjack.Compiler.Backend.BackendCommon.BoolTags

@[expose] public section

namespace Flapjack.Compiler.Backend.Bvl

/-- The source BVL Boolean constructor. -/
@[hol "cakeml/compiler/backend/bvlScript.sml" "Bool_def"]
def boolExp (value : Bool) : Exp :=
  .op (.blockOp (.cons (BackendCommon.boolToTag value))) []

end Flapjack.Compiler.Backend.Bvl
