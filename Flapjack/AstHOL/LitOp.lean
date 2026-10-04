import Flapjack.AstHOL.BackendOperators
import Flapjack.Basis.Pure.MlString

/-!
# `astScript`: literals, primitive operators and name abbreviations

Counterparts of `cakeml/semantics/astScript.sml` lines 10-188: `lit`, `arith`,
the name abbreviations `modN`/`varN`/`conN`/`typeN`/`tvarN` (all `mlstring`),
`prim_type`, `op`, `op_class`, `getOpClass_def` and `lop`. HOL `int` is `Int`,
`char` is the reviewed 256-element `HolChar`, `word8`/`word64` are `BitVec 8`/
`BitVec 64` at their fixed widths, and `mlstring` is `MlString`. Constructor order
and payloads match the source; constructor names are lower camel case.
-/

namespace Flapjack.AstHOL

open Flapjack.Basis.Pure.MlString

/-- Complete original `lit` (astScript 10-18). -/
@[hol "cakeml/semantics/astScript.sml" "lit"]
inductive Lit where
  | intLit : Int → Lit
  | char : HolChar → Lit
  | strLit : MlString → Lit
  | word8 : BitVec 8 → Lit
  | word64 : BitVec 64 → Lit
  | float64 : BitVec 64 → Lit
  deriving DecidableEq, Repr

/-- Complete original `arith` (astScript 24-26). -/
@[hol "cakeml/semantics/astScript.sml" "arith"]
inductive Arith where
  | add | sub | mul | div | mod | neg | and | xor | or | not | abs | sqrt | fma
  deriving DecidableEq, Repr

/-- Original `Type modN = “:mlstring”` (astScript 29). -/
@[hol "cakeml/semantics/astScript.sml" "modN"]
abbrev ModN := MlString

/-- Original `Type varN = “:mlstring”` (astScript 32). -/
@[hol "cakeml/semantics/astScript.sml" "varN"]
abbrev VarN := MlString

/-- Original `Type conN = “:mlstring”` (astScript 35). -/
@[hol "cakeml/semantics/astScript.sml" "conN"]
abbrev ConN := MlString

/-- Original `Type typeN = “:mlstring”` (astScript 38). -/
@[hol "cakeml/semantics/astScript.sml" "typeN"]
abbrev TypeN := MlString

/-- Original `Type tvarN = “:mlstring”` (astScript 41). -/
@[hol "cakeml/semantics/astScript.sml" "tvarN"]
abbrev TvarN := MlString

/-- Complete original `prim_type` (astScript 66-73). -/
@[hol "cakeml/semantics/astScript.sml" "prim_type"]
inductive PrimType where
  | boolT
  | intT
  | charT
  | strT
  | wordT : WordSize → PrimType
  | float64T
  deriving DecidableEq, Repr

/-- Complete original `op` (astScript 75-137): all 43 constructors in source
order with their payloads. -/
@[hol "cakeml/semantics/astScript.sml" "op"]
inductive Op where
  | arith : Arith → PrimType → Op
  | fromTo : PrimType → PrimType → Op
  | shift : WordSize → Shift → Nat → Op
  | equality
  | test : Test → PrimType → Op
  | opapp
  | opassign
  | opref
  | opderef
  | aw8alloc
  | aw8sub
  | aw8length
  | aw8update
  | copyStrStr
  | copyStrAw8
  | copyAw8Str
  | copyAw8Aw8
  | xorAw8StrUnsafe
  | implode
  | explode
  | strsub
  | strlen
  | strcat
  | vfromList
  | vsub
  | vlength
  | aalloc
  | aallocEmpty
  | aallocFixed
  | asub
  | alength
  | aupdate
  | vsubUnsafe
  | asubUnsafe
  | aupdateUnsafe
  | aw8subUnsafe
  | aw8updateUnsafe
  | thunkOp : ThunkOp → Op
  | listAppend
  | configGC
  | ffi : MlString → Op
  | eval
  | envId
  deriving DecidableEq, Repr

/-- Complete original `op_class` (astScript 140-146). -/
@[hol "cakeml/semantics/astScript.sml" "op_class"]
inductive OpClass where
  | evalOp
  | funApp
  | force
  | simple
  deriving DecidableEq, Repr

/-- Exact HOL `getOpClass_def` (astScript 148-155). -/
@[hol "cakeml/semantics/astScript.sml" "getOpClass_def"]
def getOpClass (op : Op) : OpClass :=
  match op with
  | .opapp => .funApp
  | .eval => .evalOp
  | .thunkOp t => if t = .forceThunk then .force else .simple
  | _ => .simple

/-- Complete original `lop = Andalso | Orelse` (astScript 187-189). -/
@[hol "cakeml/semantics/astScript.sml" "lop"]
inductive Lop where
  | andalso
  | orelse
  deriving DecidableEq, Repr

end Flapjack.AstHOL
