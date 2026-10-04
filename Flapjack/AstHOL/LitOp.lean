import Flapjack.AstHOL.BackendOperators
import Flapjack.Basis.Pure.MlString

/-!
# `astScript`: literals, primitive operators and name abbreviations

Counterparts of `cakeml/semantics/astScript.sml` lines 10-188: `lit`, `arith`,
the name abbreviations `modN`/`varN`/`conN`/`typeN`/`tvarN` (all `mlstring`),
`prim_type`, `op`, `op_class`, `getOpClass_def` and `lop`. HOL `int` is `Int`,
`char` is the reviewed 256-element `HolChar`, `word8`/`word64` are `BitVec 8`/
`BitVec 64` at their fixed widths, and `mlstring` is `MlString`. The riscv-mi carriers omit floating-point literals, primitive types and
arithmetic selectors. Retained constructors keep their source order and
payloads; constructor names are lower camel case.
-/

namespace Flapjack.AstHOL

open Flapjack.Basis.Pure.MlString

/-- Integer specialization of `lit` (astScript 10-18), excluding `Float64`. -/
-- riscv-mi: integer source carrier; floating-point constructors removed.
inductive Lit where
  | intLit : Int → Lit
  | char : HolChar → Lit
  | strLit : MlString → Lit
  | word8 : BitVec 8 → Lit
  | word64 : BitVec 64 → Lit
  deriving DecidableEq, Repr

/-- Integer specialization of `arith` (astScript 24-26), excluding `Sqrt` and `Fma`. -/
-- riscv-mi: integer source carrier; floating-point constructors removed.
inductive Arith where
  | add | sub | mul | div | mod | neg | and | xor | or | not | abs
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

/-- Integer specialization of `prim_type` (astScript 66-73), excluding `Float64T`. -/
-- riscv-mi: integer source carrier; floating-point constructors removed.
inductive PrimType where
  | boolT
  | intT
  | charT
  | strT
  | wordT : WordSize → PrimType
  deriving DecidableEq, Repr

/-- The `op` constructors (astScript 75-137) in source order, with their
`Arith` and `PrimType` payloads specialized to the integer carriers above. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
