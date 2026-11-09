import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Compiler.Backend.ClosToBvl.Constants
import Flapjack.HolRef

/-! Source-shaped constant-part construction used by closure conversion. -/
namespace Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.ClosLang Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.BackendCommon Flapjack.Basis.Pure.MlString

/-- Interpret one constant part using previously built values. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_part'_def"]
def buildPart (memory : Nat → Value) : ConstPart → Value
  | .int n => .number n
  | .str text => .byteVector text.explode
  | .w64 word => .word64 word
  | .con tag indices => .block tag (indices.map memory)

/-- Interpret parts in order, recording each result at its assigned index. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build'_def"]
def build (memory : Nat → Value) (index : Nat) : List ConstPart → Value
  | [] => memory (index - 1)
  | part :: rest => build (fun key => if key = index then buildPart memory part else memory key) (index + 1) rest

/-- Construct a constant from its part sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_const'_def"]
def buildConst (parts : List ConstPart) : Value :=
  build (fun _ => .number 0) 0 parts

/-- Shift constructor tags in a constant part. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "update_tag_def"]
def updateTag : ConstPart → ConstPart
  | .con tag indices => .con (closTagShift tag) indices
  | part => part

end Flapjack.Compiler.Backend.ClosConstant.Proofs
