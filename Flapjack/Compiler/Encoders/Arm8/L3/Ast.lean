import Flapjack.Compiler.Encoders.Arm8.L3.Defs

/-!
# L3 ARMv8 byte encoding

The byte-level encoder from `cakeml/compiler/encoders/arm8/arm8_targetScript.sml`
that `arm8_config` uses.  `arm8_encode` turns one L3 `instruction` into four
bytes; `arm8_encode_fail` is the `NoOperation` list used by `arm8_ast` for
unavailable operations.  The full `arm8_ast` lowering (from `asm` instructions
to L3 `instruction` values) and the exact `arm8_config` record are still to be
ported; the closed-model `arm8Ast`/`arm8Config` remain separate.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack

/-- `arm8_encode_fail` (`arm8_targetScript.sml:30-31`): the `NoOperation`
instruction list. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_encode_fail_def"]
def arm8EncodeFail : List instruction := [NoOperation]

/-- `arm8_encode` (`arm8_targetScript.sml:34-38`): little-endian bytes of the
L3 `Encode` result, or four zero bytes for `BadCode`.

    Tagged `pending_statement_review`: the statement is a direct transcription,
    but its callee `Encode` is itself a mechanically rendered (unreviewed) L3
    definition. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_encode_def"]
noncomputable def arm8Encode (i : instruction) : List (BitVec 8) :=
  match Encode i with
  | .ARM8 w =>
      [BitVec.ofNat 8 ((w >>> 0).toNat),
       BitVec.ofNat 8 ((w >>> 8).toNat),
       BitVec.ofNat 8 ((w >>> 16).toNat),
       BitVec.ofNat 8 ((w >>> 24).toNat)]
  | .BadCode _ => [0, 0, 0, 0]

end Flapjack.Compiler.Encoders.Arm8.L3
