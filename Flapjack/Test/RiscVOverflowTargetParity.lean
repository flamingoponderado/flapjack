import Flapjack.RiscV.Backend
import Flapjack.RiscV.Encoding

/-! Original HOL `riscv_ast` and `riscv_enc` observations for the overflow
clauses at riscv_targetScript.sml:151–164 are captured in
scripts/hol-probes/riscv_overflow_target_probe.out. These kernel checks compare
staged RV64 lowering helpers with the original instruction order and bytes,
including literal register aliases. They do not assert execution correctness
for aliased operands or identify the two instruction datatypes. The executed
WordArith carrier/codec integration remains tracked separately. -/

namespace Flapjack.Test.RiscVOverflowTargetParity
open Flapjack.RiscV

-- overflow_add_ast_0 / overflow_add_enc_0
example : wordAddOverflowToInstructions 5 2 3 4 =
    [.xor 31 2 3, .xori 31 31 (-1), .add 5 2 3, .xor 4 3 5, .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 5 2 3 4) =
    [179, 79, 49, 0, 147, 207, 255, 255, 179, 2, 49, 0, 51, 194, 81, 0, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_sub_ast_0 / overflow_sub_enc_0
example : wordSubOverflowToInstructions 5 2 3 4 =
    [.xor 31 2 3, .sub 5 2 3, .xor 4 3 5, .xori 4 4 (-1), .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 5 2 3 4) =
    [179, 79, 49, 0, 179, 2, 49, 64, 51, 194, 81, 0, 19, 66, 242, 255, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_add_ast_1 / overflow_add_enc_1
example : wordAddOverflowToInstructions 0 0 0 0 =
    [.xor 31 0 0, .xori 31 31 (-1), .add 0 0 0, .xor 0 0 0, .and 0 31 0, .srli 0 0 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 0 0 0 0) =
    [179, 79, 0, 0, 147, 207, 255, 255, 51, 0, 0, 0, 51, 64, 0, 0, 51, 240, 15, 0, 19, 80, 240, 3] := by decide

-- overflow_sub_ast_1 / overflow_sub_enc_1
example : wordSubOverflowToInstructions 0 0 0 0 =
    [.xor 31 0 0, .sub 0 0 0, .xor 0 0 0, .xori 0 0 (-1), .and 0 31 0, .srli 0 0 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 0 0 0 0) =
    [179, 79, 0, 0, 51, 0, 0, 64, 51, 64, 0, 0, 19, 64, 240, 255, 51, 240, 15, 0, 19, 80, 240, 3] := by decide

-- overflow_add_ast_2 / overflow_add_enc_2
example : wordAddOverflowToInstructions 31 31 31 31 =
    [.xor 31 31 31, .xori 31 31 (-1), .add 31 31 31, .xor 31 31 31, .and 31 31 31, .srli 31 31 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 31 31 31 31) =
    [179, 207, 255, 1, 147, 207, 255, 255, 179, 143, 255, 1, 179, 207, 255, 1, 179, 255, 255, 1, 147, 223, 255, 3] := by decide

-- overflow_sub_ast_2 / overflow_sub_enc_2
example : wordSubOverflowToInstructions 31 31 31 31 =
    [.xor 31 31 31, .sub 31 31 31, .xor 31 31 31, .xori 31 31 (-1), .and 31 31 31, .srli 31 31 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 31 31 31 31) =
    [179, 207, 255, 1, 179, 143, 255, 65, 179, 207, 255, 1, 147, 207, 255, 255, 179, 255, 255, 1, 147, 223, 255, 3] := by decide

-- overflow_add_ast_3 / overflow_add_enc_3
example : wordAddOverflowToInstructions 30 29 28 27 =
    [.xor 31 29 28, .xori 31 31 (-1), .add 30 29 28, .xor 27 28 30, .and 27 31 27, .srli 27 27 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 30 29 28 27) =
    [179, 207, 206, 1, 147, 207, 255, 255, 51, 143, 206, 1, 179, 77, 238, 1, 179, 253, 191, 1, 147, 221, 253, 3] := by decide

-- overflow_sub_ast_3 / overflow_sub_enc_3
example : wordSubOverflowToInstructions 30 29 28 27 =
    [.xor 31 29 28, .sub 30 29 28, .xor 27 28 30, .xori 27 27 (-1), .and 27 31 27, .srli 27 27 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 30 29 28 27) =
    [179, 207, 206, 1, 51, 143, 206, 65, 179, 77, 238, 1, 147, 205, 253, 255, 179, 253, 191, 1, 147, 221, 253, 3] := by decide

-- overflow_add_ast_4 / overflow_add_enc_4
example : wordAddOverflowToInstructions 5 2 5 4 =
    [.xor 31 2 5, .xori 31 31 (-1), .add 5 2 5, .xor 4 5 5, .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 5 2 5 4) =
    [179, 79, 81, 0, 147, 207, 255, 255, 179, 2, 81, 0, 51, 194, 82, 0, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_sub_ast_4 / overflow_sub_enc_4
example : wordSubOverflowToInstructions 5 2 5 4 =
    [.xor 31 2 5, .sub 5 2 5, .xor 4 5 5, .xori 4 4 (-1), .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 5 2 5 4) =
    [179, 79, 81, 0, 179, 2, 81, 64, 51, 194, 82, 0, 19, 66, 242, 255, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_add_ast_5 / overflow_add_enc_5
example : wordAddOverflowToInstructions 4 2 3 4 =
    [.xor 31 2 3, .xori 31 31 (-1), .add 4 2 3, .xor 4 3 4, .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 4 2 3 4) =
    [179, 79, 49, 0, 147, 207, 255, 255, 51, 2, 49, 0, 51, 194, 65, 0, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_sub_ast_5 / overflow_sub_enc_5
example : wordSubOverflowToInstructions 4 2 3 4 =
    [.xor 31 2 3, .sub 4 2 3, .xor 4 3 4, .xori 4 4 (-1), .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 4 2 3 4) =
    [179, 79, 49, 0, 51, 2, 49, 64, 51, 194, 65, 0, 19, 66, 242, 255, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_add_ast_6 / overflow_add_enc_6
example : wordAddOverflowToInstructions 2 2 3 4 =
    [.xor 31 2 3, .xori 31 31 (-1), .add 2 2 3, .xor 4 3 2, .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 2 2 3 4) =
    [179, 79, 49, 0, 147, 207, 255, 255, 51, 1, 49, 0, 51, 194, 33, 0, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_sub_ast_6 / overflow_sub_enc_6
example : wordSubOverflowToInstructions 2 2 3 4 =
    [.xor 31 2 3, .sub 2 2 3, .xor 4 3 2, .xori 4 4 (-1), .and 4 31 4, .srli 4 4 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 2 2 3 4) =
    [179, 79, 49, 0, 51, 1, 49, 64, 51, 194, 33, 0, 19, 66, 242, 255, 51, 242, 79, 0, 19, 82, 242, 3] := by decide

-- overflow_add_ast_7 / overflow_add_enc_7
example : wordAddOverflowToInstructions 5 2 3 31 =
    [.xor 31 2 3, .xori 31 31 (-1), .add 5 2 3, .xor 31 3 5, .and 31 31 31, .srli 31 31 63] := by rfl

example : encodeInstructions (wordAddOverflowToInstructions 5 2 3 31) =
    [179, 79, 49, 0, 147, 207, 255, 255, 179, 2, 49, 0, 179, 207, 81, 0, 179, 255, 255, 1, 147, 223, 255, 3] := by decide

-- overflow_sub_ast_7 / overflow_sub_enc_7
example : wordSubOverflowToInstructions 5 2 3 31 =
    [.xor 31 2 3, .sub 5 2 3, .xor 31 3 5, .xori 31 31 (-1), .and 31 31 31, .srli 31 31 63] := by rfl

example : encodeInstructions (wordSubOverflowToInstructions 5 2 3 31) =
    [179, 79, 49, 0, 179, 2, 49, 64, 179, 207, 81, 0, 147, 207, 255, 255, 179, 255, 255, 1, 147, 223, 255, 3] := by decide

end Flapjack.Test.RiscVOverflowTargetParity
