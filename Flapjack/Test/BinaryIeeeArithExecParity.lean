import Flapjack.Misc.BinaryIeeeArithExec

namespace Flapjack.Test.BinaryIeeeArithExecParity
open Flapjack

private def one : BitVec 64 := 0x3FF0000000000000
private def two : BitVec 64 := 0x4000000000000000
private def negone : BitVec 64 := 0xBFF0000000000000
private def pz : BitVec 64 := 0x0
private def nz : BitVec 64 := 0x8000000000000000
private def pinf : BitVec 64 := 0x7FF0000000000000
private def ninf : BitVec 64 := 0xFFF0000000000000
private def tenth : BitVec 64 := 0x3FB999999999999A
private def fifth : BitVec 64 := 0x3FC999999999999A
private def three : BitVec 64 := 0x4008000000000000
private def ten : BitVec 64 := 0x4024000000000000
private def sub1 : BitVec 64 := 0x1
private def maxfin : BitVec 64 := 0x7FEFFFFFFFFFFFFF
private def eps : BitVec 64 := 0x3CA0000000000000
private def qnan : BitVec 64 := 0x7FF8000000000000

-- Original oracle add_pinf_one.
example : execFp64Add pinf one = 0x7FF0000000000000 := by decide +kernel
-- Original oracle add_one_ninf.
example : execFp64Add one ninf = 0xFFF0000000000000 := by decide +kernel
-- Original oracle add_pinf_pinf.
example : execFp64Add pinf pinf = 0x7FF0000000000000 := by decide +kernel
-- Original oracle sub_one_pinf.
example : execFp64Sub one pinf = 0xFFF0000000000000 := by decide +kernel
-- Original oracle sub_ninf_pinf.
example : execFp64Sub ninf pinf = 0xFFF0000000000000 := by decide +kernel
-- Original oracle mul_pinf_negone.
example : execFp64Mul pinf negone = 0xFFF0000000000000 := by decide +kernel
-- Original oracle mul_ninf_ninf.
example : execFp64Mul ninf ninf = 0x7FF0000000000000 := by decide +kernel
-- Original oracle div_one_pinf.
example : execFp64Div one pinf = 0 := by decide +kernel
-- Original oracle div_negone_pinf.
example : execFp64Div negone pinf = 0x8000000000000000 := by decide +kernel
-- Original oracle div_pinf_negone.
example : execFp64Div pinf negone = 0xFFF0000000000000 := by decide +kernel
-- Original oracle div_one_pz.
example : execFp64Div one pz = 0x7FF0000000000000 := by decide +kernel
-- Original oracle div_negone_pz.
example : execFp64Div negone pz = 0xFFF0000000000000 := by decide +kernel
-- Original oracle div_one_nz.
example : execFp64Div one nz = 0xFFF0000000000000 := by decide +kernel
-- Original oracle fma_pinf_product.
example : execFp64Fma one pinf two = 0x7FF0000000000000 := by decide +kernel
-- Original oracle fma_ninf_addend.
example : execFp64Fma ninf one one = 0xFFF0000000000000 := by decide +kernel
-- Original oracle fma_neg_inf_product.
example : execFp64Fma one ninf two = 0xFFF0000000000000 := by decide +kernel
-- Original oracle fma_order_inf.
example : execFp64Fma one ninf pinf = 0xFFF0000000000000 := by decide +kernel
-- Original oracle add_tenth_fifth.
example : execFp64Add tenth fifth = 0x3FD3333333333334 := by decide +kernel
-- Original oracle add_one_halfulp.
example : execFp64Add one eps = 0x3FF0000000000000 := by decide +kernel
-- Original oracle add_pz_nz.
example : execFp64Add pz nz = 0 := by decide +kernel
-- Original oracle add_nz_nz.
example : execFp64Add nz nz = 0x8000000000000000 := by decide +kernel
-- Original oracle add_max_max.
example : execFp64Add maxfin maxfin = 0x7FF0000000000000 := by decide +kernel
-- Original oracle sub_one_one.
example : execFp64Sub one one = 0 := by decide +kernel
-- Original oracle sub_nz_pz.
example : execFp64Sub nz pz = 0x8000000000000000 := by decide +kernel
-- Original oracle sub_three_tenth.
example : execFp64Sub three tenth = 0x4007333333333333 := by decide +kernel
-- Original oracle mul_tenth_three.
example : execFp64Mul tenth three = 0x3FD3333333333334 := by decide +kernel
-- Original oracle mul_negone_pz.
example : execFp64Mul negone pz = 0x8000000000000000 := by decide +kernel
-- Original oracle mul_max_two.
example : execFp64Mul maxfin two = 0x7FF0000000000000 := by decide +kernel
-- Original oracle mul_sub1_half.
example : execFp64Mul sub1 0x3FE0000000000000 = 0 := by decide +kernel
-- Original oracle div_one_three.
example : execFp64Div one three = 0x3FD5555555555555 := by decide +kernel
-- Original oracle div_one_ten.
example : execFp64Div one ten = 0x3FB999999999999A := by decide +kernel
-- Original oracle div_negone_three.
example : execFp64Div negone three = 0xBFD5555555555555 := by decide +kernel
-- Original oracle div_sub1_two.
example : execFp64Div sub1 two = 0 := by decide +kernel
-- Original oracle fma_tenth_ten_negone.
example : execFp64Fma negone tenth ten = 0x3C90000000000000 := by decide +kernel
-- Original oracle fma_one_one_one.
example : execFp64Fma one one one = 0x4000000000000000 := by decide +kernel
-- Original oracle fma_zero_sign.
example : execFp64Fma pz negone pz = 0 := by decide +kernel
-- Original oracle fma_cancel.
example : execFp64Fma negone one one = 0 := by decide +kernel
-- Original symbolic quiet-NaN branch add_qnan_input; executable payload is canonical.
example : execFp64Add qnan one = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch sub_qnan_input; executable payload is canonical.
example : execFp64Sub qnan one = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch mul_qnan_input; executable payload is canonical.
example : execFp64Mul qnan one = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch div_qnan_input; executable payload is canonical.
example : execFp64Div qnan one = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch fma_qnan_input; executable payload is canonical.
example : execFp64Fma qnan one one = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch add_invalid_infinities; executable payload is canonical.
example : execFp64Add pinf ninf = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch sub_invalid_infinities; executable payload is canonical.
example : execFp64Sub pinf pinf = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch mul_invalid_inf_zero; executable payload is canonical.
example : execFp64Mul pinf pz = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch div_invalid_zero_zero; executable payload is canonical.
example : execFp64Div pz pz = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch div_invalid_inf_inf; executable payload is canonical.
example : execFp64Div pinf ninf = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch fma_invalid_inf_zero; executable payload is canonical.
example : execFp64Fma one pinf pz = defaultQuietNan := by decide +kernel
-- Original symbolic quiet-NaN branch fma_invalid_opposed_infinities; executable payload is canonical.
example : execFp64Fma ninf pinf one = defaultQuietNan := by decide +kernel
example (a b : BitVec 64) : fp64Refines (holFp64Add .roundTiesToEven a b) (execFp64Add a b) := holFp64Add_refines_exec a b
example (a b : BitVec 64) : fp64Refines (holFp64Sub .roundTiesToEven a b) (execFp64Sub a b) := holFp64Sub_refines_exec a b
example (a b : BitVec 64) : fp64Refines (holFp64Mul .roundTiesToEven a b) (execFp64Mul a b) := holFp64Mul_refines_exec a b
example (a b : BitVec 64) : fp64Refines (holFp64Div .roundTiesToEven a b) (execFp64Div a b) := holFp64Div_refines_exec a b
example (a b c : BitVec 64) : fp64Refines (fpSemFpfma a b c) (execFp64Fma a b c) := fpSemFpfma_refines_exec a b c
end Flapjack.Test.BinaryIeeeArithExecParity
