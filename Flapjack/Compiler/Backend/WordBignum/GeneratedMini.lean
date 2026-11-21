-- Generated from the pinned HOL code-constant capture
-- (scripts/hol-probes/bignum_code_defs_probe.out) by
-- scripts/generate-bignum-mini.py; do not edit.
module

public import Flapjack.Compiler.Backend.WordBignum.Mini

@[expose] public section

/-! The 64 mini programs that HOL's `to_deep` (`word_bignumScript.sml`) defines
as constants `NAME_code`, in dependency order. Each mentions the other
generated constants by name, exactly as HOL's definitions do; `mcIopCode` is
the program the executable bignum generator compiles. These ports do not prove
the shallow-to-deep generator correct; that is the `*_corr_thm` family. -/

namespace Flapjack.Compiler.Backend.WordBignum

/-- HOL `mc_add1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_add1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_add1_code_def"
  (words_as_type_indexed_bitvec)]
def mcAdd1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [0] (.ite .equal 10 (.reg 11) (.seq (.assign 0 (.const 1)) (.seq (.store 0 10) (.seq (.assign 11 (.op .add [(.var 11), (.const 1)])) (.seq (.delete [0, 10, 2]) .skip)))) (.seq (.load 0 10 .out) (.ite .equal 0 (.reg 2) (.seq (.assign 0 (.const 0)) (.seq (.store 0 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.delete [0]) .continue)))) (.seq (.assign 0 (.op .add [(.var 0), (.const 1)])) (.seq (.store 0 10) (.seq (.delete [0, 10, 2]) .skip)))))))

/-- HOL `mc_add1_call_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_add1_call`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_add1_call_code_def"
  (words_as_type_indexed_bitvec)]
def mcAdd1CallCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 2 (.imm 0) (.seq (.delete [0, 10, 6, 2]) .skip) (.ite .equal 6 (.imm 0) (.seq (.delete [0, 10, 6, 2]) .skip) (.seq (.assign 2 (.const 0)) (.seq (.assign 10 (.var 2)) (.seq (.assign 2 (.op .xor [(.var 2), (.op .sub [(.const 0), (.const 1)])])) (.seq (mcAdd1Code width) (.seq (.delete [0, 10, 6, 2]) .skip)))))))

/-- HOL `mc_add_loop1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_add_loop1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_add_loop1_code_def"
  (words_as_type_indexed_bitvec)]
def mcAddLoop1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .equal 1 (.imm 1) (.seq (.assign 1 (.const 0)) .skip) (.seq (.assign 1 (.op .sub [(.var 1), (.const 1)])) (.seq (.load 8 10 .in1) (.seq (.load 9 10 .in2) (.seq (.add 8 3 8 (.reg 9) (.reg 3)) (.seq (.store 8 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) .continue))))))))

/-- HOL `mc_add_loop2_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_add_loop2`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_add_loop2_code_def"
  (words_as_type_indexed_bitvec)]
def mcAddLoop2Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .equal 1 (.imm 1) (.seq (.assign 1 (.const 0)) .skip) (.seq (.assign 1 (.op .sub [(.var 1), (.const 1)])) (.seq (.load 8 10 .in1) (.seq (.add 8 3 8 (.reg 9) (.reg 3)) (.seq (.store 8 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) .continue)))))))

/-- HOL `mc_add_loop_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_add_loop`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_add_loop_code_def"
  (words_as_type_indexed_bitvec)]
def mcAddLoopCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 1 (.op .add [(.var 1), (.const 1)])) (.seq (.assign 2 (.op .add [(.var 2), (.const 1)])) (.seq (.assign 3 (.const 0)) (.seq (mcAddLoop1Code width) (.seq (.assign 1 (.var 2)) (.seq (.assign 9 (.const 0)) (.seq (mcAddLoop2Code width) (.ite .equal 3 (.imm 0) (.seq (.delete [3]) .skip) (.seq (.assign 8 (.const 1)) (.seq (.store 8 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.delete [3]) .skip))))))))))))

/-- HOL `mc_add_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_add`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_add_code_def"
  (words_as_type_indexed_bitvec)]
def mcAddCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 2 (.op .sub [(.var 2), (.var 1)])) (.seq (mcAddLoopCode width) (.seq (.delete [3]) .skip)))

/-- HOL `mc_adj_cmp_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_adj_cmp`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_adj_cmp_code_def"
  (words_as_type_indexed_bitvec)]
def mcAdjCmpCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 0 (.reg 3) .skip (.seq (.assign 8 (.const 1)) (.ite .lower 3 (.reg 0) .skip (.seq (.assign 8 (.const 0)) .skip))))

/-- HOL `mc_single_mul_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_single_mul`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_single_mul_code_def"
  (words_as_type_indexed_bitvec)]
def mcSingleMulCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.mul 0 2 0 2) (.seq (.add 0 4 0 (.reg 1) (.imm 0)) (.seq (.add 2 4 2 (.imm 0) (.reg 4)) (.seq (.delete [4]) .skip))))

/-- HOL `mc_adjust_aux_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_adjust_aux`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_adjust_aux_code_def"
  (words_as_type_indexed_bitvec)]
def mcAdjustAuxCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [2, 3, 0, 4] (.ite .equal 9 (.reg 11) (.seq (.assign 0 (.var 12)) (.seq (.load 3 10 .out) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (mcAdjCmpCode width) (.seq (.delete [2, 3, 0, 4, 12, 1]) .skip))))) (.seq (.assign 0 (.var 6)) (.seq (.load 2 11 .in2) (.seq (mcSingleMulCode width) (.seq (.assign 1 (.var 12)) (.seq (.assign 12 (.var 2)) (.seq (.assign 2 (.var 0)) (.seq (.assign 0 (.var 7)) (.seq (mcSingleMulCode width) (.seq (.assign 1 (.var 12)) (.seq (.assign 12 (.var 2)) (.seq (.load 3 10 .out) (.seq (mcAdjCmpCode width) (.seq (.assign 11 (.op .add [(.var 11), (.const 1)])) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.delete [2, 3, 0, 4]) .continue)))))))))))))))))

/-- HOL `mc_calc_d_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_calc_d`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_calc_d_code_def"
  (words_as_type_indexed_bitvec)]
def mcCalcDCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .less 1 (.imm 0) (.seq (.delete [1]) .skip) (.seq (.assign 1 (.op .add [(.var 1), (.var 1)])) (.seq (.assign 2 (.op .add [(.var 2), (.var 2)])) .continue))))

/-- HOL `mc_cmp2_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_cmp2`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_cmp2_code_def"
  (words_as_type_indexed_bitvec)]
def mcCmp2Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 1 (.const 1)) (.ite .equal 2 (.reg 11) (.ite .equal 0 (.reg 10) (.seq (.assign 1 (.const 0)) .skip) (.ite .lower 10 (.reg 0) .skip (.seq (.assign 1 (.const 0)) .skip))) (.ite .lower 11 (.reg 2) .skip (.seq (.assign 1 (.const 0)) .skip))))

/-- HOL `mc_cmp3_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_cmp3`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_cmp3_code_def"
  (words_as_type_indexed_bitvec)]
def mcCmp3Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 0 (.const 1)) (.ite .equal 3 (.reg 11) (.ite .equal 2 (.reg 10) (.ite .equal 1 (.reg 9) (.seq (.assign 0 (.const 0)) .skip) (.ite .lower 9 (.reg 1) .skip (.seq (.assign 0 (.const 0)) .skip))) (.ite .lower 10 (.reg 2) .skip (.seq (.assign 0 (.const 0)) .skip))) (.ite .lower 11 (.reg 3) .skip (.seq (.assign 0 (.const 0)) .skip))))

/-- HOL `mc_cmp_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_cmp`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_cmp_code_def"
  (words_as_type_indexed_bitvec)]
def mcCmpCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [9, 8] (.ite .equal 10 (.imm 0) (.seq (.delete [9, 8]) .skip) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 8 10 .in1) (.seq (.load 9 10 .in2) (.ite .equal 8 (.reg 9) (.seq (.delete [9, 8]) .continue) (.ite .lower 8 (.reg 9) (.seq (.assign 10 (.const 1)) (.seq (.delete [9, 8]) .skip)) (.seq (.assign 10 (.const 2)) (.seq (.delete [9, 8]) .skip)))))))))

/-- HOL `mc_mul_by_single2_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_mul_by_single2`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_mul_by_single2_code_def"
  (words_as_type_indexed_bitvec)]
def mcMulBySingle2Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 0 (.var 6)) (.seq (.assign 1 (.const 0)) (.seq (.assign 2 (.var 7)) (.seq (mcSingleMulCode width) (.seq (.assign 12 (.var 0)) (.seq (.assign 0 (.var 6)) (.seq (.assign 1 (.var 2)) (.seq (.assign 2 (.var 8)) (.seq (mcSingleMulCode width) (.seq (.assign 3 (.var 2)) (.seq (.assign 2 (.var 0)) (.seq (.assign 1 (.var 12)) (.seq (.delete [12, 0, 4]) .skip)))))))))))))

/-- HOL `mc_cmp_mul2_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_cmp_mul2`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_cmp_mul2_code_def"
  (words_as_type_indexed_bitvec)]
def mcCmpMul2Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (mcMulBySingle2Code width) (.seq (mcCmp3Code width) (.seq (.delete [3, 2, 1, 12, 4]) .skip)))

/-- HOL `mc_compare_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_compare`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_compare_code_def"
  (words_as_type_indexed_bitvec)]
def mcCompareCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .lower 10 (.reg 11) (.seq (.assign 10 (.const 1)) (.seq (.delete [9, 8, 11]) .skip)) (.ite .lower 11 (.reg 10) (.seq (.assign 10 (.const 2)) (.seq (.delete [9, 8, 11]) .skip)) (.seq (mcCmpCode width) (.seq (.delete [9, 8, 11]) .skip))))

/-- HOL `mc_copy_down_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_copy_down`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_copy_down_code_def"
  (words_as_type_indexed_bitvec)]
def mcCopyDownCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [0] (.ite .equal 8 (.imm 0) (.seq (.delete [0, 11, 10, 8]) .skip) (.seq (.load 0 10 .out) (.seq (.assign 8 (.op .sub [(.var 8), (.const 1)])) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.store 0 11) (.seq (.assign 11 (.op .add [(.var 11), (.const 1)])) (.seq (.delete [0]) .continue))))))))

/-- HOL `mc_copy_over_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_copy_over`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_copy_over_code_def"
  (words_as_type_indexed_bitvec)]
def mcCopyOverCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [0] (.ite .equal 10 (.imm 0) (.seq (.delete [0, 10]) .skip) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 0 10 .in1) (.seq (.store 0 10) (.seq (.delete [0]) .continue))))))

/-- HOL `mc_mul_zero_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_mul_zero`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_mul_zero_code_def"
  (words_as_type_indexed_bitvec)]
def mcMulZeroCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .equal 10 (.imm 0) (.seq (.delete [0]) .skip) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.store 0 10) .continue))))

/-- HOL `mc_div0_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div0`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div0_code_def"
  (words_as_type_indexed_bitvec)]
def mcDiv0Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 6 (.var 0)) (.ite .equal 3 (.imm 0) (.seq (.assign 0 (.const 0)) (.seq (.delete [11, 10, 1]) .skip)) (.seq (.assign 11 (.var 0)) (.seq (.assign 10 (.var 1)) (.seq (.assign 0 (.const 0)) (.seq (mcMulZeroCode width) (.seq (.assign 10 (.var 11)) (.seq (mcCopyOverCode width) (.seq (.assign 0 (.var 1)) (.seq (.delete [11, 10, 1]) .skip))))))))))

/-- HOL `mc_single_div_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_single_div`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_single_div_code_def"
  (words_as_type_indexed_bitvec)]
def mcSingleDivCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.div 0 2 2 0 9) .skip)

/-- HOL `mc_simple_div_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_simple_div`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_simple_div_code_def"
  (words_as_type_indexed_bitvec)]
def mcSimpleDivCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [0] (.ite .equal 10 (.imm 0) (.seq (.delete [0]) .skip) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 0 10 .in1) (.seq (mcSingleDivCode width) (.seq (.store 0 10) (.seq (.delete [0]) .continue)))))))

/-- HOL `mc_div1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div1_code_def"
  (words_as_type_indexed_bitvec)]
def mcDiv1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 14 (.var 3)) (.seq (.assign 2 (.const 0)) (.seq (.assign 10 (.var 2)) (.seq (.load 9 10 .in2) (.seq (.assign 10 (.var 0)) (.seq (.assign 8 (.var 0)) (.seq (mcSimpleDivCode width) (.seq (.assign 6 (.const 0)) (.seq (.assign 0 (.var 8)) (.seq (.assign 3 (.var 14)) (.ite .equal 3 (.imm 0) (.ite .equal 2 (.imm 0) (.seq (.delete [8, 9, 10, 2, 14, 1]) .skip) (.seq (.assign 6 (.const 1)) (.seq (.delete [8, 9, 10, 2, 14, 1]) .skip))) (.seq (.assign 0 (.const 1)) (.seq (.assign 10 (.const 0)) (.seq (.store 2 10) (.ite .equal 2 (.imm 0) (.seq (.delete [8, 9, 10, 2, 14, 1]) .skip) (.seq (.assign 6 (.const 1)) (.seq (.delete [8, 9, 10, 2, 14, 1]) .skip)))))))))))))))))

/-- HOL `mc_fix_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_fix`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_fix_code_def"
  (words_as_type_indexed_bitvec)]
def mcFixCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .equal 10 (.imm 0) .skip (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 8 10 .out) (.ite .equal 8 (.imm 0) .continue (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) .skip))))))

/-- HOL `mc_simple_div1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_simple_div1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_simple_div1_code_def"
  (words_as_type_indexed_bitvec)]
def mcSimpleDiv1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [0] (.ite .equal 10 (.imm 0) (.seq (.delete [0]) .skip) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 0 10 .out) (.seq (mcSingleDivCode width) (.seq (.store 0 10) (.seq (.delete [0]) .continue)))))))

/-- HOL `mc_div2_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div2`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div2_code_def"
  (words_as_type_indexed_bitvec)]
def mcDiv2Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 9 (.var 7)) (.seq (.assign 2 (.const 0)) (.seq (mcSimpleDiv1Code width) (.seq (.assign 9 (.var 11)) (.seq (.assign 10 (.var 9)) (.seq (.assign 7 (.var 8)) (.seq (mcFixCode width) (.seq (.assign 6 (.var 10)) (.seq (.assign 10 (.var 9)) (.seq (.assign 3 (.var 18)) (.seq (.assign 8 (.var 7)) (.ite .equal 3 (.imm 0) (.seq (.assign 11 (.const 0)) (.seq (mcCopyDownCode width) (.seq (.assign 0 (.var 7)) (.seq (.delete [2, 9, 18, 11, 10, 8, 7]) .skip)))) (.seq (.assign 0 (.var 9)) (.seq (.delete [2, 9, 18, 11, 10, 8, 7]) .skip))))))))))))))

/-- HOL `mc_div_adjust_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_adjust`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_adjust_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivAdjustCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 1 (.const 0)) (.seq (.assign 8 (.var 1)) (.seq (.assign 11 (.var 1)) (.seq (.assign 12 (.var 1)) (.seq (mcAdjustAuxCode width) (.ite .equal 7 (.imm 0) (.seq (.delete [8, 2, 3, 0, 4, 12, 1]) .skip) (.ite .equal 8 (.imm 0) (.seq (.delete [8, 2, 3, 0, 4, 12, 1]) .skip) (.seq (.assign 7 (.op .sub [(.var 7), (.const 1)])) (.seq (.delete [8, 2, 3, 0, 4, 12, 1]) .skip)))))))))

/-- HOL `mc_div_r1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_r1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_r1_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivR1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .lower 2 (.reg 1) (.seq (.div 0 2 2 0 1) .skip) (.seq (.assign 0 (.const 0)) (.seq (.assign 0 (.op .xor [(.var 0), (.op .sub [(.const 0), (.const 1)])])) .skip)))

/-- HOL `mc_single_mul_add_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_single_mul_add`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_single_mul_add_code_def"
  (words_as_type_indexed_bitvec)]
def mcSingleMulAddCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.mul 0 2 0 2) (.seq (.add 0 4 0 (.reg 1) (.imm 0)) (.seq (.add 2 4 2 (.imm 0) (.reg 4)) (.seq (.add 0 4 0 (.reg 3) (.imm 0)) (.seq (.add 2 4 2 (.imm 0) (.reg 4)) (.seq (.delete [4]) .skip))))))

/-- HOL `mc_sub1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_sub1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_sub1_code_def"
  (words_as_type_indexed_bitvec)]
def mcSub1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 6 (.imm 0) .skip (.seq (.assign 6 (.op .sub [(.var 6), (.const 1)])) .skip))

/-- HOL `mc_div_test_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_test`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_test_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivTestCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [0, 3, 2, 1, 12, 4] (.seq (mcCmpMul2Code width) (.ite .equal 0 (.imm 0) (.seq (.delete [0, 3, 2, 1, 12, 4]) .skip) (.seq (mcSub1Code width) (.seq (.assign 0 (.var 6)) (.seq (.assign 1 (.const 0)) (.seq (.assign 2 (.var 8)) (.seq (.assign 3 (.var 1)) (.seq (mcSingleMulAddCode width) (.seq (.assign 2 (.op .add [(.var 2), (.const 1)])) (.seq (mcCmp2Code width) (.ite .equal 1 (.imm 0) (.seq (.delete [0, 3, 2, 1, 12, 4]) .skip) (.seq (.delete [0, 3, 2, 1, 12, 4]) .continue)))))))))))))

/-- HOL `mc_div_guess_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_guess`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_guess_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivGuessCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 0 (.var 10)) (.seq (.assign 1 (.var 8)) (.seq (.assign 2 (.var 11)) (.seq (mcDivR1Code width) (.seq (.assign 6 (.var 0)) (.seq (mcDivTestCode width) (.seq (.delete [0, 3, 2, 1, 12, 4]) .skip)))))))

/-- HOL `mc_div_sub_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_sub`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_sub_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivSubCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.sub 3 8 3 (.reg 0) (.reg 8)) .skip)

/-- HOL `mc_div_sub_loop_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_sub_loop`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_sub_loop_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivSubLoopCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [2, 3, 0, 4] (.ite .equal 9 (.reg 11) (.seq (.assign 0 (.var 12)) (.seq (.load 3 10 .out) (.seq (mcDivSubCode width) (.seq (.assign 1 (.var 3)) (.seq (.store 1 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.delete [2, 3, 0, 4, 12, 8, 1]) .skip))))))) (.seq (.assign 0 (.var 6)) (.seq (.load 2 11 .in2) (.seq (mcSingleMulCode width) (.seq (.assign 1 (.var 12)) (.seq (.assign 12 (.var 2)) (.seq (.assign 2 (.var 0)) (.seq (.assign 0 (.var 7)) (.seq (mcSingleMulCode width) (.seq (.assign 1 (.var 12)) (.seq (.assign 12 (.var 2)) (.seq (.load 3 10 .out) (.seq (mcDivSubCode width) (.seq (.assign 0 (.var 1)) (.seq (.assign 1 (.var 3)) (.seq (.store 1 10) (.seq (.assign 1 (.var 0)) (.seq (.assign 11 (.op .add [(.var 11), (.const 1)])) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.delete [2, 3, 0, 4]) .continue)))))))))))))))))))))

/-- HOL `mc_div_loop_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_loop`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_loop_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivLoopCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [16, 6, 2, 3, 0, 4, 12, 8, 1] (.ite .equal 10 (.imm 0) (.seq (.delete [16, 6, 2, 3, 0, 4, 12, 8, 1]) .skip) (.seq (.assign 6 (.var 14)) (.seq (.assign 3 (.var 15)) (.seq (.assign 14 (.var 7)) (.seq (.assign 15 (.var 9)) (.seq (.assign 16 (.var 10)) (.seq (.assign 10 (.op .add [(.var 10), (.var 9)])) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 0 10 .out) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 1 10 .out) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 2 10 .out) (.seq (.assign 11 (.var 0)) (.seq (.assign 10 (.var 1)) (.seq (.assign 9 (.var 2)) (.seq (.assign 7 (.var 3)) (.seq (.assign 8 (.var 6)) (.seq (mcDivGuessCode width) (.seq (.assign 0 (.var 6)) (.seq (.assign 6 (.var 14)) (.seq (.assign 9 (.var 15)) (.seq (.assign 10 (.var 16)) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.assign 15 (.var 7)) (.seq (.assign 14 (.var 8)) (.seq (.assign 7 (.var 0)) (.seq (mcDivAdjustCode width) (.seq (.assign 10 (.op .sub [(.var 10), (.var 9)])) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.assign 1 (.const 0)) (.seq (.assign 8 (.var 1)) (.seq (.assign 8 (.const 1)) (.seq (.assign 11 (.var 1)) (.seq (.assign 12 (.var 1)) (.seq (mcDivSubLoopCode width) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.store 7 10) (.seq (.assign 10 (.op .sub [(.var 10), (.var 9)])) (.seq (.assign 7 (.var 6)) (.seq (.delete [16, 6, 2, 3, 0, 4, 12, 8, 1]) .continue))))))))))))))))))))))))))))))))))))))))))

/-- HOL `mc_mul_by_single_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_mul_by_single`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_mul_by_single_code_def"
  (words_as_type_indexed_bitvec)]
def mcMulBySingleCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [3, 0, 2, 4] (.ite .equal 9 (.reg 11) (.seq (.store 1 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.delete [3, 0, 2, 4, 11]) .skip))) (.seq (.load 2 11 .in1) (.seq (.assign 0 (.var 8)) (.seq (.assign 3 (.const 0)) (.seq (mcSingleMulAddCode width) (.seq (.store 0 10) (.seq (.assign 1 (.var 2)) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.assign 11 (.op .add [(.var 11), (.const 1)])) (.seq (.delete [3, 0, 2, 4]) .continue)))))))))))

/-- HOL `mc_top_two_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_top_two`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_top_two_code_def"
  (words_as_type_indexed_bitvec)]
def mcTopTwoCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [2, 4] (.ite .equal 9 (.reg 11) (.seq (.assign 1 (.var 3)) (.seq (.delete [2, 4, 3]) .skip)) (.seq (.assign 3 (.var 0)) (.seq (.load 2 11 .in2) (.seq (.assign 0 (.var 8)) (.seq (mcSingleMulCode width) (.seq (.assign 1 (.var 2)) (.seq (.assign 11 (.op .add [(.var 11), (.const 1)])) (.seq (.delete [2, 4]) .continue)))))))))

/-- HOL `mc_div3_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div3`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div3_code_def"
  (words_as_type_indexed_bitvec)]
def mcDiv3Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 1 (.const 0)) (.seq (.assign 8 (.var 2)) (.seq (.assign 10 (.var 1)) (.seq (.assign 11 (.var 1)) (.seq (mcMulBySingleCode width) (.seq (.assign 1 (.const 0)) (.seq (.store 1 10) (.seq (.assign 0 (.const 0)) (.seq (.assign 1 (.var 0)) (.seq (.assign 3 (.var 0)) (.seq (.assign 11 (.var 0)) (.seq (.assign 9 (.var 7)) (.seq (mcTopTwoCode width) (.seq (.assign 7 (.var 8)) (.seq (.assign 11 (.var 9)) (.seq (.assign 10 (.var 19)) (.seq (.assign 10 (.op .sub [(.var 10), (.var 9)])) (.seq (.assign 10 (.op .add [(.var 10), (.const 2)])) (.seq (.assign 14 (.var 0)) (.seq (.assign 15 (.var 1)) (.seq (.assign 17 (.var 10)) (.seq (mcDivLoopCode width) (.seq (.assign 8 (.var 17)) (.seq (.assign 11 (.var 9)) (.seq (.assign 10 (.var 9)) (.seq (mcDiv2Code width) (.seq (.delete [17, 15, 14, 16, 4, 12, 1, 11, 10, 8, 19, 18, 9, 7, 2]) .skip)))))))))))))))))))))))))))

/-- HOL `mc_div_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .lower 0 (.reg 1) (.seq (mcDiv0Code width) (.seq (.delete [17, 15, 14, 16, 4, 12, 11, 10, 8, 19, 18, 9, 7, 2, 1]) .skip)) (.ite .equal 1 (.imm 1) (.seq (mcDiv1Code width) (.seq (.delete [17, 15, 14, 16, 4, 12, 11, 10, 8, 19, 18, 9, 7, 2, 1]) .skip)) (.seq (.assign 18 (.var 3)) (.seq (.assign 19 (.var 0)) (.seq (.assign 7 (.var 1)) (.seq (.assign 9 (.var 0)) (.seq (.assign 10 (.var 1)) (.seq (.assign 10 (.op .sub [(.var 10), (.const 1)])) (.seq (.load 1 10 .in2) (.seq (.assign 2 (.const 1)) (.seq (mcCalcDCode width) (.seq (mcDiv3Code width) (.seq (.delete [17, 15, 14, 16, 4, 12, 11, 10, 8, 19, 18, 9, 7, 2, 1]) .skip)))))))))))))

/-- HOL `mc_div_sub_aux1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_sub_aux1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_sub_aux1_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivSubAux1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .equal 1 (.imm 1) (.seq (.assign 1 (.const 0)) .skip) (.seq (.assign 1 (.op .sub [(.var 1), (.const 1)])) (.seq (.load 8 10 .in2) (.seq (.load 9 10 .out) (.seq (.sub 8 4 8 (.reg 9) (.reg 4)) (.seq (.store 8 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) .continue))))))))

/-- HOL `mc_div_sub_aux_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_sub_aux`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_sub_aux_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivSubAuxCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 10 (.const 0)) (.seq (.assign 1 (.op .add [(.var 1), (.const 1)])) (.seq (.assign 4 (.const 1)) (.seq (mcDivSubAux1Code width) .skip))))

/-- HOL `mc_div_sub1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_sub1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_sub1_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivSub1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (mcDivSubAuxCode width) (.seq (.delete [4]) .skip))

/-- HOL `mc_div_sub_call_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_div_sub_call`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_div_sub_call_code_def"
  (words_as_type_indexed_bitvec)]
def mcDivSubCallCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 2 (.imm 0) (.seq (.delete [10, 3, 9, 8, 4, 2, 1]) .skip) (.ite .equal 6 (.imm 0) (.seq (.delete [10, 3, 9, 8, 4, 2, 1]) .skip) (.seq (.assign 8 (.var 6)) (.seq (.assign 9 (.var 6)) (.seq (.assign 3 (.var 1)) (.seq (mcDivSub1Code width) (.seq (.assign 10 (.var 3)) (.seq (mcFixCode width) (.seq (.assign 6 (.var 10)) (.seq (.delete [10, 3, 9, 8, 4, 2, 1]) .skip))))))))))

/-- HOL `mc_fac_final_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_fac_final`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_fac_final_code_def"
  (words_as_type_indexed_bitvec)]
def mcFacFinalCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 1 (.op .add [(.var 1), (.var 2)])) (.seq (.delete [2]) .skip))

/-- HOL `mc_fac_init_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_fac_init`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_fac_init_code_def"
  (words_as_type_indexed_bitvec)]
def mcFacInitCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .lower 1 (.imm 2) (.seq (.assign 0 (.const 0)) (.seq (.assign 2 (.const 0)) (.seq (.assign 3 (.const 0)) .skip))) (.seq (.assign 0 (.const 1)) (.seq (.assign 2 (.op .sub [(.var 1), (.const 1)])) (.seq (.assign 3 (.op .sub [(.var 1), (.const 2)])) .skip))))

/-- HOL `mc_fac_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_fac`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_fac_code_def"
  (words_as_type_indexed_bitvec)]
def mcFacCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop true [3, 0, 2] (.seq (mcFacInitCode width) (.ite .equal 0 (.imm 0) (.seq (.delete [3, 0, 2]) .skip) (.seq (.assign 1 (.var 2)) (.seq (.recurse [2, 3] []) (.seq (.assign 2 (.var 1)) (.seq (.assign 1 (.var 3)) (.seq (.recurse [2] []) (.seq (mcFacFinalCode width) (.seq (.delete [3, 0, 2]) .skip))))))))))

/-- HOL `mc_iadd1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_iadd1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_iadd1_code_def"
  (words_as_type_indexed_bitvec)]
def mcIadd1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 0 (.const 0)) (.ite .lower 1 (.reg 2) (.seq .swap (.seq (.assign 0 (.const 1)) (.seq (.delete [8]) .skip))) (.seq (.assign 8 (.var 1)) (.seq (.assign 1 (.var 2)) (.seq (.assign 2 (.var 8)) (.seq (.delete [8]) .skip))))))

/-- HOL `mc_iadd2_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_iadd2`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_iadd2_code_def"
  (words_as_type_indexed_bitvec)]
def mcIadd2Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 0 (.const 0)) (.ite .equal 10 (.imm 1) (.seq .swap (.seq (.assign 12 (.op .xor [(.var 12), (.const 1)])) (.seq (.assign 0 (.const 1)) (.seq (.delete [8, 10]) .skip)))) (.seq (.assign 8 (.var 1)) (.seq (.assign 1 (.var 2)) (.seq (.assign 2 (.var 8)) (.seq (.delete [8, 10]) .skip))))))

/-- HOL `mc_iadd3_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_iadd3`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_iadd3_code_def"
  (words_as_type_indexed_bitvec)]
def mcIadd3Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 0 (.imm 0) (.seq (.delete [0]) .skip) (.seq .swap (.seq (.delete [0]) .skip)))

/-- HOL `mc_sub_loop1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_sub_loop1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_sub_loop1_code_def"
  (words_as_type_indexed_bitvec)]
def mcSubLoop1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .equal 1 (.imm 1) (.seq (.assign 1 (.const 0)) .skip) (.seq (.assign 1 (.op .sub [(.var 1), (.const 1)])) (.seq (.load 8 10 .in1) (.seq (.load 9 10 .in2) (.seq (.sub 8 3 8 (.reg 9) (.reg 3)) (.seq (.store 8 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) .continue))))))))

/-- HOL `mc_sub_loop2_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_sub_loop2`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_sub_loop2_code_def"
  (words_as_type_indexed_bitvec)]
def mcSubLoop2Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [] (.ite .equal 1 (.imm 1) (.seq (.assign 1 (.const 0)) .skip) (.seq (.assign 1 (.op .sub [(.var 1), (.const 1)])) (.seq (.load 8 10 .in1) (.seq (.sub 8 3 8 (.reg 9) (.reg 3)) (.seq (.store 8 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) .continue)))))))

/-- HOL `mc_sub_loop_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_sub_loop`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_sub_loop_code_def"
  (words_as_type_indexed_bitvec)]
def mcSubLoopCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 1 (.op .add [(.var 1), (.const 1)])) (.seq (.assign 2 (.op .add [(.var 2), (.const 1)])) (.seq (.assign 3 (.const 1)) (.seq (.assign 8 (.op .sub [(.var 8), (.const 0)])) (.seq (mcSubLoop1Code width) (.seq (.assign 1 (.var 2)) (.seq (.assign 9 (.const 0)) (.seq (mcSubLoop2Code width) (.seq (.delete [3]) .skip)))))))))

/-- HOL `mc_sub_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_sub`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_sub_code_def"
  (words_as_type_indexed_bitvec)]
def mcSubCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 2 (.op .sub [(.var 2), (.var 1)])) (.seq (mcSubLoopCode width) (.seq (mcFixCode width) (.seq (.delete [3]) .skip))))

/-- HOL `mc_iadd_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_iadd`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_iadd_code_def"
  (words_as_type_indexed_bitvec)]
def mcIaddCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 10 (.var 1)) (.seq (.assign 10 (.op .and [(.var 10), (.const 1)])) (.seq (.assign 11 (.var 2)) (.seq (.assign 11 (.op .and [(.var 11), (.const 1)])) (.ite .equal 10 (.reg 11) (.seq (.assign 1 (.shift .lsr (.var 1) (.const 1))) (.seq (.assign 2 (.shift .lsr (.var 2) (.const 1))) (.seq (mcIadd1Code width) (.seq (.assign 8 (.const 0)) (.seq (.assign 9 (.var 8)) (.seq (.assign 10 (.var 8)) (.seq (mcAddCode width) (.seq (mcIadd3Code width) (.seq (.assign 10 (.shift .lsl (.var 10) (.const 1))) (.seq (.assign 10 (.op .add [(.var 10), (.var 11)])) (.seq (.delete [12, 9, 11, 0, 8, 3, 2, 1]) .skip))))))))))) (.seq (.assign 12 (.var 10)) (.seq (.assign 10 (.var 1)) (.seq (.assign 10 (.shift .lsr (.var 10) (.const 1))) (.seq (.assign 11 (.var 2)) (.seq (.assign 11 (.shift .lsr (.var 11) (.const 1))) (.seq (mcCompareCode width) (.ite .equal 10 (.imm 0) (.seq (.delete [12, 9, 11, 0, 8, 3, 2, 1]) .skip) (.seq (mcIadd2Code width) (.seq (.assign 8 (.const 0)) (.seq (.assign 9 (.var 8)) (.seq (.assign 10 (.var 8)) (.seq (.assign 1 (.shift .lsr (.var 1) (.const 1))) (.seq (.assign 2 (.shift .lsr (.var 2) (.const 1))) (.seq (mcSubCode width) (.seq (mcIadd3Code width) (.seq (.assign 10 (.shift .lsl (.var 10) (.const 1))) (.seq (.assign 10 (.op .add [(.var 10), (.var 12)])) (.seq (.delete [12, 9, 11, 0, 8, 3, 2, 1]) .skip)))))))))))))))))))))))

/-- HOL `mc_idiv_mod_header_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_idiv_mod_header`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_idiv_mod_header_code_def"
  (words_as_type_indexed_bitvec)]
def mcIdivModHeaderCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 6 (.imm 0) (.seq (.delete [11]) .skip) (.seq (.assign 6 (.shift .lsl (.var 6) (.const 1))) (.ite .test 11 (.imm 1) (.seq (.delete [11]) .skip) (.seq (.assign 6 (.op .add [(.var 6), (.const 1)])) (.seq (.delete [11]) .skip)))))

/-- HOL `mc_idiv0_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_idiv0`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_idiv0_code_def"
  (words_as_type_indexed_bitvec)]
def mcIdiv0Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 3 (.imm 0) (.seq (.assign 10 (.var 0)) (.seq (.assign 8 (.var 10)) (.seq (mcFixCode width) (.seq (.assign 11 (.var 10)) (.seq (.assign 2 (.var 20)) (.seq (.assign 3 (.var 2)) (.seq (mcAdd1CallCode width) (.ite .equal 11 (.imm 0) (.seq (.delete [10, 9, 8, 4, 2, 1, 20, 6, 3, 0]) .skip) (.seq (.assign 11 (.shift .lsl (.var 11) (.const 1))) (.seq (.assign 11 (.op .add [(.var 11), (.var 3)])) (.seq (.delete [10, 9, 8, 4, 2, 1, 20, 6, 3, 0]) .skip))))))))))) (.seq (.assign 2 (.var 20)) (.seq (.assign 1 (.var 11)) (.seq (.assign 1 (.shift .lsr (.var 1) (.const 1))) (.seq (mcDivSubCallCode width) (.seq (mcIdivModHeaderCode width) (.seq (.assign 11 (.var 6)) (.seq (.delete [10, 9, 8, 4, 2, 1, 20, 6, 3, 0]) .skip))))))))

/-- HOL `mc_idiv_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_idiv`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_idiv_code_def"
  (words_as_type_indexed_bitvec)]
def mcIdivCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 0 (.shift .lsr (.var 10) (.const 1))) (.seq (.assign 1 (.shift .lsr (.var 11) (.const 1))) (.seq (.assign 10 (.op .xor [(.var 10), (.var 11)])) (.seq (.assign 10 (.op .and [(.var 10), (.const 1)])) (.seq (.assign 20 (.var 10)) (.seq (.assign 21 (.var 11)) (.seq (mcDivCode width) (.seq (.assign 11 (.var 21)) (.seq (mcIdiv0Code width) (.seq (.delete [21, 17, 15, 14, 16, 12, 19, 18, 7, 9, 8, 4, 2, 1, 20, 6, 0, 10, 3]) .skip))))))))))

/-- HOL `mc_imul1_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_imul1`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_imul1_code_def"
  (words_as_type_indexed_bitvec)]
def mcImul1Code (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 10 (.reg 11) (.seq (.assign 13 (.const 0)) .skip) (.seq (.assign 13 (.const 1)) .skip))

/-- HOL `mc_mul_pass_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_mul_pass`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_mul_pass_code_def"
  (words_as_type_indexed_bitvec)]
def mcMulPassCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [0, 2, 3, 4] (.ite .equal 9 (.reg 11) (.seq (.store 1 10) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.delete [0, 2, 3, 4, 11, 8]) .skip))) (.seq (.load 3 10 .out) (.seq (.load 2 11 .in2) (.seq (.assign 0 (.var 8)) (.seq (mcSingleMulAddCode width) (.seq (.store 0 10) (.seq (.assign 1 (.var 2)) (.seq (.assign 10 (.op .add [(.var 10), (.const 1)])) (.seq (.assign 11 (.op .add [(.var 11), (.const 1)])) (.seq (.delete [0, 2, 3, 4]) .continue)))))))))))

/-- HOL `mc_mul_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_mul`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_mul_code_def"
  (words_as_type_indexed_bitvec)]
def mcMulCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.loop false [1, 0, 2, 3, 4, 11, 8] (.ite .equal 7 (.imm 0) (.seq (.assign 10 (.op .add [(.var 10), (.var 9)])) (.seq (.delete [1, 0, 2, 3, 4, 11, 8, 12, 9, 7]) .skip)) (.seq (.assign 7 (.op .sub [(.var 7), (.const 1)])) (.seq (.load 8 12 .in1) (.seq (.assign 12 (.op .add [(.var 12), (.const 1)])) (.seq (.assign 11 (.const 0)) (.seq (.assign 1 (.var 11)) (.seq (mcMulPassCode width) (.seq (.assign 10 (.op .sub [(.var 10), (.var 9)])) (.seq (.delete [1, 0, 2, 3, 4, 11, 8]) .continue))))))))))

/-- HOL `mc_imul_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_imul`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_imul_code_def"
  (words_as_type_indexed_bitvec)]
def mcImulCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (.assign 10 (.const 0)) (.ite .equal 1 (.imm 0) (.seq (.delete [13, 0, 3, 4, 11, 8, 12, 9, 7, 2, 1]) .skip) (.ite .equal 2 (.imm 0) (.seq (.delete [13, 0, 3, 4, 11, 8, 12, 9, 7, 2, 1]) .skip) (.seq (.assign 0 (.const 0)) (.seq (.assign 10 (.var 2)) (.seq (.assign 10 (.shift .lsr (.var 10) (.const 1))) (.seq (mcMulZeroCode width) (.seq (.assign 10 (.var 1)) (.seq (.assign 10 (.op .and [(.var 10), (.const 1)])) (.seq (.assign 11 (.var 2)) (.seq (.assign 11 (.op .and [(.var 11), (.const 1)])) (.seq (mcImul1Code width) (.seq (.assign 7 (.var 1)) (.seq (.assign 7 (.shift .lsr (.var 7) (.const 1))) (.seq (.assign 9 (.var 2)) (.seq (.assign 9 (.shift .lsr (.var 9) (.const 1))) (.seq (.assign 10 (.const 0)) (.seq (.assign 12 (.const 0)) (.seq (mcMulCode width) (.seq (.assign 8 (.const 0)) (.seq (mcFixCode width) (.seq (.assign 10 (.shift .lsl (.var 10) (.const 1))) (.seq (.assign 10 (.op .add [(.var 10), (.var 13)])) (.seq (.delete [13, 0, 3, 4, 11, 8, 12, 9, 7, 2, 1]) .skip))))))))))))))))))))))))

/-- HOL `mc_isub_flip_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_isub_flip`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_isub_flip_code_def"
  (words_as_type_indexed_bitvec)]
def mcIsubFlipCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .equal 3 (.imm 0) .skip (.seq (.assign 1 (.op .xor [(.var 1), (.const 1)])) .skip))

/-- HOL `mc_iop_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_iop`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_iop_code_def"
  (words_as_type_indexed_bitvec)]
def mcIopCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.ite .lower 3 (.imm 2) (.seq (mcIsubFlipCode width) (.seq (.assign 2 (.var 1)) (.seq (.assign 1 (.var 0)) (.seq (mcIaddCode width) (.seq (.delete [21, 17, 15, 14, 16, 19, 18, 20, 6, 13, 4, 11, 8, 12, 9, 7, 2, 3, 1, 0]) .skip))))) (.ite .equal 3 (.imm 4) (.seq (.assign 2 (.var 1)) (.seq (.assign 1 (.var 0)) (.seq (mcImulCode width) (.seq (.delete [21, 17, 15, 14, 16, 19, 18, 20, 6, 13, 4, 11, 8, 12, 9, 7, 2, 3, 1, 0]) .skip)))) (.seq (.assign 3 (.op .sub [(.var 3), (.const 5)])) (.seq (.assign 10 (.var 0)) (.seq (.assign 11 (.var 1)) (.seq (mcIdivCode width) (.seq (.assign 10 (.var 11)) (.seq (.delete [21, 17, 15, 14, 16, 19, 18, 20, 6, 13, 4, 11, 8, 12, 9, 7, 2, 3, 1, 0]) .skip))))))))

/-- HOL `mc_use_fac_code`, defined by `to_deep` (`Define`) when translating the
shallow `mc_use_fac`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mc_use_fac_code_def"
  (words_as_type_indexed_bitvec)]
def mcUseFacCode (width : Nat) [NeZero width] : Mini (BitVec width) :=
  (.seq (mcFacCode width) (.seq (.assign 0 (.var 1)) (.seq (.delete [3, 2, 1]) .skip)))

end Flapjack.Compiler.Backend.WordBignum
