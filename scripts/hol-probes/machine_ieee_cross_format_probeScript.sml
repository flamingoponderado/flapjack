load "machine_ieeeTheory"; load "binary_ieeeLib"; load "wordsLib"; load "bitstringLib";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory;
val _ = Globals.max_print_depth := 1000;
val _ = Parse.temp_remove_user_printer ("num.numeral_computations", mk_var("n", numSyntax.num));
val () = computeLib.add_funs [convert_def, fp32_to_fp64_with_flags_def,
 fp64_to_fp32_with_flags_def, fp32_to_fp64_def, fp64_to_fp32_def,
 fp32_to_float_def, fp64_to_float_def, float_to_fp32_def, float_to_fp64_def,
 real_to_fp32_with_flags_def, real_to_fp64_with_flags_def];
val conv = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV THENC EVAL;
fun observe label tm = let val th = conv tm in
 if null (hyp th) then (print(label ^ "="); print_term(rhs(concl th)); print "\n")
 else raise Fail (label ^ " has assumptions") end;
val _ = print "source_convert="; val _ = print_thm convert_def; val _ = print "\n";
val _ = observe "widen_pinf" ``fp32_to_fp64_with_flags (0x7f800000w : word32)``;
val _ = observe "widen_ninf" ``fp32_to_fp64_with_flags (0xff800000w : word32)``;
val _ = observe "widen_qnan" ``FST (fp32_to_fp64_with_flags (0x7fc00000w : word32))``;
val _ = observe "widen_snan" ``FST (fp32_to_fp64_with_flags (0x7f800001w : word32))``;
val _ = observe "narrow_pinf" ``fp64_to_fp32_with_flags roundTiesToEven (0x7ff0000000000000w : word64)``;
val _ = observe "narrow_ninf" ``fp64_to_fp32_with_flags roundTiesToEven (0xfff0000000000000w : word64)``;
val _ = observe "narrow_qnan" ``FST (fp64_to_fp32_with_flags roundTiesToEven (0x7ff8000000000000w : word64))``;
val _ = observe "narrow_snan" ``FST (fp64_to_fp32_with_flags roundTiesToEven (0x7ff0000000000001w : word64))``;
val _ = observe "widen_zero" ``fp32_to_fp64_with_flags (0w : word32)``;
val _ = observe "widen_one" ``fp32_to_fp64_with_flags (0x3f800000w : word32)``;
val _ = observe "widen_min_subnormal" ``fp32_to_fp64_with_flags (1w : word32)``;
val _ = observe "narrow_zero" ``fp64_to_fp32_with_flags roundTiesToEven (0w : word64)``;
val _ = observe "narrow_one" ``fp64_to_fp32_with_flags roundTiesToEven (0x3ff0000000000000w : word64)``;
val _ = observe "narrow_tie_even" ``fp64_to_fp32_with_flags roundTiesToEven (0x3ff0000010000000w : word64)``;
