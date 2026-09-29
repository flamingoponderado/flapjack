(*
  Direct HOL source proof plus HOL-EVAL result fixture for NaN-input and
  invalid-operation branches of binary64 add/sub/mul/div/mul_add in
  HOL/src/floating-point/binary_ieeeScript.sml:587-722. The payload of
  float_some_qnan (binary_ieeeScript.sml:495-499) is unspecified; only
  float_is_nan and float_is_signalling are observed. The fp64 encoding comes
  from HOL/src/floating-point/machine_ieeeScript.sml.
*)
load "machine_ieeeTheory";
load "binary_ieeeLib";
open HolKernel Parse boolLib bossLib machine_ieeeTheory binary_ieeeTheory;

val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_add_def,
  fp64_sub_def, fp64_mul_def, fp64_div_def, fp64_mul_add_def];

val qnan_classification = prove
  (``!fp_op.
      (float_is_nan (float_some_qnan fp_op),
       float_is_signalling (float_some_qnan fp_op)) = (T, F)``,
   simp [some_nan_properties]);

(* The kernel proves this classification directly from
   binary_ieeeTheory.some_nan_properties.  The operation EVAL rows below
   identify the exact float_some_qnan branch; this theorem establishes its
   NaN/non-signalling classification without selecting or observing payload. *)
val _ = print "source_qnan_classification=";
val _ = print_thm qnan_classification;
val _ = print "\n";

fun print_result label result =
  (print (label ^ "="); print_thm (EVAL result); print "\n");

val qnan = ``0x7FF8000000000000w : word64``;
val one = ``0x3FF0000000000000w : word64``;
val pz = ``0x0w : word64``;
val pinf = ``0x7FF0000000000000w : word64``;
val ninf = ``0xFFF0000000000000w : word64``;

val _ = print_result "add_qnan_input" ``fp64_add roundTiesToEven ^qnan ^one``;
val _ = print_result "sub_qnan_input" ``fp64_sub roundTiesToEven ^qnan ^one``;
val _ = print_result "mul_qnan_input" ``fp64_mul roundTiesToEven ^qnan ^one``;
val _ = print_result "div_qnan_input" ``fp64_div roundTiesToEven ^qnan ^one``;
val _ = print_result "fma_qnan_input" ``fp64_mul_add roundTiesToEven ^one ^one ^qnan``;

val _ = print_result "add_invalid_infinities" ``fp64_add roundTiesToEven ^pinf ^ninf``;
val _ = print_result "sub_invalid_infinities" ``fp64_sub roundTiesToEven ^pinf ^pinf``;
val _ = print_result "mul_invalid_inf_zero" ``fp64_mul roundTiesToEven ^pinf ^pz``;
val _ = print_result "div_invalid_zero_zero" ``fp64_div roundTiesToEven ^pz ^pz``;
val _ = print_result "div_invalid_inf_inf" ``fp64_div roundTiesToEven ^pinf ^ninf``;
val _ = print_result "fma_invalid_inf_zero" ``fp64_mul_add roundTiesToEven ^pinf ^pz ^one``;
val _ = print_result "fma_invalid_opposed_infinities" ``fp64_mul_add roundTiesToEven ^pinf ^one ^ninf``;
