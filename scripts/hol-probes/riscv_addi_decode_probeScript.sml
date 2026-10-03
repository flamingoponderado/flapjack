load "preamble"; load "riscvTheory";
open HolKernel Parse bossLib preamble riscvTheory;
val _ = computeLib.add_funs [Encode_def, Itype_def, opc_def, Decode_def, boolify32_def];
val _ = Globals.linewidth := 1000000;
(* Original ground oracle evidence; the unrestricted composition is proved in
   Lean and source-reviewed separately. These finite rows are not equivalence. *)
fun out label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))); print "\n");
val _ = out "addi_decode_zero" ``Decode (Encode (ArithI (ADDI (0w,0w,0w)))) = ArithI (ADDI (0w,0w,0w))``;
val _ = out "addi_decode_all_ones" ``Decode (Encode (ArithI (ADDI (31w,31w,4095w)))) = ArithI (ADDI (31w,31w,4095w))``;
val _ = out "addi_decode_sign_bit" ``Decode (Encode (ArithI (ADDI (1w,0w,2048w)))) = ArithI (ADDI (1w,0w,2048w))``;
val _ = out "addi_decode_positive_max" ``Decode (Encode (ArithI (ADDI (0w,31w,2047w)))) = ArithI (ADDI (0w,31w,2047w))``;
val _ = OS.Process.exit OS.Process.success;
