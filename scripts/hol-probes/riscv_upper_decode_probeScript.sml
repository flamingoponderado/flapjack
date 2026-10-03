load "preamble"; load "riscvTheory";
open HolKernel Parse bossLib preamble riscvTheory;
val _ = computeLib.add_funs [Encode_def, Utype_def, opc_def, Decode_def, boolify32_def];
val _ = Globals.linewidth := 1000000;
(* Finite original boundaries only; unrestricted Lean proofs and source
   comparison are separate obligations. No exhaustive equivalence claim. *)
fun out label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))); print "\n");
val _ = out "lui_decode_zero" ``Decode (Encode (ArithI (LUI (0w,0w)))) = ArithI (LUI (0w,0w))``;
val _ = out "lui_decode_all_ones" ``Decode (Encode (ArithI (LUI (31w,1048575w)))) = ArithI (LUI (31w,1048575w))``;
val _ = out "lui_decode_sign_bit" ``Decode (Encode (ArithI (LUI (1w,524288w)))) = ArithI (LUI (1w,524288w))``;
val _ = out "lui_decode_positive_max" ``Decode (Encode (ArithI (LUI (0w,524287w)))) = ArithI (LUI (0w,524287w))``;
val _ = out "auipc_decode_zero" ``Decode (Encode (ArithI (AUIPC (0w,0w)))) = ArithI (AUIPC (0w,0w))``;
val _ = out "auipc_decode_all_ones" ``Decode (Encode (ArithI (AUIPC (31w,1048575w)))) = ArithI (AUIPC (31w,1048575w))``;
val _ = out "auipc_decode_sign_bit" ``Decode (Encode (ArithI (AUIPC (1w,524288w)))) = ArithI (AUIPC (1w,524288w))``;
val _ = out "auipc_decode_positive_max" ``Decode (Encode (ArithI (AUIPC (0w,524287w)))) = ArithI (AUIPC (0w,524287w))``;
val _ = OS.Process.exit OS.Process.success;
