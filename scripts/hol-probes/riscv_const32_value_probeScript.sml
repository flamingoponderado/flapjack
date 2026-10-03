load "preamble"; load "riscvTheory";
open HolKernel Parse bossLib preamble riscvTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
(* Ground original word-value boundaries supplement the unrestricted Lean
   theorem and literal riscv_const32/dfn'LUI/XORI/ADDI source review. *)
fun out label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))); print "\n");
val _ = out "const32_value_zero" ``let c = (0w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_low_positive_max" ``let c = (2047w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_low_sign_bit" ``let c = (2048w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_low_all_ones" ``let c = (4095w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_high_one" ``let c = (4096w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_positive_sign_boundary" ``let c = (2147481600w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_positive_max" ``let c = (2147483647w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_negative_min" ``let c = (2147483648w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_negative_min_low_sign" ``let c = (2147485696w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_negative_low_positive" ``let c = (4294965247w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_negative_low_sign" ``let c = (4294965248w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = out "const32_value_all_ones" ``let c = (4294967295w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``;
val _ = (print "const32_value_statement="; print_term ``let c = (0w : word32) in
 (if c ' 11 then
   (sw2sw (((~((31 >< 12) c : word20)) @@ (0w : word12)) : word32) : word64) ??
     (sw2sw ((11 >< 0) c : word12) : word64)
  else
   (sw2sw ((((31 >< 12) c : word20) @@ (0w : word12)) : word32) : word64) +
     (sw2sw ((11 >< 0) c : word12) : word64)) = (sw2sw c : word64)``; print "\n");
val _ = print ("const32_value_types=" ^ String.concatWith ", " (map (fn (n, t) => n ^ " : " ^ type_to_string t) [("c", type_of ``(0w : word32)``), ("result", type_of ``(sw2sw (0w : word32) : word64)``)]) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
