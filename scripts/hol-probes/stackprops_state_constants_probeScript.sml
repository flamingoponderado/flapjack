(* Captures the full original StackProps20-168 statements and free-variable
   types. Local/overwritten declarations are re-proved from their unchanged
   original statements and original HOL definition proofs; they are not claimed
   to be exported theory declarations. The exported versions are fetched as-is. *)
load "bossLib";
load "preamble";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackSemTheory stackPropsTheory;
val _ = show_types := true;
fun capture label th = (print (label ^ "="); print_term (concl th); print "\n");
fun captureTypes label th = (print (label ^ "=");
  app (fn v => (print_term v; print ":"; print_type(type_of v); print ";")) (free_vars(concl th)); print "\n");

val _ = capture "sc_20" (DB.fetch "stackProps" "set_store_const");
val _ = captureTypes "sc_20_types" (DB.fetch "stackProps" "set_store_const");

val _ = capture "sc_43" (DB.fetch "stackProps" "set_store_with_const");
val _ = captureTypes "sc_43_types" (DB.fetch "stackProps" "set_store_with_const");

val _ = capture "sc_49" (DB.fetch "stackProps" "set_var_const");
val _ = captureTypes "sc_49_types" (DB.fetch "stackProps" "set_var_const");

val _ = capture "sc_74" (DB.fetch "stackProps" "set_var_with_const");
val _ = captureTypes "sc_74_types" (DB.fetch "stackProps" "set_var_with_const");

val local_84 = prove (``set_fp_var x y (z with clock := k) = set_fp_var x y z with clock := k``, EVAL_TAC);
val _ = capture "sc_84" local_84;
val _ = captureTypes "sc_84_types" local_84;

val local_90 = prove (``(set_fp_var x y z).ffi = z.ffi ∧
   (set_fp_var x y z).clock = z.clock ∧
   (set_fp_var x y z).use_alloc = z.use_alloc ∧
   (set_fp_var x y z).use_store = z.use_store ∧
   (set_fp_var x y z).use_stack = z.use_stack ∧
   (set_fp_var x y z).code = z.code ∧
   (set_fp_var x y z).be = z.be ∧
   (set_fp_var x y z).gc_fun = z.gc_fun ∧
   (set_fp_var x y z).mdomain = z.mdomain ∧
   (set_fp_var x y z).sh_mdomain = z.sh_mdomain ∧
   (set_fp_var x y z).bitmaps = z.bitmaps ∧
   (set_fp_var x y z).compile = z.compile ∧
   (set_fp_var x y z).compile_oracle = z.compile_oracle ∧
   (set_fp_var x y z).stack = z.stack ∧
   (set_fp_var x y z).stack_space = z.stack_space``, EVAL_TAC);
val _ = capture "sc_90" local_90;
val _ = captureTypes "sc_90_types" local_90;

val local_110 = prove (``get_fp_var x (y with clock := k) = get_fp_var x y``, EVAL_TAC);
val _ = capture "sc_110" local_110;
val _ = captureTypes "sc_110_types" local_110;

val _ = capture "sc_116" (DB.fetch "stackProps" "get_var_with_const");
val _ = captureTypes "sc_116_types" (DB.fetch "stackProps" "get_var_with_const");

val local_125 = prove (``get_vars xs (y with clock := k) = get_vars xs y``, Induct_on `xs` >> EVAL_TAC >> simp[]);
val _ = capture "sc_125" local_125;
val _ = captureTypes "sc_125_types" local_125;

val _ = capture "sc_131" (DB.fetch "stackProps" "get_var_imm_with_const");
val _ = captureTypes "sc_131_types" (DB.fetch "stackProps" "get_var_imm_with_const");

val _ = capture "sc_137" (DB.fetch "stackProps" "set_fp_var_const");
val _ = captureTypes "sc_137_types" (DB.fetch "stackProps" "set_fp_var_const");

val _ = capture "sc_144" (DB.fetch "stackProps" "empty_env_const");
val _ = captureTypes "sc_144_types" (DB.fetch "stackProps" "empty_env_const");

val _ = capture "sc_164" (DB.fetch "stackProps" "empty_env_with_const");
val _ = captureTypes "sc_164_types" (DB.fetch "stackProps" "empty_env_with_const");
