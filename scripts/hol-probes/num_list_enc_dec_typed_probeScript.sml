(* Typed source declarations for num_list_enc_dec. Labels avoid apostrophes so
   the row printer can parse them. *)
load "preamble";
load "num_list_enc_decTheory";
open HolKernel Parse boolLib bossLib;
open preamble num_list_enc_decTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "dec_ok_def_typed" num_list_enc_decTheory.dec_ok_def;
val _ = show "enc_dec_ok_def_typed" num_list_enc_decTheory.enc_dec_ok_def;
val _ = show "dec_ok_simp_typed" num_list_enc_decTheory.dec_ok_simp;
val _ = show "enc_dec_ok_o_typed" num_list_enc_decTheory.enc_dec_ok_o;
val _ = show "enc_dec_ok_prime_def_typed" num_list_enc_decTheory.enc_dec_ok'_def;
val _ = show "IMP_enc_dec_ok_typed" num_list_enc_decTheory.IMP_enc_dec_ok;
val _ = show "enc_dec_ok_prime_IMP_typed" num_list_enc_decTheory.enc_dec_ok'_IMP;
val _ = show "const_dec_def_typed" num_list_enc_decTheory.const_dec_def;
val _ = show "enc_dec_ok_prime_const_typed" num_list_enc_decTheory.enc_dec_ok'_const;
val _ = show "enc_dec_ok_prime_o_typed" num_list_enc_decTheory.enc_dec_ok'_o;
val _ = show "fix_res_def_typed" num_list_enc_decTheory.fix_res_def;
val _ = show "fix_res_IMP_typed" num_list_enc_decTheory.fix_res_IMP;
val _ = show "unit_enc_def_typed" num_list_enc_decTheory.unit_enc_def;
val _ = show "unit_dec_def_typed" num_list_enc_decTheory.unit_dec_def;
val _ = show "unit_enc_dec_ok_typed" num_list_enc_decTheory.unit_enc_dec_ok;
val _ = show "num_enc_def_typed" num_list_enc_decTheory.num_enc_def;
val _ = show "num_dec_def_typed" num_list_enc_decTheory.num_dec_def;
val _ = show "num_enc_dec_ok_typed" num_list_enc_decTheory.num_enc_dec_ok;
val _ = show "word64_enc_def_typed" num_list_enc_decTheory.word64_enc_def;
val _ = show "word64_dec_def_typed" num_list_enc_decTheory.word64_dec_def;
val _ = show "word64_enc_dec_ok_typed" num_list_enc_decTheory.word64_enc_dec_ok;
val _ = show "bool_enc_def_typed" num_list_enc_decTheory.bool_enc_def;
val _ = show "bool_dec_def_typed" num_list_enc_decTheory.bool_dec_def;
val _ = show "bool_enc_dec_ok_typed" num_list_enc_decTheory.bool_enc_dec_ok;
val _ = show "int_enc_def_typed" num_list_enc_decTheory.int_enc_def;
val _ = show "int_dec_def_typed" num_list_enc_decTheory.int_dec_def;
val _ = show "int_enc_dec_ok_typed" num_list_enc_decTheory.int_enc_dec_ok;
