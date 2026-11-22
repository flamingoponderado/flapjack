(* Typed capture of data_to_word_assignProof's exported `assign_def_extras`
   (data_to_word_assignProofScript.sml:63-72), a LIST_CONJ of 28 theorems.
   The probe splits the right-nested conjunction exactly 27 times, checks that
   each conjunct is alpha-equivalent to the source theorem named in its label,
   and prints each conjunct with inferred types. Conjunct 18,
   generated_bignum_stubs_eq, is only checked for equivalence here: its typed
   statement is captured by word_bignum_stubs_eq_typed_probe.out. *)
load "preamble";
load "data_to_word_assignProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;

val th = data_to_word_assignProofTheory.assign_def_extras;
val _ = if null (hyp th) then ()
  else raise Fail "assign_def_extras has unexpected hypotheses";

fun split 1 t = [t]
  | split k t = let val (a, b) = dest_conj t in a :: split (k - 1) b end;
val conjuncts = split 28 (concl th);

val _ = (print "assign_def_extras_hyps=";
  print (Int.toString (length (hyp th))); print "\n");
val _ = (print "assign_def_extras_conjuncts=";
  print (Int.toString (length conjuncts)); print "\n");
val _ = (print "assign_def_extras_free_vars=";
  print (String.concatWith "; "
    (map (fn v => fst (dest_var v) ^ " " ^ type_to_string (type_of v))
      (free_vars (concl th))));
  print "\n");
val _ = (print "assign_def_extras_type_vars=";
  print (String.concatWith "; "
    (map type_to_string (type_vars_in_term (concl th))));
  print "\n");

val _ = show_types := true;
(* Conjunct k (1-based) must be alpha-equivalent to the listed source theorem. *)
fun check k source =
  let val c = List.nth (conjuncts, k - 1)
  in if aconv c (concl source) andalso null (hyp source) then c
     else raise Fail ("assign_def_extras conjunct " ^ Int.toString k ^ " differs")
  end;
fun emit label k source =
  (print (label ^ "="); print_term (check k source); print "\n");
fun same label k source =
  (check k source; print (label ^ "=T\n"));

val _ = emit "assign_def_extras_conjunct_01_LoadWord64_def_typed" 1 data_to_wordTheory.LoadWord64_def;
val _ = emit "assign_def_extras_conjunct_02_WriteWord64_def_typed" 2 data_to_wordTheory.WriteWord64_def;
val _ = emit "assign_def_extras_conjunct_03_BignumHalt_def_typed" 3 data_to_wordTheory.BignumHalt_def;
val _ = emit "assign_def_extras_conjunct_04_LoadBignum_def_typed" 4 data_to_wordTheory.LoadBignum_def;
val _ = emit "assign_def_extras_conjunct_05_AnyArith_code_def_typed" 5 data_to_wordTheory.AnyArith_code_def;
val _ = emit "assign_def_extras_conjunct_06_Add_code_def_typed" 6 data_to_wordTheory.Add_code_def;
val _ = emit "assign_def_extras_conjunct_07_Sub_code_def_typed" 7 data_to_wordTheory.Sub_code_def;
val _ = emit "assign_def_extras_conjunct_08_Mul_code_def_typed" 8 data_to_wordTheory.Mul_code_def;
val _ = emit "assign_def_extras_conjunct_09_Div_code_def_typed" 9 data_to_wordTheory.Div_code_def;
val _ = emit "assign_def_extras_conjunct_10_Mod_code_def_typed" 10 data_to_wordTheory.Mod_code_def;
val _ = emit "assign_def_extras_conjunct_11_Compare1_code_def_typed" 11 data_to_wordTheory.Compare1_code_def;
val _ = emit "assign_def_extras_conjunct_12_Compare_code_def_typed" 12 data_to_wordTheory.Compare_code_def;
val _ = emit "assign_def_extras_conjunct_13_Equal1_code_def_typed" 13 data_to_wordTheory.Equal1_code_def;
val _ = emit "assign_def_extras_conjunct_14_Equal_code_def_typed" 14 data_to_wordTheory.Equal_code_def;
val _ = emit "assign_def_extras_conjunct_15_LongDiv1_code_def_typed" 15 data_to_wordTheory.LongDiv1_code_def;
val _ = emit "assign_def_extras_conjunct_16_LongDiv_code_def_typed" 16 data_to_wordTheory.LongDiv_code_def;
val _ = emit "assign_def_extras_conjunct_17_ShiftVar_def_typed" 17 data_to_wordTheory.ShiftVar_def;
val _ = same "assign_def_extras_conjunct_18_generated_bignum_stubs_eq_aconv" 18 word_bignumTheory.generated_bignum_stubs_eq;
val _ = emit "assign_def_extras_conjunct_19_DivCode_def_typed" 19 word_bignumTheory.DivCode_def;
val _ = emit "assign_def_extras_conjunct_20_AddNumSize_def_typed" 20 data_to_wordTheory.AddNumSize_def;
val _ = emit "assign_def_extras_conjunct_21_AnyHeader_def_typed" 21 data_to_wordTheory.AnyHeader_def;
val _ = emit "assign_def_extras_conjunct_22_WriteWord64_on_32_def_typed" 22 data_to_wordTheory.WriteWord64_on_32_def;
val _ = emit "assign_def_extras_conjunct_23_WriteWord32_on_32_def_typed" 23 data_to_wordTheory.WriteWord32_on_32_def;
val _ = emit "assign_def_extras_conjunct_24_AllocVar_def_typed" 24 data_to_wordTheory.AllocVar_def;
val _ = emit "assign_def_extras_conjunct_25_SilentFFI_def_typed" 25 data_to_wordTheory.SilentFFI_def;
val _ = emit "assign_def_extras_conjunct_26_WordOp64_on_32_def_typed" 26 data_to_wordTheory.WordOp64_on_32_def;
val _ = emit "assign_def_extras_conjunct_27_WordShift64_on_32_def_typed" 27 data_to_wordTheory.WordShift64_on_32_def;
val _ = emit "assign_def_extras_conjunct_28_Make_ptr_bits_code_def_typed" 28 data_to_wordTheory.Make_ptr_bits_code_def;
