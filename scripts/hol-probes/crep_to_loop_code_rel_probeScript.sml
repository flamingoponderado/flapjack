load "bossLib";
load "preamble";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopProofTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

(* Concrete instance of HOL `code_rel_def`
   (cakeml/pancake/proofs/crep_to_loopProofScript.sml:76-88):

     ctxt  = <| vars := FEMPTY; funcs := FEMPTY |+ ("f", (42,2)); vmax := 0;
                 target := RISC_V |>;
     s_code = FEMPTY |+ (5, ([1;2], Skip))         (* ns = [1;2], prog = Skip *)
     t_code = insert 42 ([0;1], Mark Skip) LN

   The witness for the existential is loc = 42, len = 2, with
   args = GENLIST I 2 = [0;1] and nctxt = ctxt_fc RISC_V funcs [1;2] args. *)

val funcs = ``FEMPTY |+ (strlit "f", (42:num,2:num))``;
val ctxt = ``context FEMPTY ^funcs 0 RISC_V``;
val s_code = ``FEMPTY |+ ((5:num), (([1;2] : num list), (crepLang$Skip : 8 word crepLang$prog)))``;
val t_code = ``insert (42:num) (([0;1] : num list), (Mark Skip : 8 word loopLang$prog)) LN``;
val sk = ``(crepLang$Skip : 8 word crepLang$prog)``;

val args = ``GENLIST I 2``;
val nctxt = ``ctxt_fc RISC_V ^funcs ([1;2] : num list) ^args``;
val compiled = ``ocompile ^nctxt (list_to_num_set ^args) ^sk``;

print_eval "code_rel_funcs_lookup" ``FLOOKUP ^funcs (strlit "f")``;
print_eval "code_rel_scode_lookup" ``FLOOKUP ^s_code 5``;
print_eval "code_rel_args" args;
print_eval "code_rel_skip_compile" compiled;
print_eval "code_rel_tcode_lookup" ``lookup 42 ^t_code``;

(* The full instantiated requirement of `code_rel`, with the witnesses
   loc = 42 and len = 2 substituted. *)
print_eval "code_rel_witness"
  ``(FLOOKUP ^s_code (5:num) = SOME (([1;2] : num list), ^sk)) /\
    (FLOOKUP ^funcs (strlit "f") = SOME ((42:num),(2:num))) /\
    (LENGTH ([1;2] : num list) = 2) /\
    (lookup 42 ^t_code = SOME (^args, ^compiled))``;

(* Same shape but with the function table missing the key: the required
   existential cannot be discharged. *)
print_eval "code_rel_missing_funcs"
  ``(FLOOKUP ^funcs (strlit "g") = SOME ((42:num),(2:num))) /\
    (LENGTH ([1;2] : num list) = 2)``;

(* Same shape but with a length mismatch between `ns` and the stored length. *)
print_eval "code_rel_len_mismatch"
  ``(FLOOKUP ^funcs (strlit "f") = SOME ((42:num),(2:num))) /\
    (LENGTH ([1;2] : num list) = 3)``;

(* The lookup of the target code map at the stored location is the compiled
   program together with the generated argument list. *)
print_eval "code_rel_lookup_pair"
  ``lookup 42 ^t_code = SOME (^args, ^compiled)``;