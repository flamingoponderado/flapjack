(* Typed captures for the reviewed wordConvsScript.sml declarations that had
   no typed capture (task 155). Exported names are printed with show_types from
   the loaded wordConvsTheory; a free variable of a theorem conclusion appears in
   a ∀* prefix (HOL stores it implicitly universally quantified, so its order is
   not significant). [local] theorems are not exported: each statement is read
   literally from the pinned source and parsed with show_types in the loaded
   wordConvsTheory context (a typed source parse, not re-proved). *)
load "preamble";
load "wordConvsTheory";
open HolKernel Parse boolLib bossLib preamble wordConvsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_text = TextIO.inputAll (TextIO.openIn
  (OS.Path.concat (source_cake, "compiler/backend/semantics/wordConvsScript.sml")));

fun after_prefix pre s =
  case (Substring.position pre (Substring.full s)) of
    (_, rest) => if Substring.isEmpty rest then NONE
                 else SOME (Substring.string (Substring.triml (String.size pre) rest));
fun statement_of name =
  let
    fun first [] = raise Fail ("missing " ^ name)
      | first (h :: t) = (case after_prefix h source_text of SOME r => r | NONE => first t)
    val rest = first ["\nTheorem " ^ name ^ "[", "\nTheorem  " ^ name ^ "[",
                      "\nTriviality " ^ name, "\nTriviality  " ^ name]
    val body = case after_prefix ":\n" rest of SOME b => b | NONE => raise Fail ("no statement " ^ name)
    val (stmt, _) = Substring.position "\nProof" (Substring.full body)
  in Substring.string stmt end;
fun capture label name =
  let val tm = Parse.Term [QUOTE (statement_of name)]
  in (print (label ^ "="); print_term tm; print "\n") end;

fun show label th =
  let val fvs = free_vars (concl th) in
    (print (label ^ "=");
     if null fvs then ()
     else (print "\226\136\128*";
           app (fn v =>
             let val ts = type_to_string (type_of v)
                 val ts = if String.sub (ts, 0) = #":"
                          then String.extract (ts, 1, NONE) else ts
             in print "("; print (#1 (dest_var v));
                print " :"; print ts; print ") " end) fvs;
           print ". ");
     app (fn h => (print_term h; print " ==> ")) (hyp th);
     print_term (concl th); print "\n")
  end;

val thy = "wordConvs";

fun emit label name =
  case DB.lookup {Thy = thy, Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in " ^ thy ^ ">\n");

val _ = emit "call_arg_convention_def_typed" "call_arg_convention_def";
val _ = emit "distinct_tar_reg_def_typed" "distinct_tar_reg_def";
val _ = emit "every_inst_def_typed" "every_inst_def";
val _ = emit "extract_labels_def_typed" "extract_labels_def";
val _ = emit "flat_exp_conventions_def_typed" "flat_exp_conventions_def";
val _ = emit "good_handlers_def_typed" "good_handlers_def";
val _ = emit "inst_arg_convention_def_typed" "inst_arg_convention_def";
val _ = emit "inst_ok_less_def_typed" "inst_ok_less_def";
val _ = emit "labels_rel_def_typed" "labels_rel_def";
val _ = emit "labels_rel_APPEND_typed" "labels_rel_APPEND";
val _ = emit "labels_rel_CONS_typed" "labels_rel_CONS";
val _ = emit "PERM_IMP_labels_rel_typed" "PERM_IMP_labels_rel";
val _ = emit "labels_rel_refl_typed" "labels_rel_refl";
val _ = emit "labels_rel_TRANS_typed" "labels_rel_TRANS";
val _ = emit "post_alloc_conventions_def_typed" "post_alloc_conventions_def";
val _ = emit "pre_alloc_conventions_def_typed" "pre_alloc_conventions_def";
val _ = emit "two_reg_inst_def_typed" "two_reg_inst_def";
val _ = emit "get_code_labels_def_typed" "get_code_labels_def";
val _ = emit "every_var_inst_mono_typed" "every_var_inst_mono";
val _ = emit "every_var_exp_mono_typed" "every_var_exp_mono";
val _ = emit "full_inst_ok_less_def_typed" "full_inst_ok_less_def";
val _ = emit "good_code_labels_def_typed" "good_code_labels_def";
val _ = emit "max_var_intro_typed" "max_var_intro";
val _ = emit "every_name_mono_typed" "every_name_mono";
val _ = emit "no_install_def_typed" "no_install_def";
val _ = emit "no_alloc_subprogs_def_typed" "no_alloc_subprogs_def";
val _ = emit "no_install_subprogs_def_typed" "no_install_subprogs_def";
val _ = emit "no_mt_subprogs_def_typed" "no_mt_subprogs_def";
val _ = emit "no_share_inst_subprogs_def_typed" "no_share_inst_subprogs_def";
val _ = emit "not_created_subprogs_def_typed" "not_created_subprogs_def";
val _ = emit "no_alloc_def_typed" "no_alloc_def";
val _ = emit "no_mt_def_typed" "no_mt_def";
val _ = emit "no_share_inst_def_typed" "no_share_inst_def";
val _ = emit "every_var_mono_typed" "every_var_mono";
val _ = emit "every_name_conj_typed" "every_name_conj";
val _ = emit "every_stack_var_conj_typed" "every_stack_var_conj";
val _ = emit "every_stack_var_mono_typed" "every_stack_var_mono";
val _ = emit "every_var_imp_every_stack_var_typed" "every_var_imp_every_stack_var";
val _ = emit "wf_cutsets_def_typed" "wf_cutsets_def";
val _ = capture "max_var_exp_IMP_typed" "max_var_exp_IMP";
val _ = emit "wf_names_def_typed" "wf_names_def";

val _ = OS.Process.exit OS.Process.success;
