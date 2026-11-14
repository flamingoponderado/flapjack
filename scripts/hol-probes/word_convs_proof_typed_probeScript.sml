(* Typed captures for the wordConvsProof reviewed rows (task 171).
   The theory is a default CakeML build target, so no private build copy is
   needed for it; see scripts/hol-probes/README.md for the load path.
   175 names (177 reviewed rows; two rows share ssa_cc_trans_flat_exp_conventions):
   36 exported (fetched from the theory DB), 137 local statements parsed
   literally from the pinned source text (typed source evidence, not a
   replay), 2 derived (remove_dead_prog_conventions fetched from the DB;
   const_fp_loop_Seq replayed from its own definition derivation),
   0 datatypes.
*)
load "preamble";
load "wordConvsProofTheory";
load "wordConvsTheory";
load "wordPropsTheory";
load "wordSemTheory";
load "word_simpTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open wordConvsProofTheory;
open wordConvsTheory wordPropsTheory wordSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="wordConvsProof",Name=name} of
    NONE => raise Fail ("missing export " ^ name)
  | SOME (th,_) => emit label th;

fun emit_as label th = emit label th;

fun fetch_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => th;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");

fun source_text_of relpath =
  let
    val stream = TextIO.openIn (OS.Path.concat (source_cake, relpath))
    val text = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in text end;

val source_text = source_text_of "compiler/backend/proofs/wordConvsProofScript.sml";

val source_lines = String.fields (fn c => c = #"\n") source_text;

fun strip_leading s =
  Substring.string (Substring.dropl (fn c => c = #" " orelse c = #"\t")
    (Substring.full s));

fun decl_head line name kw =
  let
    val line' = strip_leading line
  in
    if not (String.isPrefix kw line') then NONE
    else
      let
        val rest = strip_leading (String.extract (line', String.size kw, NONE))
      in
        if String.isPrefix name rest andalso
           (String.size rest = String.size name orelse
            let val c = String.sub (rest, String.size name) in
              not (Char.isAlphaNum c) andalso c <> #"_"
            end)
        then SOME rest
        else NONE
      end
  end;

fun statement_of name =
  let
    fun scan [] = raise Fail ("missing declaration " ^ name)
      | scan (l :: rest) =
          (case decl_head l name "Theorem" of
             SOME _ => ("Proof", rest)
           | NONE => (case decl_head l name "Definition" of
                        SOME _ => ("End", rest)
                      | NONE => scan rest))
    val (stop, body) = scan source_lines
    fun take [] = []
      | take (l :: rest) =
          if String.isPrefix stop (strip_leading l) then []
          else l :: take rest
    val stmt = String.concatWith "\n" (take body)
  in
    if String.size stmt = 0 then raise Fail ("empty statement " ^ name)
    else stmt
  end;

(* A `^` immediately followed by an identifier is an SML antiquotation of
   a term variable; the capture drops the marker and keeps the variable.
   An infix `^` (mlstring concatenation) is followed by a space and is
   kept. *)
(* SML antiquotation `^x` splices the term bound by `val x = ...` in the source
   script. Deleting the marker loses the type constraint the spliced term
   carries and unlinks type variables that the splice shares between conjuncts
   (e.g. source_to_flatProof's `val s_i1 = ``s_i1 : ('f_orac_st, 'ffi)
   flatSem$state``;` is spliced into both conjuncts of pmatch). Expand each
   splice to the bound term instead; a splice whose binding is not recognised
   is left intact, so the re-parse fails loudly rather than silently weakening
   the captured statement. *)
local
  fun lead_trim s =
    Substring.string (Substring.dropl
      (fn c => c = #" " orelse c = #"\t") (Substring.full s));

  fun tail_trim s =
    let
      fun drop [] = []
        | drop (c :: rest) =
            if c = #" " orelse c = #"\t" orelse c = #";" then drop rest
            else c :: rest
    in String.implode (List.rev (drop (List.rev (String.explode s)))) end;

  (* ``term`` or curly-quoted “term” (UTF-8), possibly spanning lines *)
  fun quoted body =
    let
      fun close acc [] = NONE
        | close acc (#"`" :: #"`" :: _) = SOME (String.implode (List.rev acc))
        | close acc (#"\226" :: #"\128" :: #"\157" :: _) =
            SOME (String.implode (List.rev acc))
        | close acc (c :: rest) = close (c :: acc) rest
      fun scan [] = NONE
        | scan (#"`" :: #"`" :: rest) = close [] rest
        | scan (#"\226" :: #"\128" :: #"\156" :: rest) = close [] rest
        | scan (_ :: rest) = scan rest
    in scan (String.explode body) end;

  fun ends_semi s =
    let
      fun go [] = false
        | go (c :: rest) =
            if c = #" " orelse c = #"\t" then go rest else c = #";"
    in go (List.rev (String.explode s)) end;

  (* the `val name = ...` chunk, joined across lines until the term closes *)
  fun chunk_for lines name =
    let
      val pre = "val " ^ name ^ " ="
      fun scan [] = NONE
        | scan (l :: rest) =
            if String.isPrefix pre (lead_trim l) then
              let
                fun take acc [] = SOME (String.concatWith "\n" (List.rev acc))
                  | take acc (m :: ms) =
                      let val acc' = m :: acc in
                        if isSome (quoted (String.concatWith "\n" (List.rev acc')))
                           orelse ends_semi m
                        then SOME (String.concatWith "\n" (List.rev acc'))
                        else take acc' ms
                      end
              in
                case take [l] rest of
                  NONE => NONE
                | SOME c =>
                    SOME (String.extract (lead_trim c, String.size pre, NONE))
              end
            else scan rest
    in scan lines end;

  (* `rand ``l = r`` ` splices the right-hand side of the equation *)
  fun after_last_eq q =
    let
      fun go acc [] = String.implode (List.rev acc)
        | go acc (#" " :: #"=" :: #" " :: rest) = go [] rest
        | go acc (c :: rest) = go (c :: acc) rest
    in lead_trim (go [] (String.explode q)) end;

  (* the type written in `x : ty`, or in `mk_var ("x", ``: ty``)` *)
  fun type_text body =
    case quoted body of
      NONE => NONE
    | SOME q =>
        let val q' = lead_trim q in
          if String.isPrefix ":" q' then
            SOME (tail_trim (String.extract (q', 1, NONE)))
          else
            (case Substring.position ":" (Substring.full q) of
               (_, rhs) =>
                 if Substring.isEmpty rhs then NONE
                 else SOME (tail_trim
                   (String.extract (Substring.string rhs, 1, NONE))))
        end;

  fun expansion lines name =
    case chunk_for lines name of
      NONE => NONE
    | SOME body =>
        if String.isPrefix "mk_var" (lead_trim body) then
          let
            fun from_type_of () =
              case Substring.position "type_of " (Substring.full body) of
                (_, rhs) =>
                  if Substring.isEmpty rhs then NONE
                  else
                    let
                      val rest = Substring.string
                        (Substring.triml (String.size "type_of ") rhs)
                      val ys = String.tokens
                        (fn c => not (Char.isAlphaNum c) andalso c <> #"_") rest
                    in
                      case ys of
                        [] => NONE
                      | (y :: _) =>
                          (case chunk_for lines y of
                             NONE => NONE
                           | SOME yb => type_text yb)
                    end
          in
            case type_text body of
              SOME ty => SOME ("(" ^ name ^ " : " ^ ty ^ ")")
            | NONE =>
                (case from_type_of () of
                   SOME ty => SOME ("(" ^ name ^ " : " ^ ty ^ ")")
                 | NONE => NONE)
          end
        else if String.isPrefix "rand" (lead_trim body) then
          (case quoted body of
             SOME q => SOME ("(" ^ after_last_eq q ^ ")")
           | NONE => NONE)
        else
          (case quoted body of
             SOME q => SOME ("(" ^ q ^ ")")
           | NONE => NONE);
in
  fun strip_antiquote s =
    let
      val lines = String.fields (fn c => c = #"\n") source_text
      fun take_name (cs, acc) =
        case cs of
          (c :: rest) =>
            if Char.isAlphaNum c orelse c = #"_"
            then take_name (rest, c :: acc)
            else (String.implode (List.rev acc), cs)
        | [] => (String.implode (List.rev acc), [])
      fun go [] acc = String.concat (List.rev acc)
        | go (#"^" :: rest) acc =
            let val (name, rest') = take_name (rest, []) in
              case expansion lines name of
                SOME e => go rest' (e :: acc)
              | NONE => go rest (String.str #"^" :: acc)
            end
        | go (c :: rest) acc = go rest (String.str c :: acc)
    in go (String.explode s) [] end;
end;

fun capture label name =
  let val tm = Parse.Term [QUOTE (strip_antiquote (statement_of name))]
  in (print (label ^ "="); print_term tm; print "\n") end;

fun capture_dt label (thy,ctor) =
  let
    val ty = type_of (prim_mk_const {Thy=thy,Name=ctor})
    val cs = TypeBase.constructors_of ty
  in
    print (label ^ "=");
    print (String.concatWith "; "
      (map (fn c => let val (n,t) = dest_const c
         in n ^ ":" ^ type_to_string t end) cs));
    print "\n"
  end;

val _ = emit_exported "every_inst_distinct_tar_reg_copy_prop_typed" "every_inst_distinct_tar_reg_copy_prop";
val _ = emit_exported "extract_labels_copy_prop_typed" "extract_labels_copy_prop";
val _ = emit_exported "flat_exp_conventions_copy_prop_typed" "flat_exp_conventions_copy_prop";
val _ = emit_exported "full_inst_ok_less_copy_prop_typed" "full_inst_ok_less_copy_prop";
val _ = emit_exported "pre_alloc_conventions_copy_prop_typed" "pre_alloc_conventions_copy_prop";
val _ = emit_exported "wf_cutsets_copy_prop_typed" "wf_cutsets_copy_prop";
val _ = emit_exported "inst_select_flat_exp_conventions_typed" "inst_select_flat_exp_conventions";
val _ = emit_exported "inst_select_full_inst_ok_less_typed" "inst_select_full_inst_ok_less";
val _ = emit_exported "inst_select_lab_pres_typed" "inst_select_lab_pres";
val _ = emit_exported "compile_single_not_created_subprogs_typed" "compile_single_not_created_subprogs";
val _ = emit_exported "remove_must_terminate_conventions_typed" "remove_must_terminate_conventions";
val _ = emit_exported "full_ssa_cc_trans_flat_exp_conventions_typed" "full_ssa_cc_trans_flat_exp_conventions";
val _ = emit_exported "full_ssa_cc_trans_lab_pres_typed" "full_ssa_cc_trans_lab_pres";
val _ = emit_exported "full_ssa_cc_trans_wf_cutsets_typed" "full_ssa_cc_trans_wf_cutsets";
val _ = emit_exported "three_to_two_reg_prog_flat_exp_conventions_typed" "three_to_two_reg_prog_flat_exp_conventions";
val _ = emit_exported "three_to_two_reg_prog_full_inst_ok_less_typed" "three_to_two_reg_prog_full_inst_ok_less";
val _ = emit_exported "three_to_two_reg_prog_lab_pres_typed" "three_to_two_reg_prog_lab_pres";
val _ = emit_exported "three_to_two_reg_prog_pre_alloc_conventions_typed" "three_to_two_reg_prog_pre_alloc_conventions";
val _ = emit_exported "three_to_two_reg_prog_two_reg_inst_typed" "three_to_two_reg_prog_two_reg_inst";
val _ = emit_exported "three_to_two_reg_prog_wf_cutsets_typed" "three_to_two_reg_prog_wf_cutsets";
val _ = emit_exported "every_inst_remove_unreach_typed" "every_inst_remove_unreach";
val _ = emit_exported "flat_exp_conventions_remove_unreach_typed" "flat_exp_conventions_remove_unreach";
val _ = emit_exported "full_inst_ok_less_remove_unreach_typed" "full_inst_ok_less_remove_unreach";
val _ = emit_exported "wf_cutsets_remove_unreach_typed" "wf_cutsets_remove_unreach";
val _ = emit_exported "labels_rel_remove_unreach_typed" "labels_rel_remove_unreach";
val _ = emit_exported "pre_alloc_conventions_remove_unreach_typed" "pre_alloc_conventions_remove_unreach";
val _ = emit_exported "word_alloc_flat_exp_conventions_typed" "word_alloc_flat_exp_conventions";
val _ = emit_exported "word_alloc_lab_pres_typed" "word_alloc_lab_pres";
val _ = emit_exported "word_alloc_two_reg_inst_typed" "word_alloc_two_reg_inst";
val _ = emit_exported "extract_labels_word_common_subexp_elim_typed" "extract_labels_word_common_subexp_elim";
val _ = emit_exported "flat_exp_conventions_word_common_subexp_elim_typed" "flat_exp_conventions_word_common_subexp_elim";
val _ = emit_exported "wf_cutsets_word_common_subexp_elim_typed" "wf_cutsets_word_common_subexp_elim";
val _ = emit_exported "compile_exp_no_inst_typed" "compile_exp_no_inst";
val _ = emit_exported "extract_labels_compile_exp_typed" "extract_labels_compile_exp";
val _ = emit_exported "word_good_handlers_word_to_word_incr_typed" "word_good_handlers_word_to_word_incr";
val _ = emit_exported "word_good_handlers_word_to_word_typed" "word_good_handlers_word_to_word";
(* Derived exported theorem: fetched with its own derived statement. *)
val _ = emit_exported "remove_dead_prog_conventions_typed" "remove_dead_prog_conventions";
val _ = capture "apply_colour_lab_pres_typed" "apply_colour_lab_pres";
val _ = capture "apply_colour_not_created_subprogs_typed" "apply_colour_not_created_subprogs";
val _ = capture "word_get_code_labels_apply_colour_typed" "word_get_code_labels_apply_colour";
val _ = capture "word_good_handlers_apply_colour_typed" "word_good_handlers_apply_colour";
val _ = capture "copy_prop_not_created_subprogs_typed" "copy_prop_not_created_subprogs";
val _ = capture "copy_prop_prog_not_alloc_var_typed" "copy_prop_prog_not_alloc_var";
val _ = capture "copy_prop_prog_not_alloc_var_aux1_typed" "copy_prop_prog_not_alloc_var_aux1";
val _ = capture "copy_prop_prog_not_alloc_var_aux2_typed" "copy_prop_prog_not_alloc_var_aux2";
val _ = capture "every_inst_distinct_tar_reg_copy_prop_aux_typed" "every_inst_distinct_tar_reg_copy_prop_aux";
val _ = capture "extract_labels_copy_prop_aux_typed" "extract_labels_copy_prop_aux";
val _ = capture "flat_exp_conventions_copy_prop_aux_typed" "flat_exp_conventions_copy_prop_aux";
val _ = capture "full_inst_ok_less_copy_prop_aux_typed" "full_inst_ok_less_copy_prop_aux";
val _ = capture "pre_alloc_conventions_copy_prop_aux_typed" "pre_alloc_conventions_copy_prop_aux";
val _ = capture "wf_cutsets_copy_prop_aux_typed" "wf_cutsets_copy_prop_aux";
val _ = capture "word_get_code_labels_copy_prop_typed" "word_get_code_labels_copy_prop";
val _ = capture "word_good_handlers_copy_prop_typed" "word_good_handlers_copy_prop";
val _ = capture "inst_select_exp_flat_exp_conventions_typed" "inst_select_exp_flat_exp_conventions";
val _ = capture "inst_select_exp_full_inst_ok_less_typed" "inst_select_exp_full_inst_ok_less";
val _ = capture "inst_select_exp_no_lab_typed" "inst_select_exp_no_lab";
val _ = capture "compile_exp_not_created_subprogs_typed" "compile_exp_not_created_subprogs";
val _ = capture "not_created_subprogs_const_fp_typed" "not_created_subprogs_const_fp";
val _ = capture "not_created_subprogs_const_fp_loop_typed" "not_created_subprogs_const_fp_loop";
val _ = capture "not_created_subprogs_hoist2_typed" "not_created_subprogs_hoist2";
val _ = capture "inst_select_not_created_subprogs_typed" "inst_select_not_created_subprogs";
val _ = capture "inst_select_exp_not_created_subprogs_typed" "inst_select_exp_not_created_subprogs";
val _ = capture "not_created_subprogs_push_out_if_typed" "not_created_subprogs_push_out_if";
val _ = capture "not_created_subprogs_Seq_assoc_typed" "not_created_subprogs_Seq_assoc";
val _ = capture "not_created_subprogs_simp_duplicate_if_typed" "not_created_subprogs_simp_duplicate_if";
val _ = capture "not_created_subprogs_SmartSeq_typed" "not_created_subprogs_SmartSeq";
val _ = capture "not_created_subprogs_drop_consts_typed" "not_created_subprogs_drop_consts";
val _ = capture "fake_moves_not_created_subprogs_typed" "fake_moves_not_created_subprogs";
val _ = capture "fake_seq_not_created_subprogs_typed" "fake_seq_not_created_subprogs";
val _ = capture "full_ssa_cc_trans_not_created_subprogs_typed" "full_ssa_cc_trans_not_created_subprogs";
val _ = capture "loop_setup_not_created_subprogs_typed" "loop_setup_not_created_subprogs";
val _ = capture "setup_ssa_not_created_subprogs_typed" "setup_ssa_not_created_subprogs";
val _ = capture "ssa_cc_trans_not_created_subprogs_typed" "ssa_cc_trans_not_created_subprogs";
val _ = capture "ssa_cc_trans_inst_not_created_subprogs_typed" "ssa_cc_trans_inst_not_created_subprogs";
val _ = capture "remove_unreach_not_created_subprogs_typed" "remove_unreach_not_created_subprogs";
val _ = capture "Seq_assoc_right_not_created_subprogs_typed" "Seq_assoc_right_not_created_subprogs";
val _ = capture "SimpSeq_not_created_subprogs_typed" "SimpSeq_not_created_subprogs";
val _ = capture "three_to_two_reg_prog_not_created_subprogs_typed" "three_to_two_reg_prog_not_created_subprogs";
val _ = capture "word_get_code_labels_remove_dead_typed" "word_get_code_labels_remove_dead";
val _ = capture "word_get_code_labels_remove_dead_prog_typed" "word_get_code_labels_remove_dead_prog";
val _ = capture "word_good_handlers_remove_dead_typed" "word_good_handlers_remove_dead";
val _ = capture "word_good_handlers_remove_dead_prog_typed" "word_good_handlers_remove_dead_prog";
val _ = capture "remove_dead_conventions_typed" "remove_dead_conventions";
val _ = capture "remove_dead_prog_not_created_subprogs_typed" "remove_dead_prog_not_created_subprogs";
val _ = capture "remove_dead_not_created_subprogs_typed" "remove_dead_not_created_subprogs";
val _ = capture "word_get_code_labels_remove_must_terminate_typed" "word_get_code_labels_remove_must_terminate";
val _ = capture "word_good_handlers_remove_must_terminate_typed" "word_good_handlers_remove_must_terminate";
val _ = capture "flat_exp_conventions_fake_moves_typed" "flat_exp_conventions_fake_moves";
val _ = capture "fake_seq_flat_exp_conventions_typed" "fake_seq_flat_exp_conventions";
val _ = capture "loop_setup_flat_exp_conventions_typed" "loop_setup_flat_exp_conventions";
val _ = capture "ssa_reconcile_flat_exp_conventions_typed" "ssa_reconcile_flat_exp_conventions";
val _ = capture "ssa_cc_trans_flat_exp_conventions_typed" "ssa_cc_trans_flat_exp_conventions";
val _ = capture "fake_moves_no_labs_typed" "fake_moves_no_labs";
val _ = capture "fake_seq_no_labs_typed" "fake_seq_no_labs";
val _ = capture "loop_setup_no_labs_typed" "loop_setup_no_labs";
val _ = capture "ssa_reconcile_no_labs_typed" "ssa_reconcile_no_labs";
val _ = capture "fake_moves_wf_cutsets_typed" "fake_moves_wf_cutsets";
val _ = capture "fake_seq_wf_cutsets_typed" "fake_seq_wf_cutsets";
val _ = capture "loop_setup_wf_cutsets_typed" "loop_setup_wf_cutsets";
val _ = capture "ssa_cc_trans_wf_cutsets_typed" "ssa_cc_trans_wf_cutsets";
val _ = capture "ssa_reconcile_wf_cutsets_typed" "ssa_reconcile_wf_cutsets";
val _ = capture "extract_labels_SmartSeq_typed" "extract_labels_SmartSeq";
val _ = capture "every_inst_Seq_assoc_right_lemma_typed" "every_inst_Seq_assoc_right_lemma";
val _ = capture "every_inst_SimpSeq_typed" "every_inst_SimpSeq";
val _ = capture "flat_exp_conventions_Seq_assoc_right_lemma_typed" "flat_exp_conventions_Seq_assoc_right_lemma";
val _ = capture "flat_exp_conventions_SimpSeq_typed" "flat_exp_conventions_SimpSeq";
val _ = capture "full_inst_ok_less_Seq_assoc_right_lemma_typed" "full_inst_ok_less_Seq_assoc_right_lemma";
val _ = capture "wf_cutsets_Seq_assoc_right_lemma_typed" "wf_cutsets_Seq_assoc_right_lemma";
val _ = capture "wf_cutsets_SimpSeq_typed" "wf_cutsets_SimpSeq";
val _ = capture "ALL_DISTINCT_extract_labels_remove_unreach_typed" "ALL_DISTINCT_extract_labels_remove_unreach";
val _ = capture "ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma_typed" "ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma";
val _ = capture "extract_labels_remove_unreach_typed" "extract_labels_remove_unreach";
val _ = capture "extract_labels_Seq_assoc_right_lemma_typed" "extract_labels_Seq_assoc_right_lemma";
val _ = capture "extract_labels_SimpSeq_typed" "extract_labels_SimpSeq";
val _ = capture "MEM_extract_labels_Seq_assoc_right_lemma_typed" "MEM_extract_labels_Seq_assoc_right_lemma";
val _ = capture "call_arg_convention_remove_unreach_typed" "call_arg_convention_remove_unreach";
val _ = capture "call_arg_convention_Seq_assoc_right_lemma_typed" "call_arg_convention_Seq_assoc_right_lemma";
val _ = capture "every_stack_var_is_stack_var_remove_unreach_typed" "every_stack_var_is_stack_var_remove_unreach";
val _ = capture "every_stack_var_is_stack_var_Seq_assoc_right_lemma_typed" "every_stack_var_is_stack_var_Seq_assoc_right_lemma";
val _ = capture "word_alloc_flat_exp_conventions_lem_typed" "word_alloc_flat_exp_conventions_lem";
val _ = capture "word_alloc_two_reg_inst_lem_typed" "word_alloc_two_reg_inst_lem";
val _ = capture "word_get_code_labels_word_alloc_typed" "word_get_code_labels_word_alloc";
val _ = capture "word_good_handlers_word_alloc_typed" "word_good_handlers_word_alloc";
val _ = capture "word_alloc_not_created_subprogs_typed" "word_alloc_not_created_subprogs";
val _ = capture "word_common_subexp_elim_not_created_subprogs_typed" "word_common_subexp_elim_not_created_subprogs";
val _ = capture "word_cseInst_not_created_subprogs_typed" "word_cseInst_not_created_subprogs";
val _ = capture "word_cse_extract_labels_typed" "word_cse_extract_labels";
val _ = capture "word_cse_flat_exp_conventions_typed" "word_cse_flat_exp_conventions";
val _ = capture "word_cse_get_code_labels_typed" "word_cse_get_code_labels";
val _ = capture "word_cse_not_created_subprogs_typed" "word_cse_not_created_subprogs";
val _ = capture "word_cse_wf_cutsets_typed" "word_cse_wf_cutsets";
val _ = capture "word_get_code_labels_word_common_subexp_elim_typed" "word_get_code_labels_word_common_subexp_elim";
val _ = capture "word_good_handlers_word_common_subexp_elim_typed" "word_good_handlers_word_common_subexp_elim";
val _ = capture "dest_Seq_no_inst_typed" "dest_Seq_no_inst";
val _ = capture "every_inst_const_fp_typed" "every_inst_const_fp";
val _ = capture "every_inst_drop_consts_typed" "every_inst_drop_consts";
val _ = capture "every_inst_SmartSeq_typed" "every_inst_SmartSeq";
val _ = capture "Seq_assoc_no_inst_typed" "Seq_assoc_no_inst";
val _ = capture "simp_duplicate_if_no_inst_typed" "simp_duplicate_if_no_inst";
val _ = capture "simp_push_out_if_no_inst_typed" "simp_push_out_if_no_inst";
val _ = capture "try_if_hoist2_no_inst_typed" "try_if_hoist2_no_inst";
val _ = capture "extract_labels_const_fp_typed" "extract_labels_const_fp";
val _ = capture "extract_labels_const_fp_loop_typed" "extract_labels_const_fp_loop";
val _ = capture "labels_rel_hoist2_typed" "labels_rel_hoist2";
val _ = capture "labels_rel_simp_duplicate_if_typed" "labels_rel_simp_duplicate_if";
val _ = capture "const_fp_loop_dummy_cases_typed" "const_fp_loop_dummy_cases";
val _ = capture "dest_If_thm_typed" "dest_If_thm";
val _ = capture "labels_rel_push_out_if_typed" "labels_rel_push_out_if";
val _ = capture "extract_labels_drop_consts_typed" "extract_labels_drop_consts";
val _ = capture "extract_labels_drop_consts_1_typed" "extract_labels_drop_consts_1";
val _ = capture "extract_labels_Seq_assoc_typed" "extract_labels_Seq_assoc";
val _ = capture "extract_labels_Seq_assoc_lemma_typed" "extract_labels_Seq_assoc_lemma";
val _ = capture "labels_rel_append_imp_typed" "labels_rel_append_imp";
val _ = capture "word_good_handlers_inst_select_exp_typed" "word_good_handlers_inst_select_exp";
val _ = capture "word_good_handlers_inst_select_typed" "word_good_handlers_inst_select";
val _ = capture "word_good_handlers_three_to_two_reg_prog_typed" "word_good_handlers_three_to_two_reg_prog";
val _ = capture "word_good_handlers_SimpSeq_typed" "word_good_handlers_SimpSeq";
val _ = capture "word_good_handlers_Seq_assoc_right_typed" "word_good_handlers_Seq_assoc_right";
val _ = capture "word_good_handlers_remove_unreach_typed" "word_good_handlers_remove_unreach";
val _ = capture "word_good_handlers_SmartSeq_typed" "word_good_handlers_SmartSeq";
val _ = capture "word_good_handlers_Seq_assoc_typed" "word_good_handlers_Seq_assoc";
val _ = capture "word_good_handlers_drop_consts_typed" "word_good_handlers_drop_consts";
val _ = capture "word_good_handlers_const_fp_loop_typed" "word_good_handlers_const_fp_loop";
val _ = capture "word_good_handlers_try_if_hoist2_typed" "word_good_handlers_try_if_hoist2";
val _ = capture "word_good_handlers_simp_duplicate_if_typed" "word_good_handlers_simp_duplicate_if";
val _ = capture "word_good_handlers_simp_push_out_if_typed" "word_good_handlers_simp_push_out_if";
val _ = capture "word_good_handlers_word_simp_typed" "word_good_handlers_word_simp";
val _ = capture "word_good_handlers_fake_moves_typed" "word_good_handlers_fake_moves";
val _ = capture "word_good_handlers_ssa_cc_trans_typed" "word_good_handlers_ssa_cc_trans";
val _ = capture "word_good_handlers_full_ssa_cc_trans_typed" "word_good_handlers_full_ssa_cc_trans";
val _ = capture "word_good_handlers_word_to_word_incr_helper_typed" "word_good_handlers_word_to_word_incr_helper";
val _ = capture "loop_setup_good_handlers_typed" "loop_setup_good_handlers";
val _ = capture "fake_seq_good_handlers_typed" "fake_seq_good_handlers";
val _ = capture "ssa_reconcile_good_handlers_typed" "ssa_reconcile_good_handlers";

(* Derived local theorem: const_fp_loop_Seq is the conjunction of the
   const_fp_loop definition clauses that mention Seq, filtered and
   conjoined exactly as in the source script. *)
val _ = emit_as "const_fp_loop_Seq_typed"
  (LIST_CONJ
    (List.filter
      (can (find_term (fn t => total (fst o dest_const) t = SOME "Seq")) o concl)
      (BODY_CONJUNCTS (fetch_other ("word_simp","const_fp_loop_def")))));
