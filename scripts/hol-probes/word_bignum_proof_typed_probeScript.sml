(* Typed captures for the word_bignumProof reviewed rows.
   Definitions are fetched from the theory DB (word_bignumProof exports them);
   the multiword single-word helpers come from the HOL multiword examples;
   local theorems are parsed literally from the pinned source text.
*)
load "preamble";
load "multiwordTheory";
load "mc_multiwordTheory";
load "word_bignumProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open multiwordTheory mc_multiwordTheory word_bignumProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label thy name =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => print (label ^ "=MISSING\n")
  | SOME (th,_) => emit label th;

fun components ty =
  case Lib.total Type.dest_thy_type ty of
    NONE => [ty]
  | SOME {Thy,Tyop,Args} => ty :: List.concat (map components Args);

fun datatype_type_of_const thy name tyop =
  let
    val c = prim_mk_const {Thy=thy,Name=name}
    val ts = components (type_of c)
    fun is_it t =
      case Lib.total Type.dest_thy_type t of
        NONE => false
      | SOME {Thy,Tyop,Args} => Tyop = tyop andalso List.length Args > 0
  in
    case List.find is_it ts of
      NONE => raise Fail ("no datatype type " ^ tyop)
    | SOME t => t
  end;

fun emit_datatype label thy sizeName tyop =
  let
    val ty = datatype_type_of_const thy sizeName tyop
    val cs = TypeBase.constructors_of ty
  in
    print (label ^ "=");
    print (String.concatWith "; "
      (map (fn c => let val (n,t) = dest_const c
         in n ^ ":" ^ type_to_string t end) cs));
    print "\n"
  end;

(* Local statements parsed literally from the pinned source text. *)
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

val source_text = source_text_of "compiler/backend/proofs/word_bignumProofScript.sml";

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

fun statement_from start name =
  let
    val lines = List.drop (source_lines, start)
    fun scan [] = raise Fail ("missing declaration " ^ name)
      | scan (l :: rest) =
          (case decl_head l name "Theorem" of
             SOME _ => ("Proof", rest)
           | NONE => (case decl_head l name "Definition" of
                        SOME _ => ("End", rest)
                      | NONE => scan rest))
    val (stop, body) = scan lines
    fun take [] = []
      | take (l :: rest) =
          if String.isPrefix stop (strip_leading l) then []
          else l :: take rest
    val stmt = String.concatWith "\n" (take body)
  in
    if String.size stmt = 0 then raise Fail ("empty statement " ^ name)
    else stmt
  end;

fun statement_of name = statement_from 0 name;

(* Expand `^name` antiquotations to the bound term. *)
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

  fun after_last_eq q =
    let
      fun go acc [] = String.implode (List.rev acc)
        | go acc (#" " :: #"=" :: #" " :: rest) = go [] rest
        | go acc (c :: rest) = go (c :: acc) rest
    in lead_trim (go [] (String.explode q)) end;

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

fun capture_at label name line =
  let val tm = Parse.Term [QUOTE (strip_antiquote (statement_from (line - 1) name))]
  in (print (label ^ "="); print_term tm; print "\n") end;

(* ---- multiword single-word helpers ---- *)
val _ = emit_exported "b2n_def_typed" "multiword" "b2n_def";
val _ = emit_exported "b2w_def_typed" "multiword" "b2w_def";
val _ = emit_exported "single_add_def_typed" "multiword" "single_add_def";
val _ = emit_exported "single_sub_def_typed" "multiword" "single_sub_def";
val _ = emit_exported "single_mul_def_typed" "multiword" "single_mul_def";
val _ = emit_exported "single_div_def_typed" "multiword" "single_div_def";
val _ = emit_exported "single_div_pre_def_typed" "mc_multiword" "single_div_pre_def";
val _ = emit_exported "single_add_word_def_typed" "mc_multiword" "single_add_word_def";
val _ = emit_exported "single_sub_word_def_typed" "mc_multiword" "single_sub_word_def";

(* ---- word_bignumProof definitions ---- *)
val _ = emit_datatype "state_typed" "word_bignumProof" "state_size" "state";
val _ = emit_exported "eval_exp_def_typed" "word_bignumProof" "eval_exp_def";
val _ = emit_exported "eval_exp_pre_def_typed" "word_bignumProof" "eval_exp_pre_def";
val _ = emit_exported "eval_ri_pre_def_typed" "word_bignumProof" "eval_ri_pre_def";
val _ = emit_exported "eval_ri_def_typed" "word_bignumProof" "eval_ri_def";
val _ = emit_exported "dec_clock_def_typed" "word_bignumProof" "dec_clock_def";
val _ = emit_exported "reg_write_def_typed" "word_bignumProof" "reg_write_def";
val _ = emit_exported "delete_vars_def_typed" "word_bignumProof" "delete_vars_def";
val _ = emit_exported "array_write_def_typed" "word_bignumProof" "array_write_def";
val _ = emit_exported "clock_write_def_typed" "word_bignumProof" "clock_write_def";
val _ = emit_exported "copy_vars_def_typed" "word_bignumProof" "copy_vars_def";
val _ = emit_exported "eval_rules_typed" "word_bignumProof" "eval_rules";
val _ = emit_exported "exp_ok_def_typed" "word_bignumProof" "exp_ok_def";
val _ = emit_exported "syntax_ok_aux_def_typed" "word_bignumProof" "syntax_ok_aux_def";
val _ = emit_exported "syntax_ok_def_typed" "word_bignumProof" "syntax_ok_def";
val _ = emit_exported "list_update_def_typed" "word_bignumProof" "list_update_def";
val _ = emit_exported "list_store_def_typed" "word_bignumProof" "list_store_def";
val _ = emit_exported "loop_app_def_typed" "word_bignumProof" "loop_app_def";
val _ = emit_exported "tick_before_def_typed" "word_bignumProof" "tick_before_def";
val _ = emit_exported "code_subset_def_typed" "word_bignumProof" "code_subset_def";
val _ = emit_exported "array_rel_def_typed" "word_bignumProof" "array_rel_def";
val _ = emit_exported "code_rel_def_typed" "word_bignumProof" "code_rel_def";
val _ = emit_exported "div_code_assum_def_typed" "word_bignumProof" "div_code_assum_def";
val _ = emit_exported "state_rel_def_typed" "word_bignumProof" "state_rel_def";
val _ = emit_exported "good_code_def_typed" "word_bignumProof" "good_code_def";
val _ = emit_exported "Corr_def_typed" "word_bignumProof" "Corr_def";

(* ---- exported theorems ---- *)
val _ = emit_exported "Eval_NONE_IMP_typed" "word_bignumProof" "Eval_NONE_IMP";
val _ = emit_exported "evaluate_Seq_Seq_typed" "word_bignumProof" "evaluate_Seq_Seq";
val _ = emit_exported "word_list_APPEND_typed" "word_bignumProof" "word_list_APPEND";
val _ = emit_exported "compile_thm_typed" "word_bignumProof" "compile_thm";
val _ = emit_exported "reg_write_simp_alt_typed" "word_bignumProof" "reg_write_simp_alt";
val _ = emit_exported "FLOOKUP_DOMSUB_typed" "word_bignumProof" "FLOOKUP_DOMSUB";
val _ = emit_exported "evaluate_mc_iop_typed" "word_bignumProof" "evaluate_mc_iop";
val _ = emit_exported "compile_NIL_IMP_typed" "word_bignumProof" "compile_NIL_IMP";

(* ---- local theorems parsed from the source ---- *)
val _ = capture "state_rel_delete_vars_282_typed" "state_rel_delete_vars";
val _ = capture_at "state_rel_delete_vars_293_typed" "state_rel_delete_vars" 293;
val _ = capture "env_to_list_insert_0_LN_typed" "env_to_list_insert_0_LN";
val _ = capture "evaluate_LoadRegs_typed" "evaluate_LoadRegs";
val _ = capture "evaluate_SaveRegs_typed" "evaluate_SaveRegs";
val _ = capture "Corr_Skip_typed" "Corr_Skip";
val _ = capture "Corr_Seq_typed" "Corr_Seq";
val _ = capture "Corr_Seq_alt_typed" "Corr_Seq_alt";
val _ = capture "Corr_Continue_typed" "Corr_Continue";
val _ = capture "Corr_Assign_typed" "Corr_Assign";
val _ = capture "Corr_Delete_typed" "Corr_Delete";
val _ = capture "Corr_Load_typed" "Corr_Load";
val _ = capture "Corr_Store_typed" "Corr_Store";
val _ = capture "Corr_Swap_typed" "Corr_Swap";
val _ = capture "Corr_Add_typed" "Corr_Add";
val _ = capture "Corr_Sub_typed" "Corr_Sub";
val _ = capture "Corr_Mul_typed" "Corr_Mul";
val _ = capture "Corr_Div_typed" "Corr_Div";
val _ = capture "Corr_If_typed" "Corr_If";
val _ = capture "Corr_LoopBody_typed" "Corr_LoopBody";
val _ = capture "Corr_Loop_lemma_typed" "Corr_Loop_lemma";
val _ = capture "Corr_STRENGTHEN_TERM_typed" "Corr_STRENGTHEN_TERM";
val _ = capture "Corr_move_pre_typed" "Corr_move_pre";
val _ = capture "mc_fac_corr_typed" "mc_fac_corr";
val _ = capture "code_subset_refl_typed" "code_subset_refl";
val _ = capture "code_subset_trans_typed" "code_subset_trans";
val _ = capture "compile_IMP_code_subset_typed" "compile_IMP_code_subset";
val _ = capture "has_compiled_lemma_typed" "has_compiled_lemma";
val _ = capture "state_rel_IN_FDOM_typed" "state_rel_IN_FDOM";
val _ = capture "compile_exp_thm_typed" "compile_exp_thm";
val _ = capture "evaluate_SeqTemp_typed" "evaluate_SeqTemp";
val _ = capture "evaluate_SeqTempImm_typed" "evaluate_SeqTempImm";
val _ = capture "evaluate_SeqTempImmNot_typed" "evaluate_SeqTempImmNot";
val _ = capture "LESS_LENGTH_IMP_APPEND_typed" "LESS_LENGTH_IMP_APPEND";
val _ = capture "shift_eq_bytes_in_word_typed" "shift_eq_bytes_in_word";
val _ = capture "b2w_if_typed" "b2w_if";
val _ = capture "b2n_if_typed" "b2n_if";
val _ = capture "list_update_alist_insert_typed" "list_update_alist_insert";
val _ = capture "domain_list_update_typed" "domain_list_update";
val _ = capture "list_store_FUPDATE_typed" "list_store_FUPDATE";
val _ = capture "FLOOKUP_list_store_ignore_typed" "FLOOKUP_list_store_ignore";
val _ = capture "copy_vars_const_typed" "copy_vars_const";
val _ = capture "lookup_list_update_ADD_2_typed" "lookup_list_update_ADD_2";
val _ = capture "copy_vars_ignore_typed" "copy_vars_ignore";
val _ = capture "copy_vars_IMP_typed" "copy_vars_IMP";
val _ = capture "LIST_REL_lemma_typed" "LIST_REL_lemma";
val _ = capture "compile_LESS_mini_size_typed" "compile_LESS_mini_size";
val _ = capture "MEM_compile_typed" "MEM_compile";
val _ = capture "loop_app_EQ_typed" "loop_app_EQ";
val _ = capture "true_pres_typed" "true_pres";
val _ = capture "dec_clock_thm_typed" "dec_clock_thm";
val _ = capture "array_write_cancel_typed" "array_write_cancel";
val _ = capture "reg_write_cancel_typed" "reg_write_cancel";
val _ = capture "state_eq_lemma_typed" "state_eq_lemma";
val _ = capture "clock_write_simp_typed" "clock_write_simp";
val _ = capture "dec_clock_write_simp_typed" "dec_clock_write_simp";
val _ = capture "reg_write_simp_typed" "reg_write_simp";
val _ = capture "array_write_simp_typed" "array_write_simp";
val _ = capture "delete_vars_simp_typed" "delete_vars_simp";
val _ = capture "reg_read_lemma1_typed" "reg_read_lemma1";
val _ = capture "reg_read_lemma2_typed" "reg_read_lemma2";
val _ = capture "array_read_lemma_typed" "array_read_lemma";
val _ = capture "clock_read_lemma_typed" "clock_read_lemma";
val _ = capture "i2mw_NOT_NIL_typed" "i2mw_NOT_NIL";
val _ = capture "mw_ok_SND_i2mw_typed" "mw_ok_SND_i2mw";
