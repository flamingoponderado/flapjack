(* Typed captures for the word_elim reviewed rows.
   Definitions of word_elimScript are fetched from the theory DB; the
   definitions and theorems of word_elimProofScript are parsed literally from
   the pinned source text (so local declarations and type annotations in the
   source survive).
*)
load "preamble";
load "word_elimTheory";
load "word_elimProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open word_elimTheory word_elimProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
(* Mirror the source script's parser setup: `mem` is a variable in these
   statements, and `domain` must resolve to sptree's domain. *)
val _ = Parse.hide "mem";
val _ = Parse.bring_to_front_overload "domain" {Thy = "sptree", Name = "domain"};

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
    | NONE => raise Fail ("CAKEML or FLAPJACK_HOL_PROBE_DIR is required"));

fun source_text_of relpath =
  let
    val stream = TextIO.openIn (OS.Path.concat (source_cake, relpath))
    val text = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in text end;

val source_text = source_text_of "compiler/backend/proofs/word_elimProofScript.sml";

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

(* ---- word_elim definitions (exported by word_elimTheory) ---- *)
val _ = emit_exported "find_word_loc_def_typed" "word_elim" "find_word_loc_def";
val _ = emit_exported "find_word_ref_def_typed" "word_elim" "find_word_ref_def";
val _ = emit_exported "analyse_word_code_def_typed" "word_elim" "analyse_word_code_def";
val _ = emit_exported "remove_word_code_def_typed" "word_elim" "remove_word_code_def";
val _ = emit_exported "remove_word_prog_def_typed" "word_elim" "remove_word_prog_def";

(* ---- word_elimProof definitions and theorems, parsed from the source ---- *)
val _ = capture "dest_word_loc_def_typed" "dest_word_loc_def";
val _ = capture "dest_result_loc_def_typed" "dest_result_loc_def";
val _ = capture "get_locals_def_typed" "get_locals_def";
val _ = capture "get_store_def_typed" "get_store_def";
val _ = capture "get_num_wordloc_alist_def_typed" "get_num_wordloc_alist_def";
val _ = capture "get_stack_def_typed" "get_stack_def";
val _ = capture "get_memory_def_typed" "get_memory_def";
val _ = capture "find_loc_state_def_typed" "find_loc_state_def";
val _ = capture "code_rel_def_typed" "code_rel_def";
val _ = capture "code_closed_def_typed" "code_closed_def";
val _ = capture "gc_no_new_locs_def_typed" "gc_no_new_locs_def";
val _ = capture "word_state_rel_def_typed" "word_state_rel_def";

val _ = capture "lookup_analyse_word_code_typed" "lookup_analyse_word_code";
val _ = capture "remove_word_code_thm_typed" "remove_word_code_thm";
val _ = capture "domain_get_locals_lookup_typed" "domain_get_locals_lookup";
val _ = capture "get_locals_insert_Loc_typed" "get_locals_insert_Loc";
val _ = capture "get_locals_insert_typed" "get_locals_insert";
val _ = capture "domain_get_store_typed" "domain_get_store";
val _ = capture "get_store_update_typed" "get_store_update";
val _ = capture "get_num_wordloc_alist_thm_typed" "get_num_wordloc_alist_thm";
val _ = capture "get_num_wordloc_alist_get_locals_typed"
  "get_num_wordloc_alist_get_locals";
val _ = capture "get_locals_union_subset_typed" "get_locals_union_subset";
val _ = capture "get_stack_hd_thm_typed" "get_stack_hd_thm";
val _ = capture "get_stack_LASTN_typed" "get_stack_LASTN";
val _ = capture "get_stack_CONS_typed" "get_stack_CONS";
val _ = capture "get_stack_enc_stack_typed" "get_stack_enc_stack";
val _ = capture "get_stack_dec_stack_typed" "get_stack_dec_stack";
val _ = capture "FINITE_mdom_mem_typed" "FINITE_mdom_mem";
val _ = capture "domain_get_memory_typed" "domain_get_memory";
val _ = capture "get_memory_update_typed" "get_memory_update";
val _ = capture "domain_find_loc_state_typed" "domain_find_loc_state";
val _ = capture "ALOOKUP_ZIP_SUCCESS_typed" "ALOOKUP_ZIP_SUCCESS";
val _ = capture "get_vars_locals_typed" "get_vars_locals";
val _ = capture "get_vars_get_locals_typed" "get_vars_get_locals";
val _ = capture "get_locals_fromList2_typed" "get_locals_fromList2";
val _ = capture "get_locals_fromList2_extension_typed" "get_locals_fromList2_extension";
val _ = capture "get_locals_fromList2_FRONT_typed" "get_locals_fromList2_FRONT";
val _ = capture "get_memory_write_bytearray_lemma_typed" "get_memory_write_bytearray_lemma";
val _ = capture "stack_list_rearrange_lemma_typed" "stack_list_rearrange_lemma";
val _ = capture "remove_word_code_thm_FST_typed" "remove_word_code_thm_FST";
val _ = capture "remove_word_code_MAP_FST_lemma_typed" "remove_word_code_MAP_FST_lemma";
val _ = capture "word_state_rel_get_var_typed" "word_state_rel_get_var";
val _ = capture "word_state_rel_get_store_typed" "word_state_rel_get_store";
val _ = capture "word_state_rel_get_vars_typed" "word_state_rel_get_vars";
val _ = capture "word_state_rel_set_var_typed" "word_state_rel_set_var";
val _ = capture "word_state_rel_set_var_word_typed" "word_state_rel_set_var_word";
val _ = capture "word_state_rel_set_vars_typed" "word_state_rel_set_vars";
val _ = capture "word_state_rel_set_fp_var_typed" "word_state_rel_set_fp_var";
val _ = capture "word_state_rel_word_exp_typed" "word_state_rel_word_exp";
val _ = capture "word_state_rel_mem_load_typed" "word_state_rel_mem_load";
val _ = capture "word_state_rel_mem_load_32_typed" "word_state_rel_mem_load_32";
val _ = capture "word_state_rel_get_fp_var_typed" "word_state_rel_get_fp_var";
val _ = capture "word_state_rel_assign_NONE_typed" "word_state_rel_assign_NONE";
val _ = capture "word_state_rel_inst_NONE_typed" "word_state_rel_inst_NONE";
val _ = capture "word_state_rel_assign_SOME_typed" "word_state_rel_assign_SOME";
val _ = capture "word_state_rel_inst_SOME_typed" "word_state_rel_inst_SOME";
val _ = capture "word_state_rel_pop_env_NONE_typed" "word_state_rel_pop_env_NONE";
val _ = capture "word_state_rel_pop_env_typed" "word_state_rel_pop_env";
val _ = capture "word_state_rel_jump_exc_typed" "word_state_rel_jump_exc";
val _ = capture "word_state_rel_gc_typed" "word_state_rel_gc";
val _ = capture "word_state_rel_alloc_typed" "word_state_rel_alloc";
val _ = capture "const_writes_eq_Loc_typed" "const_writes_eq_Loc";
val _ = capture "push_env_def2_typed" "push_env_def2";
val _ = capture "get_locals_inter_subset_typed" "get_locals_inter_subset";
val _ = capture "word_removal_lemma_typed" "word_removal_lemma";
val _ = capture "word_removal_thm_typed" "word_removal_thm";
