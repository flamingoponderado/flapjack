(* Typed captures for the pan_structsProof reviewed rows (task 169).
   The theory is built in a private copy of the pinned CakeML tree
   (commit 857f0d98d); see scripts/hol-probes/README.md for the build
   recipe and the CAKEML load path.
   70 names: 49 exported (fetched from the theory DB), 19 local
   statements parsed literally from the pinned source text (typed source
   evidence, not a replay), 2 derived local theorems captured through
   their base statement, 0 datatypes.
*)
load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
open pan_structsProofTheory;
open panSemTheory pan_structsTheory panPropsTheory panLangTheory pan_commonPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit_exported label name =
  case DB.lookup {Thy="pan_structsProof",Name=name} of
    NONE => raise Fail ("missing export " ^ name)
  | SOME (th,_) => emit label th;

fun emit_as label th = emit label th;

fun fetch_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => th;

fun emit_other (thy,name) =
  case DB.lookup {Thy=thy,Name=name} of
    NONE => raise Fail ("missing export " ^ thy ^ ":" ^ name)
  | SOME (th,_) => emit (name ^ "_typed") th;

val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_structsProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;

fun after_prefix pre s =
  case Substring.position pre (Substring.full s) of
    (_, rest) => if Substring.isEmpty rest then raise Fail ("missing " ^ pre)
                 else Substring.string (Substring.triml (String.size pre) rest);

fun statement_of name =
  let
    val header = after_prefix ("\nTheorem " ^ name) source_text
    val rest = after_prefix ":\n" header
    val (stmt, _) = Substring.position "\nProof" (Substring.full rest)
  in Substring.string stmt end;

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

val _ = emit_exported "ALOOKUP_eq_afindi_typed" "ALOOKUP_eq_afindi";
val _ = emit_exported "FEVERY_res_var_typed" "FEVERY_res_var";
val _ = emit_exported "afindi_EL_typed" "afindi_EL";
val _ = emit_exported "afindi_MAP_eq_typed" "afindi_MAP_eq";
val _ = emit_exported "afindi_append_typed" "afindi_append";
val _ = emit_exported "afindi_less_length_typed" "afindi_less_length";
val _ = emit_exported "compile_correct_typed" "compile_correct";
val _ = emit_exported "compile_decls_correct_typed" "compile_decls_correct";
val _ = emit_exported "compile_exp_correct_typed" "compile_exp_correct";
val _ = emit_exported "compile_shape_n_def_typed" "compile_shape_n_def";
val _ = emit_exported "compile_shape_n_eq_typed" "compile_shape_n_eq";
val _ = emit_exported "compile_shape_n_no_name_typed" "compile_shape_n_no_name";
val _ = emit_exported "compile_shape_no_name_typed" "compile_shape_no_name";
val _ = emit_exported "compile_shapes_eq_map_typed" "compile_shapes_eq_map";
val _ = emit_exported "compile_top_no_names_typed" "compile_top_no_names";
val _ = emit_exported "compile_top_semantics_decls_typed" "compile_top_semantics_decls";
val _ = emit_exported "convert_code_def_typed" "convert_code_def";
val _ = emit_exported "convert_eshapes_def_typed" "convert_eshapes_def";
val _ = emit_exported "convert_res_def_typed" "convert_res_def";
val _ = emit_exported "convert_s_def_typed" "convert_s_def";
val _ = emit_exported "convert_v_def_typed" "convert_v_def";
val _ = emit_exported "decs_stcnames_compile_decs_typed" "decs_stcnames_compile_decs";
val _ = emit_exported "decs_stcnames_infos_ok_typed" "decs_stcnames_infos_ok";
val _ = emit_exported "decs_stcnames_to_get_names_typed" "decs_stcnames_to_get_names";
val _ = emit_exported "dropWhile_MAP_helper_typed" "dropWhile_MAP_helper";
val _ = emit_exported "dropWhile_afindi_typed" "dropWhile_afindi";
val _ = emit_exported "fields_in_order_reorder_noop_typed" "fields_in_order_reorder_noop";
val _ = emit_exported "flatten_convert_v_typed" "flatten_convert_v";
val _ = emit_exported "is_cont_res_def_typed" "is_cont_res_def";
val _ = emit_exported "is_wf_shape_compile_shape_typed" "is_wf_shape_compile_shape";
val _ = emit_exported "is_wf_shape_drop_typed" "is_wf_shape_drop";
val _ = emit_exported "mem_load_conversion_typed" "mem_load_conversion";
val _ = emit_exported "mem_load_flds_eq_typed" "mem_load_flds_eq";
val _ = emit_exported "mem_loads_EL_typed" "mem_loads_EL";
val _ = emit_exported "mem_loads_mem_typed" "mem_loads_mem";
val _ = emit_exported "opt_mmap_eq_some_el_typed" "opt_mmap_eq_some_el";
val _ = emit_exported "res_var_FMAP_MAP2_rev_typed" "res_var_FMAP_MAP2_rev";
val _ = emit_exported "res_vs_def_typed" "res_vs_def";
val _ = emit_exported "semantics_eq_typed" "semantics_eq";
val _ = emit_exported "shape_of_convert_v_typed" "shape_of_convert_v";
val _ = emit_exported "size_of_compile_shape_typed" "size_of_compile_shape";
val _ = emit_exported "size_of_sh_with_ctxt_drop_typed" "size_of_sh_with_ctxt_drop";
val _ = emit_exported "size_of_shape_compile_pass_eq_typed" "size_of_shape_compile_pass_eq";
val _ = emit_exported "struct_infos_ok_append_typed" "struct_infos_ok_append";
val _ = emit_exported "struct_infos_ok_cons_typed" "struct_infos_ok_cons";
val _ = emit_exported "struct_infos_ok_def_typed" "struct_infos_ok_def";
val _ = emit_exported "struct_infos_ok_drop_typed" "struct_infos_ok_drop";
val _ = emit_exported "v_flds_ok_append_typed" "v_flds_ok_append";
val _ = emit_exported "v_flds_ok_def_typed" "v_flds_ok_def";
val _ = capture "UNCURRY_EQ_o_SND_typed" "UNCURRY_EQ_o_SND";
val _ = capture "alookup_drop_helper_typed" "alookup_drop_helper";
val _ = capture "alookup_map_structs_ok_typed" "alookup_map_structs_ok";
val _ = capture "compile_decs_no_names_typed" "compile_decs_no_names";
val _ = capture "compile_decs_structs_typed" "compile_decs_structs";
val _ = capture "compile_exp_correct_mmap_helper_typed" "compile_exp_correct_mmap_helper";
val _ = capture "convert_code_locals_upd_typed" "convert_code_locals_upd";
val _ = capture "convert_res_eq_case1_typed" "convert_res_eq_case1";
val _ = capture "evaluate_structs_code_inv_typed" "evaluate_structs_code_inv";
val _ = capture "every_convert_v_eq_typed" "every_convert_v_eq";
val _ = capture "fupdate_elim2_typed" "fupdate_elim2";
val _ = capture "is_cont_res_eq_disj_typed" "is_cont_res_eq_disj";
val _ = capture "lookup_code_flds_ok_typed" "lookup_code_flds_ok";
val _ = capture "map_fst_eq_alookup_typed" "map_fst_eq_alookup";
val _ = capture "map_uncurry_zip_again_typed" "map_uncurry_zip_again";
val _ = capture "mem_loads_convert_helper_typed" "mem_loads_convert_helper";
val _ = capture "opt_mmap_eq_every_typed" "opt_mmap_eq_every";
val _ = capture "shape_of_convert_v_ind_typed" "shape_of_convert_v_ind";
val _ = capture "size_of_compile_shape_n_typed" "size_of_compile_shape_n";

(* Derived local theorems: the base statement is captured typed under
   the derived theorem name; the derivation is named in each comment,
   so the carriers are the base statement carriers. *)
(* mem_load_conversion_inst: SIMP_RULE bool_ss [] *)
val _ = emit_as "mem_load_conversion_inst_typed" (fetch_other ("pan_structsProof","mem_load_conversion"));
(* shape_of_convert_v_rev: GSYM *)
val _ = emit_as "shape_of_convert_v_rev_typed" (fetch_other ("pan_structsProof","shape_of_convert_v"));
