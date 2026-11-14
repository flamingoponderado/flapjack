(* Typed source declarations for sptree (task 154). Free variables of a
   theorem conclusion are printed as a ∀* prefix; HOL stores them as
   implicitly universally quantified, so their order is not significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/src/finite_maps") ::
  !loadPath;
load "sptreeTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th =
  let val fvs = free_vars (concl th) in
    (print (label ^ "=");
     if null fvs then ()
     else (print "∀*";
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

val thy = "sptree";
val datatypeNames =
  List.map (fn n => String.substring (n, 0, String.size n - 6))
    (List.filter (fn n => String.isSuffix "_Axiom" n)
      (List.map #1 (DB.theorems thy)));

fun ctorsOf d =
  let
    fun try n =
      (TypeBase.constructors_of
         (mk_type (d, List.tabulate (n, fn _ => alpha)))
       handle _ => [])
    fun first [] = []
      | first (n :: ns) =
          let val cs = try n in if null cs then first ns else cs end
  in first [0, 1, 2, 3, 4] end;

val allCtors = List.concat (List.map ctorsOf datatypeNames);

fun emitDatatype label name =
  let val cs = ctorsOf name in
    if null cs then false
    else
      (print (label ^ "=");
       print (String.concatWith "; "
         (List.map (fn c =>
            let val (n, t) = dest_const c
            in n ^ ":" ^ type_to_string t end) cs));
       print "\n"; true)
  end;

fun ctorType name =
  case List.filter (fn c => #1 (dest_const c) = name) allCtors of
    [] => NONE
  | c :: _ => SOME (type_to_string (#2 (dest_const c)));

fun emit label name =
  case DB.lookup {Thy = thy, Name = name} of
    SOME (th, _) => show label th
  | NONE =>
      if emitDatatype label name then ()
      else case ctorType name of
        SOME s => (print (label ^ "="); print s; print "\n")
      | NONE => print (label ^ "=<not found in " ^ thy ^ ">\n");

val _ = emit "domain_def_typed" "domain_def";
val _ = emit "domain_fromList_typed" "domain_fromList";
(* local theorem: typed statement parse *)
val MEM_toListA_statement =
  ``!t acc x. MEM x (toListA acc t) <=> (MEM x acc \/ ?k. lookup k t = SOME x)``;
val _ = (print "MEM_toListA_typed="; print_term MEM_toListA_statement; print "\n");
val _ = emit "MEM_toList_typed" "MEM_toList";
val _ = emit "domain_lookup_typed" "domain_lookup";
val _ = emit "spt_typed" "spt";
val _ = emit "lookup_def_typed" "lookup_def";
val _ = emit "insert_def_typed" "insert_def";
val _ = emit "mk_BN_def_typed" "mk_BN_def";
val _ = emit "mk_BS_def_typed" "mk_BS_def";
val _ = emit "union_def_typed" "union_def";
val _ = emit "fromAList_def_typed" "fromAList_def";
val _ = emit "size_def_typed" "size_def";
val _ = emit "delete_def_typed" "delete_def";
val _ = emit "fromList_def_typed" "fromList_def";
val _ = emit "lookup_mk_wf_typed" "lookup_mk_wf";
val _ = emit "domain_inter_typed" "domain_inter";
val _ = emit "domain_union_typed" "domain_union";
val _ = emit "lookup_inter_typed" "lookup_inter";
val _ = emit "lookup_union_typed" "lookup_union";
val _ = emit "wf_def_typed" "wf_def";
val _ = emit "filter_v_def_typed" "filter_v_def";
val _ = emit "lookup_filter_v_typed" "lookup_filter_v";
val _ = emit "lrnext_def_typed" "lrnext_def";
val _ = emit "toAList_def_typed" "toAList_def";
val _ = emit "foldi_def_typed" "foldi_def";
val _ = emit "foldi_FOLDR_toAList_typed" "foldi_FOLDR_toAList";
val _ = emit "insert_unchanged_typed" "insert_unchanged";
val _ = emit "inter_eq_def_typed" "inter_eq_def";
val _ = emit "lookup_inter_eq_typed" "lookup_inter_eq";
val _ = emit "domain_map_typed" "domain_map";
val _ = emit "lookup_map_typed" "lookup_map";
val _ = emit "map_def_typed" "map_def";
val _ = emit "map_fromAList_typed" "map_fromAList";
val _ = emit "map_insert_typed" "map_insert";
val _ = emit "map_union_typed" "map_union";
val _ = emit "wf_map_typed" "wf_map";
val _ = emit "mapi_def_typed" "mapi_def";
val _ = emit "mapi0_def_typed" "mapi0_def";
val _ = emit "lookup_mapi_typed" "lookup_mapi";
val _ = emit "lookup_mapi0_typed" "lookup_mapi0";
val _ = emit "wf_mapi_typed" "wf_mapi";
val _ = emit "wf_mk_BN_typed" "wf_mk_BN";
val _ = emit "wf_mk_BS_typed" "wf_mk_BS";
val _ = emit "subspt_def_typed" "subspt_def";
val _ = emit "subspt_FOLDL_union_typed" "subspt_FOLDL_union";
val _ = emit "subspt_lookup_typed" "subspt_lookup";
val _ = emit "subspt_trans_typed" "subspt_trans";
val _ = emit "subspt_union_typed" "subspt_union";
val _ = emit "ALL_DISTINCT_MAP_FST_toAList_typed" "ALL_DISTINCT_MAP_FST_toAList";
val _ = emit "domain_difference_typed" "domain_difference";
val _ = emit "domain_fromAList_typed" "domain_fromAList";
val _ = emit "domain_insert_typed" "domain_insert";
val _ = emit "MEM_toAList_typed" "MEM_toAList";
val _ = emit "insert_union_typed" "insert_union";
val _ = emit "union_assoc_typed" "union_assoc";
val _ = emit "union_insert_LN_typed" "union_insert_LN";
val _ = emit "union_num_set_sym_typed" "union_num_set_sym";
val _ = emit "spt_eq_thm_typed" "spt_eq_thm";
val _ = emit "insert_notEmpty_typed" "insert_notEmpty";
val _ = emit "lookup_difference_typed" "lookup_difference";
val _ = emit "wf_delete_typed" "wf_delete";
val _ = emit "wf_difference_typed" "wf_difference";
val _ = emit "wf_fromAList_typed" "wf_fromAList";
val _ = emit "wf_insert_typed" "wf_insert";
val _ = emit "wf_inter_typed" "wf_inter";
val _ = emit "wf_union_typed" "wf_union";
val _ = emit "inter_def_typed" "inter_def";
val _ = emit "mk_wf_def_typed" "mk_wf_def";
val _ = emit "toList_def_typed" "toList_def";
val _ = emit "toListA_def_typed" "toListA_def";

val _ = OS.Process.exit OS.Process.success;
