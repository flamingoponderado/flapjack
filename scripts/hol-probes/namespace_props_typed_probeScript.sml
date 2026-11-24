(* Typed source declarations for namespaceProps (task 148). *)
load "preamble";
load "namespacePropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble namespacePropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="namespaceProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by namespaceProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of namespaceProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "nsLookup_nsEmpty_typed" "nsLookup_nsEmpty";
val _ = emit "nsLookupMod_nsEmpty_typed" "nsLookupMod_nsEmpty";
val _ = emit "nsLookup_nsLift_typed" "nsLookup_nsLift";
val _ = emit "nsLookupMod_nsLift_typed" "nsLookupMod_nsLift";
val _ = emit "nsDom_nsLift_typed" "nsDom_nsLift";
val _ = emit "nsDomMod_nsLift_typed" "nsDomMod_nsLift";
val _ = emit "nsDom_nsAppend_equal_typed" "nsDom_nsAppend_equal";
val _ = emit "nsAppend_nsEmpty_typed" "nsAppend_nsEmpty";
val _ = emit "nsLookup_nsBind_typed" "nsLookup_nsBind";
val _ = emit "nsAppend_assoc_typed" "nsAppend_assoc";
val _ = emit "nsAppend_to_nsBindList_typed" "nsAppend_to_nsBindList";
val _ = emit "nsAll_nsAppend_typed" "nsAll_nsAppend";
val _ = emit "nsAll_nsBind_typed" "nsAll_nsBind";
val _ = emit "nsAll_nsSing_typed" "nsAll_nsSing";
val _ = emit "nsAll2_nsAppend_typed" "nsAll2_nsAppend";

(* Identifiers, empty namespaces, binding and singletons (task 273). *)
val _ = emit "mk_id_11_typed" "mk_id_11";
val _ = emit "id_to_mods_mk_id_typed" "id_to_mods_mk_id";
val _ = emit "id_to_namemods_mk_id_typed" "id_to_namemods_mk_id";
val _ = emit "mk_id_surj_typed" "mk_id_surj";
val _ = emit "mk_id_thm_typed" "mk_id_thm";
val _ = emit "alist_to_ns_nil_typed" "alist_to_ns_nil";
val _ = emit "nsSub_nsEmpty_typed" "nsSub_nsEmpty";
val _ = emit "nsAll_nsEmpty_typed" "nsAll_nsEmpty";
val _ = emit "nsAll2_nsEmpty_typed" "nsAll2_nsEmpty";
val _ = emit "nsDom_nsEmpty_typed" "nsDom_nsEmpty";
val _ = emit "nsDomMod_nsEmpty_typed" "nsDomMod_nsEmpty";
val _ = emit "nsMap_nsEmpty_typed" "nsMap_nsEmpty";
val _ = emit "nsBind_nsEmpty_typed" "nsBind_nsEmpty";
val _ = emit "nsAll_mono_typed" "nsAll_mono";
val _ = emit "alist_to_ns_cons_typed" "alist_to_ns_cons";
val _ = emit "nsAppend_nsBind_typed" "nsAppend_nsBind";
val _ = emit "nsAppend_alist_to_ns_typed" "nsAppend_alist_to_ns";
val _ = emit "nsBind_11_typed" "nsBind_11";
val _ = emit "nsLookupMod_alist_to_ns_typed" "nsLookupMod_alist_to_ns";
val _ = emit "alist_to_ns_11_typed" "alist_to_ns_11";
val _ = emit "nsAppend_nsSing_typed" "nsAppend_nsSing";
val _ = emit "nsLookup_nsSing_typed" "nsLookup_nsSing";
val _ = emit "nsMap_nsSing_typed" "nsMap_nsSing";
val _ = emit "nsLookupMod_nsSing_typed" "nsLookupMod_nsSing";
val _ = emit "nsDom_nsSing_typed" "nsDom_nsSing";
val _ = emit "nsDomMod_nsSing_typed" "nsDomMod_nsSing";

(* Sub-relations, domains and lookup (task 273). *)
val _ = emit "eALL_T_typed" "eALL_T";
val _ = emit "nsLookup_nsAll_typed" "nsLookup_nsAll";
val _ = emit "nsLookup_nsDom_typed" "nsLookup_nsDom";
val _ = emit "nsLift_nsMap_typed" "nsLift_nsMap";
val _ = emit "nsLookup_Bind_v_some_typed" "nsLookup_Bind_v_some";
val _ = emit "nsSub_refl_typed" "nsSub_refl";
val _ = emit "nsDomMod_alist_to_ns_typed" "nsDomMod_alist_to_ns";
val _ = emit "nsSub_nsBind_typed" "nsSub_nsBind";
val _ = emit "nsAll2_nsBind_typed" "nsAll2_nsBind";
val _ = emit "nsSub_conj_typed" "nsSub_conj";
val _ = emit "nsAll2_conj_typed" "nsAll2_conj";
