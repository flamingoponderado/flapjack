(* Typed captures of the remaining mlstring token/field/substring declarations. *)
load "mlstringTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "TOKENS_eq_tokens_typed" mlstringTheory.TOKENS_eq_tokens;
val _ = show "collate_thm_typed" mlstringTheory.collate_thm;
val _ = show "splitl_SPLITL_typed" mlstringTheory.splitl_SPLITL;
val _ = show "TOKENS_eq_tokens_sym_typed" mlstringTheory.TOKENS_eq_tokens_sym;
val _ = show "fields_alt_typed" mlstringTheory.fields_alt;
val _ = show "tokens_alt_typed" mlstringTheory.tokens_alt;
val _ = show "tokens_append_typed" mlstringTheory.tokens_append;
val _ = show "str_findi_OLEAST_typed" mlstringTheory.str_findi_OLEAST;
val _ = show "isSubString_spec_typed" mlstringTheory.isSubString_spec;
val _ = show "OLEAST_LE_STEP_typed" mlstringTheory.OLEAST_LE_STEP;
val _ = show "fields_alt_aux_def_typed" mlstringTheory.fields_alt_aux_def;
val _ = show "str_app_list_opt_thm_typed" mlstringTheory.str_app_list_opt_thm;
val _ = show "tokens_alt_aux_def_typed" mlstringTheory.tokens_alt_aux_def;
val _ = show "fields_alt_fields_alt_aux_typed" mlstringTheory.fields_alt_fields_alt_aux;
val _ = show "splitl_aux_SPLITP_typed" mlstringTheory.splitl_aux_SPLITP;
val _ = show "TOKENS_eq_tokens_aux_typed" mlstringTheory.TOKENS_eq_tokens_aux;
val _ = show "tokens_alt_tokens_alt_aux_typed" mlstringTheory.tokens_alt_tokens_alt_aux;
