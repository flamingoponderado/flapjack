(* Typed source declarations for the presLang basics and display helpers.
   Free variables of a theorem conclusion are printed as a ∀* prefix; HOL
   stores them as implicitly universally quantified, so their order is not
   significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/src/finite_maps") ::
  !loadPath;
load "presLangTheory";
load "jsonLangTheory";
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

val thy = "presLang";

fun emitIn label sourceTheory name =
  case DB.lookup {Thy = sourceTheory, Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in " ^ sourceTheory ^ ">\n");

fun emit label name = emitIn label thy name;

val _ = emit "empty_item_def_typed" "empty_item_def";
val _ = emit "num_to_display_def_typed" "num_to_display_def";
val _ = emit "int_to_display_def_typed" "int_to_display_def";
val _ = emit "string_imp_def_typed" "string_imp_def";
val _ = emit "item_with_num_def_typed" "item_with_num_def";
val _ = emit "item_with_nums_def_typed" "item_with_nums_def";
val _ = emit "bool_to_display_def_typed" "bool_to_display_def";
val _ = emit "num_to_hex_def_typed" "num_to_hex_def";
val _ = emitIn "num_to_hex_digit_def_typed" "jsonLang" "num_to_hex_digit_def";
val _ = emit "num_to_hex_digit_eq_typed" "num_to_hex_digit_eq";
val _ = emit "separate_lines_def_typed" "separate_lines_def";
val _ = emit "num_to_hex_mlstring_def_typed" "num_to_hex_mlstring_def";
val _ = emit "word_to_display_def_typed" "word_to_display_def";
val _ = emit "item_with_word_def_typed" "item_with_word_def";
val _ = emit "map_to_append_def_typed" "map_to_append_def";
val _ = emit "source_to_strs_def_typed" "source_to_strs_def";
val _ = emit "flat_to_strs_def_typed" "flat_to_strs_def";

val _ = OS.Process.exit OS.Process.success;
