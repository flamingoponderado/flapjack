(* Typed captures of the panProps `with_shape` lemmas
   (panPropsScript.sml:265, :286, :307, :328, :341, :357, :409, :452, :568).
   Each row prints the exported theorem's conclusion with inferred types
   (`show_types`) plus its hypothesis count, so the Lean ports can be compared
   against the original carriers (`shape`, `mlstring` names, list carriers). *)
load "bossLib";
load "preamble";
load "panSemTheory";
load "panPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val _ = (print "length_with_shape_eq_shape_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.length_with_shape_eq_shape);
  print "\n");
val _ = print ("length_with_shape_eq_shape_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.length_with_shape_eq_shape)) ^ "\n");

val _ = (print "all_distinct_with_shape_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.all_distinct_with_shape);
  print "\n");
val _ = print ("all_distinct_with_shape_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.all_distinct_with_shape)) ^ "\n");

val _ = (print "el_mem_with_shape_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.el_mem_with_shape);
  print "\n");
val _ = print ("el_mem_with_shape_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.el_mem_with_shape)) ^ "\n");

val _ = (print "mem_with_shape_length_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.mem_with_shape_length);
  print "\n");
val _ = print ("mem_with_shape_length_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.mem_with_shape_length)) ^ "\n");

val _ = (print "with_shape_el_take_drop_eq_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.with_shape_el_take_drop_eq);
  print "\n");
val _ = print ("with_shape_el_take_drop_eq_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.with_shape_el_take_drop_eq)) ^ "\n");

val _ = (print "all_distinct_with_shape_distinct_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.all_distinct_with_shape_distinct);
  print "\n");
val _ = print ("all_distinct_with_shape_distinct_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.all_distinct_with_shape_distinct)) ^ "\n");

val _ = (print "all_distinct_disjoint_with_shape_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.all_distinct_disjoint_with_shape);
  print "\n");
val _ = print ("all_distinct_disjoint_with_shape_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.all_distinct_disjoint_with_shape)) ^ "\n");

val _ = (print "all_distinct_mem_zip_disjoint_with_shape_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.all_distinct_mem_zip_disjoint_with_shape);
  print "\n");
val _ = print ("all_distinct_mem_zip_disjoint_with_shape_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.all_distinct_mem_zip_disjoint_with_shape)) ^ "\n");

val _ = (print "el_el_with_shape_typed=";
  Lib.with_flag (Globals.show_types, true)
    print_term (concl panPropsTheory.el_el_with_shape);
  print "\n");
val _ = print ("el_el_with_shape_hypotheses=" ^
  Int.toString (length (hyp panPropsTheory.el_el_with_shape)) ^ "\n");
