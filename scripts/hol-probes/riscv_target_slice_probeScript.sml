(* Literal original lem6 term and original BBLAST_PROVE construction. *)
load "preamble"; load "riscv_targetTheory"; load "blastLib";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;
val lem6 = blastLib.BBLAST_PROVE
  ``(((31 >< 0) (c: word64) : word32) ' 11 = c ' 11) /\
    (((63 >< 32) c : word32) ' 11 = c ' 43) /\
    (~(63 >< 32) c : word32 ' 11 = ~c ' 43) ``;
val _ = (print "slice_statement="; print_term (concl (GEN_ALL lem6)); print "\n");
val _ = print ("slice_types=" ^ String.concatWith ", "
  (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v))
    (#1 (strip_forall (concl (GEN_ALL lem6))))) ^ "\n");
val _ = print ("slice_hypotheses=" ^ Int.toString (length (hyp lem6)) ^ "\n");
val _ = (print "slice_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL lem6)))); print "\n");
val _ = OS.Process.exit OS.Process.success;
