load "bossLib";
load "preamble";
load "targetSemTheory";
open bossLib HolKernel Parse preamble targetSemTheory wordLangTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t = DB.fetch "targetSem" "good_init_state_def";
val _ = capture "good_init_state_def" t;
val _ = types "good_init_state_def_types" t;
val _ = print("good_init_state_def_hypotheses=" ^ Int.toString(length(hyp t)) ^ "\n");
val _ = show_types := false;
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO th))); print "\n");
val _ = checked "word_memory" (prove(
  ``good_init_state mc ms bytes space t m dm sdm ==>
    !a. ?w. m (alignment$byte_align a) = Word w``,
  simp [good_init_state_def] >> metis_tac []));
val _ = checked "entry_bound" (prove(
  ``good_init_state mc ms bytes space t m dm sdm /\
      index < LENGTH mc.ffi_names ==> index < LENGTH mc.ffi_entry_pcs``,
  simp [good_init_state_def, start_pc_ok_def] >> metis_tac []));
val _ = checked "space_bound" (prove(
  ``good_init_state (mc:('a,'b,'c) machine_config) ms bytes space t m dm sdm ==>
    space + LENGTH bytes < dimword (:'a)``,
  simp [good_init_state_def]));
val _ = checked "space_overflow_rejected" (prove(
  ``dimword (:'a) <= space + LENGTH bytes ==>
    ~good_init_state (mc:('a,'b,'c) machine_config) ms bytes space t m dm sdm``,
  simp [good_init_state_def]));
