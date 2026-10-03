load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t = DB.fetch "lab_to_targetProof" "mc_conf_ok_def";
val _ = capture "mc_conf_ok_def" t;
val _ = types "mc_conf_ok_def_types" t;
val _ = print("mc_conf_ok_def_hypotheses=" ^ Int.toString(length(hyp t)) ^ "\n");
val _ = show_types := false;
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO th))); print "\n");
val _ = checked "full_contract" (prove(
  ``mc_conf_ok (mc:('a,'b,'c) targetSem$machine_config) <=>
    misc$good_dimindex (:'a) /\ asmProps$encoder_correct mc.target /\
    asm$reg_ok mc.ptr_reg mc.target.config /\
    asm$reg_ok mc.len_reg mc.target.config /\
    asm$reg_ok mc.ptr2_reg mc.target.config /\
    asm$reg_ok mc.len2_reg mc.target.config /\
    asm$reg_ok (case mc.target.config.link_reg of NONE => 0 | SOME n => n)
      mc.target.config /\ asmProps$enc_ok mc.target.config``,
  simp [mc_conf_ok_def]));
val _ = checked "encoder_correct" (prove(
  ``mc_conf_ok mc ==> asmProps$encoder_correct mc.target``,
  simp [mc_conf_ok_def]));
val _ = checked "target_ok" (prove(
  ``mc_conf_ok mc ==> asmProps$target_ok mc.target``,
  simp [mc_conf_ok_def, asmPropsTheory.encoder_correct_def]));
val _ = checked "dimension8_rejected" (prove(
  ``~mc_conf_ok (mc:(8,'b,'c) targetSem$machine_config)``,
  simp [mc_conf_ok_def, miscTheory.good_dimindex_def]));
val _ = checked "dimension128_rejected" (prove(
  ``~mc_conf_ok (mc:(128,'b,'c) targetSem$machine_config)``,
  simp [mc_conf_ok_def, miscTheory.good_dimindex_def]));
