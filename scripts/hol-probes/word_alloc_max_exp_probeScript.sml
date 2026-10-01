load "preamble";
load "wordConvsTheory";
open bossLib HolKernel Parse preamble wordLangTheory wordConvsTheory listTheory arithmeticTheory;
fun out label q = (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
val _ = out "me_const" ``let e = (Const 999w:64 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_lookup" ``let e = (Lookup CurrHeap:64 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_var" ``let e = (Var 1208925819614629174706176:64 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_load" ``let e = (Load (Load (Var 7)):32 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_empty" ``let e = (Op Add []:64 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_nested" ``let e = (Op Add [Var 2; Op Sub [Var 19; Var 3]; Load (Var 7)]:64 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_duplicate" ``let e = (Op Add [Var 9; Var 9; Var 2]:80 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_shiftleft" ``let e = (Shift Lsl (Var 23) (Var 4):64 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_shiftright" ``let e = (Shift Lsr (Const 1w) (Var 43):1 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val _ = out "me_zero" ``let e = (Op Add [Const 99w; Lookup CurrHeap; Op Sub []]:64 wordLang$exp) in (max_var_exp e, every_var_exp (\x. x <= max_var_exp e) e, every_var_exp (\x. x < max_var_exp e) e)``;
val th = Q.prove (`∀exp.
    every_var_exp (λx. x≤ max_var_exp exp) exp`, ho_match_mp_tac max_var_exp_ind>>
  srw_tac[][every_var_exp_def,max_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>res_tac>>
  match_mp_tac every_var_exp_mono>>
  first_assum $ irule_at (Pos last)>>
  srw_tac[][]>>
  irule LE_TRANS >>
  irule_at (Pos (el 2)) MAX_LIST_PROPERTY >>
  simp[MEM_MAP,PULL_EXISTS] >>
  first_x_assum (fn x => irule_at (Any) x >> first_x_assum irule));
val _ = (print "me_original_theorem="; print_thm th; print "\n");
