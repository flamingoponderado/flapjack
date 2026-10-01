(* Full local theorem is re-elaborated from its literal original proof.
   Observations run the faithful original evaluator; free-state fields stay free. *)
load "bossLib";
load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordLangTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val _ = computeLib.add_funs [evaluate_def];
val mov_eval_head_replay = prove (``  evaluate(Move p moves,st) = (NONE,rst) ∧
  y ∈ domain st.locals ∧
  ¬MEM y (MAP FST moves) ∧
  ¬MEM x (MAP FST moves)
  ⇒
  evaluate(Move p ((x,y)::moves),st) = (NONE, rst with locals:=insert x (THE (lookup y st.locals)) rst.locals)``,
  full_simp_tac(srw_ss())[evaluate_def,get_vars_def,get_var_def,domain_lookup]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>
  full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
  qpat_x_assum `A=rst` (sym_sub_tac)>>full_simp_tac(srw_ss())[]);
val _ = (print "mh_original_statement="; print_thm mov_eval_head_replay; print "\n");
val _ = print ("mh_original_types=" ^ String.concatWith ";" (map (fn v => term_to_string v ^ ":" ^ type_to_string (type_of v)) (free_vars (concl mov_eval_head_replay))) ^ "\n");
val _ = print ("mh_original_state_type=" ^ type_to_string(type_of ``st:(32,unit,unit) wordSem$state``) ^ "\n");
fun out label q = (print(label ^ "=");print_term(rconc(EVAL q));print "\n");
val _ = out "mh_empty" ``let st = ((s:(1,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 1w)]; clock := 17|>) in let (r,t) = evaluate(Move 0 ((2,1)::[]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_single" ``let st = ((s:(32,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w);(4,Word 7w)]; clock := 17|>) in let (r,t) = evaluate(Move 7 ((5,1)::[(4,1)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_parallel" ``let st = ((s:(64,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w);(2,Loc 7 8);(4,Word 3w);(5,Word 4w)]; clock := 17|>) in let (r,t) = evaluate(Move 9 ((6,2)::[(4,1);(5,2)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_overwrite" ``let st = ((s:(80,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w);(5,Word 123w)]; clock := 17|>) in let (r,t) = evaluate(Move 99 ((5,1)::[(4,1)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_self" ``let st = ((s:(32,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w);(5,Word 12w)]; clock := 17|>) in let (r,t) = evaluate(Move 4 ((5,5)::[(4,1)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_same_source" ``let st = ((s:(1,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 1w)]; clock := 17|>) in let (r,t) = evaluate(Move 3 ((6,1)::[(4,1);(5,1)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_malformed" ``let st = ((s:(64,unit,unit) wordSem$state) with <|locals := BS (BN LN LN) (Word 7w) (LS (Loc 3 4)); clock := 17|>) in let (r,t) = evaluate(Move 8 ((5,0)::[(4,1)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_huge" ``let st = ((s:(80,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w)]; clock := 17|>) in let (r,t) = evaluate(Move 0 ((1208925819614629174706176,1)::[(4,1)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_missing_source" ``let st = ((s:(32,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w)]; clock := 17|>) in let (r,t) = evaluate(Move 0 ((5,2)::[]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_duplicate_destination" ``let st = ((s:(32,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w)]; clock := 17|>) in let (r,t) = evaluate(Move 0 ((5,1)::[(5,1)]),st) in (r,toAList t.locals,t.clock)``;
val _ = out "mh_bad_tail" ``let st = ((s:(64,unit,unit) wordSem$state) with <|locals := fromAList [(1,Word 9w)]; clock := 17|>) in let (r,t) = evaluate(Move 0 ((5,1)::[(4,1);(4,1)]),st) in (r,toAList t.locals,t.clock)``;
