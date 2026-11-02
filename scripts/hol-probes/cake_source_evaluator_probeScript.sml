load "evaluateTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "source_evaluate_definition=" evaluateTheory.full_evaluate_def;
val _ = show_thm "con_check_definition=" semanticPrimitivesTheory.do_con_check_def;
val _ = show_thm "one_con_check_definition=" semanticPrimitivesTheory.one_con_check_def;
val _ = show_thm "build_conv_definition=" semanticPrimitivesTheory.build_conv_def;
val _ = show_thm "lit_same_type_definition=" semanticPrimitivesTheory.lit_same_type_def;
val _ = show_thm "same_type_definition=" semanticPrimitivesTheory.same_type_def;
val _ = show_thm "same_ctor_definition=" semanticPrimitivesTheory.same_ctor_def;
val _ = show_thm "ctor_same_type_definition=" semanticPrimitivesTheory.ctor_same_type_def;
val _ = show_thm "bool_type_num_definition=" semanticPrimitivesTheory.bool_type_num_def;
val _ = show_thm "bool_value_definition=" semanticPrimitivesTheory.Boolv_def;
val _ = show_thm "source_pmatch_definition=" semanticPrimitivesTheory.pmatch_def;
val _ = show_thm "can_pmatch_all_definition=" semanticPrimitivesTheory.can_pmatch_all_def;
val _ = show_thm "build_rec_env_definition=" semanticPrimitivesTheory.build_rec_env_def;
val _ = show_thm "find_recfun_definition=" semanticPrimitivesTheory.find_recfun_def;
val _ = show_thm "do_log_definition=" semanticPrimitivesTheory.do_log_def;
val _ = show_thm "do_if_definition=" semanticPrimitivesTheory.do_if_def;
val _ = show_thm "build_constrs_definition=" semanticPrimitivesTheory.build_constrs_def;
val _ = show_thm "build_tdefs_definition=" semanticPrimitivesTheory.build_tdefs_def;
val _ = show_thm "check_dup_ctors_definition=" semanticPrimitivesTheory.check_dup_ctors_def;
val _ = show_thm "combine_dec_result_definition=" semanticPrimitivesTheory.combine_dec_result_def;
val _ = show_thm "extend_dec_env_definition=" semanticPrimitivesTheory.extend_dec_env_def;
val _ = (print "build_constrs_nat="; print_term (rhs (concl (EVAL
  ``semanticPrimitives$build_constrs 3 [(«A», [4n; 5n])]``))); print "\n");
val _ = (print "build_constrs_bool="; print_term (rhs (concl (EVAL
  ``semanticPrimitives$build_constrs 3 [(«A», [T; F])]``))); print "\n");
val _ = (print "evaluate_type="; print_type (type_of ``evaluate$evaluate``); print "\n");
val _ = (print "match_type="; print_type (type_of ``evaluate$evaluate_match``); print "\n");
val _ = (print "decs_type="; print_type (type_of ``evaluate$evaluate_decs``); print "\n");
val exists_eq = CONV_RULE (DEPTH_CONV ETA_CONV) (prove (``∀a:'a. ∃x. a = x``, metis_tac []));
fun capture name tm =
 let val result = EVAL tm |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [exists_eq] THENC EVAL
   THENC SIMP_CONV (srw_ss()) [exists_eq] THENC EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV)))
 in print (name ^ "="); print_term (rhs (concl result)); print "\n" end;
val _ = capture "literal" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 10; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,s.refs,r)) (evaluate st env [Lit (IntLit 7)])``;
val _ = capture "raise" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 10; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,s.refs,r)) (evaluate st env [Raise (Lit (IntLit 7))])``;
val _ = capture "type_error" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 10; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,s.refs,r)) (evaluate st env [If (Lit (IntLit 1)) (Lit (IntLit 2)) (Lit (IntLit 3))])``;
val _ = capture "call_zero" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 0; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,s.refs,r)) (evaluate st env [App Opapp [Fun «x» (Var (Short «x»)); Lit (IntLit 9)]])``;
val _ = capture "call_one" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 1; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,s.refs,r)) (evaluate st env [App Opapp [Fun «x» (Var (Short «x»)); Lit (IntLit 9)]])``;
val _ = capture "match_bind" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 4; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,s.refs,r)) (evaluate_match st env (Litv (IntLit 7)) [(Pvar «x»,Var (Short «x»))] bind_exn_v)``;
val _ = capture "match_empty" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 4; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,s.refs,r)) (evaluate_match st env (Litv (IntLit 7)) [] bind_exn_v)``;
val _ = capture "declaration" ``let st = (ARB:num semanticPrimitives$state) with <|clock := 4; refs := []|> in
 let env = <|v := Bind [] []; c := Bind [] []|> in
 (λ(s,r). (s.clock,case r of Rval e => nsLookup e.v (Short «x») | _ => NONE))
   (evaluate_decs st env [Dlet (Locs UNKNOWNpt UNKNOWNpt) (Pvar «x») (Lit (IntLit 7))])``;
