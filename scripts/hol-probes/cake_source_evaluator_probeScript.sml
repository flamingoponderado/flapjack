load "evaluateTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
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
