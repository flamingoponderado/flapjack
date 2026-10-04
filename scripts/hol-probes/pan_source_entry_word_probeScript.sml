load "preamble";
load "pan_to_targetTheory";
open HolKernel Parse bossLib preamble pan_to_targetTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th =
  let val full = GEN_ALL th in
    if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
    print(label ^ "=" ^ term_to_string(concl full) ^ "\n")
  end;
val full = SPEC_ALL compile_prog_def;
val firstMain = snd(dest_comb(rhs(concl full)));
val programVar = mk_var("prog", type_of firstMain);
fun first program =
  let val (ts,tys) = match_term programVar program;
      val instantiated = subst ts (inst tys firstMain)
  in instantiated end;
fun emit label q = print(label ^ "=" ^ term_to_string(rhs(concl(EVAL q))) ^ "\n");
val _ = emit "empty_word" ``pan_to_word$compile_prog RISC_V ^(first ``([] : 8 decl list)``)``;
val missing = ``[Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const (7w : 8 word)); return := One|>] : 8 decl list``;
val _ = emit "missing_word" ``pan_to_word$compile_prog RISC_V ^(first missing)``;
