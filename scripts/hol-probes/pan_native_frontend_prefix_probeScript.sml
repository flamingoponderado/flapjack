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
val source = ``[Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const (7w : 8 word)); return := One|>;
 Function <|name := «main»; inline := F; export := F; params := []; body := Call NONE «f» []; return := One|>] : 8 decl list``;
val moved = first source;
val cake = ``pan_globals$compile_top (pan_structs$compile_top (pan_simp$compile_prog ^moved)) «main»``;
val _ = emit "cake_declarations" cake;
val _ = emit "raw_crep" ``pan_to_crep$compile_prog ^cake``;
val _ = emit "original_loop" ``crep_to_loop$compile_prog RISC_V (pan_to_crep$compile_prog ^cake)``;
