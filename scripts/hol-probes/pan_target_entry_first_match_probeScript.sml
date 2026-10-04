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
fun observe label program =
  let val (ts,tys) = match_term programVar program;
      val instantiated = subst ts (inst tys firstMain)
  in print(label ^ "=" ^ term_to_string(rhs(concl(EVAL instantiated))) ^ "\n") end;
val _ = observe "empty" ``[] : 8 decl list``;
val _ = observe "missing" ``[Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const (1w : 8 word)); return := One|>; Function <|name := «g»; inline := F; export := F; params := []; body := Return(Const (3w : 8 word)); return := One|>] : 8 decl list``;
val _ = observe "head" ``[Function <|name := «main»; inline := F; export := F; params := []; body := Return(Const (2w : 8 word)); return := One|>; Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const (1w : 8 word)); return := One|>; Function <|name := «g»; inline := F; export := F; params := []; body := Return(Const (3w : 8 word)); return := One|>; Function <|name := «main»; inline := F; export := T; params := []; body := Return(Const (4w : 8 word)); return := One|>] : 8 decl list``;
val _ = observe "duplicates" ``[Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const (1w : 8 word)); return := One|>; Function <|name := «main»; inline := F; export := F; params := []; body := Return(Const (2w : 8 word)); return := One|>; Function <|name := «g»; inline := F; export := F; params := []; body := Return(Const (3w : 8 word)); return := One|>; Function <|name := «main»; inline := F; export := T; params := []; body := Return(Const (4w : 8 word)); return := One|>] : 8 decl list``;
val _ = observe "nonfunction" ``[ExnDecl «E» One; Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const (1w : 8 word)); return := One|>; Function <|name := «main»; inline := F; export := F; params := []; body := Return(Const (2w : 8 word)); return := One|>; Function <|name := «g»; inline := F; export := F; params := []; body := Return(Const (3w : 8 word)); return := One|>; Function <|name := «main»; inline := F; export := T; params := []; body := Return(Const (4w : 8 word)); return := One|>] : 8 decl list``;
