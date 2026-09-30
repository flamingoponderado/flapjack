(* Original source213-247 compile_decs/get_names/compile_top.
   HOL_PROBE_ONLY=pan_structs_compile_decls_probeScript.sml
   scripts/hol-probes/regenerate.sh *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
open bossLib HolKernel Parse preamble;
val fields = ``[(«left», One); («right», Comb [One; One])]``;
val initial = ``<| structs := []; locals := []; globals := [] |>``;
val ctxt = ``^initial with structs := [(«Pair», ^fields)]``;
val ds =
  ``[Function <| name := «read»; inline := T; export := T;
      params := [(«p», Named «Pair»)];
      body := Return (NField «right» (Var Global «g»)); return := Named «Pair» |>;
     Decl (Named «Pair») «g»
       (NStruct «Pair» [(«left», Const (1w : 8 word)); («right», Const 2w)]);
     Name «Ignored» []; ExnDecl «E» (Named «Pair»)]``;
fun print_eval label q =
  let val th = EVAL q
  in print (label ^ "="); print_term (rconc th); print "\n" end;
val _ = print_eval "empty" ``pan_structs$compile_decs ^ctxt ([] : 8 word decl list)``;
val _ = print_eval "decs" ``pan_structs$compile_decs ^ctxt ^ds``;
val _ = print_eval "names"
  ``pan_structs$get_names ^initial ((Name «Pair» ^fields)::^ds)``;
val _ = print_eval "top" ``pan_structs$compile_top ((Name «Pair» ^fields)::^ds)``;
val _ = print_eval "shadow"
  ``pan_structs$get_names ^ctxt ([Name «Pair» []] : 8 word decl list)``;
