load "source_evalProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_term label tm = (print label; print_term tm; print "\n");
val _ = show_term "is_insert_decs="
  ``source_evalProof$is_insert_oracle ci f (SOME (semanticPrimitives$EvalDecs eds))``;
val _ = show_term "declare_env_adjust="
  ``semanticPrimitives$declare_env (source_evalProof$adjust_oracle ci f es) env =
    (case semanticPrimitives$declare_env es env of NONE => NONE
     | SOME (x, es2) => SOME (x, source_evalProof$adjust_oracle ci f es2))``;
val _ = show_term "adjust_oracle_reset="
  ``source_evalProof$adjust_oracle ci f (semanticPrimitives$reset_env_generation es1 es2) =
    semanticPrimitives$reset_env_generation (source_evalProof$adjust_oracle ci f es1)
      (source_evalProof$adjust_oracle ci f es2)``;
val _ = show_term "is_insert_related="
  ``source_evalProof$is_insert_oracle ci f (SOME (semanticPrimitives$EvalOracle es)) ==>
    (es2.custom_do_eval = es.custom_do_eval /\ es2.oracle = es.oracle) ==>
    source_evalProof$is_insert_oracle ci f (SOME (semanticPrimitives$EvalOracle es2))``;
val _ = show_term "is_insert_reset="
  ``source_evalProof$is_insert_oracle ci f (semanticPrimitives$reset_env_generation es1 es2) =
    source_evalProof$is_insert_oracle ci f es2``;
val _ = show_term "declare_env_is_insert="
  ``semanticPrimitives$declare_env es env = SOME (x, es2) /\
    source_evalProof$is_insert_oracle ci f es ==> source_evalProof$is_insert_oracle ci f es2``;
val _ = show_term "do_eval_adjust="
  ``semanticPrimitives$do_eval vs es = SOME (env1, decs, es1) /\
    source_evalProof$is_insert_oracle ci f es ==>
    (semanticPrimitives$do_eval vs (source_evalProof$adjust_oracle ci (g o f) es) =
      SOME (env1, g decs, source_evalProof$adjust_oracle ci (g o f) es1) \/
     semanticPrimitives$do_eval vs (source_evalProof$adjust_oracle ci (g o f) es) =
      SOME (env1, decs, source_evalProof$adjust_oracle ci (g o f) es1)) /\
    source_evalProof$is_insert_oracle ci f es1``;
