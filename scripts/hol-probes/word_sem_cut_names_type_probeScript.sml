load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib HolKernel Parse preamble wordSemTheory;
fun observeType label term =
  (print (label ^ "="); print_type (type_of term); print "\n");
val _ = observeType "cut_names_type" ``cut_names``;
val _ = observeType "cut_envs_type" ``cut_envs``;
val _ = observeType "cut_env_type" ``cut_env``;
