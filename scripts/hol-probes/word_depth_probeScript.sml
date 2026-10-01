(*
  Direct HOL-EVAL observations for CakeML `word_depth` call-tree max-depth and
  call-graph construction.

  Source:
    cakeml/compiler/backend/word_depthScript.sml
      call_tree (lines 20-27), max_depth (lines 24-35),
      mk_Branch (lines 37-45), call_graph (lines 47-86),
      full_call_graph (lines 88-94), max_depth_graphs (lines 96-105)

  `max_depth` reads frame sizes by `lookup` on a `num_map` (`num spt`). The
  rows below vary the tree shape (Leaf/Unknown/Const/Branch/Call), the frame
  lookup hit/miss, and nesting. A missing frame stays NONE (the original never
  invents a bound for unknown/cyclic calls). The `call_graph` /
  `full_call_graph` / `max_depth_graphs` rows exercise the `Skip` default,
  `Seq`, `Alloc`, `Install`, `Call` destination/lookup/short-circuit/guard
  cases, and the frame/code lookup hit and miss of `max_depth_graphs`.
*)
load "bossLib";
load "preamble";
load "word_depthTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_depthTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val fs10 = ``insert 1 10 (insert 2 20 (LN:num num_map))``;
val frame2 = ``insert 2 5 (LN:num num_map)``;
val funs_hit = ``insert 2 (0:num, Skip) (LN:(num # 'a wordLang$prog) num_map)``;

(* max_depth over the tree shapes *)
val _ = print_eval "leaf" ``max_depth (LN:num num_map) Leaf``
val _ = print_eval "unknown" ``max_depth (LN:num num_map) Unknown``
val _ = print_eval "const_leaf" ``max_depth (LN:num num_map) (Const 5 Leaf)``
val _ = print_eval "nested_const" ``max_depth (LN:num num_map) (Const 3 (Const 4 Leaf))``
val _ = print_eval "branch_max"
  ``max_depth (LN:num num_map) (Branch (Const 3 Leaf) (Const 5 Leaf))``
val _ = print_eval "branch_unknown"
  ``max_depth (LN:num num_map) (Branch (Const 3 Leaf) Unknown)``
val _ = print_eval "call_hit" ``max_depth ^fs10 (Call 1 Leaf)``
val _ = print_eval "call_miss" ``max_depth ^fs10 (Call 7 Leaf)``
val _ = print_eval "call_hit_nested" ``max_depth ^fs10 (Call 1 (Const 4 Leaf))``
val _ = print_eval "deep_calls"
  ``max_depth ^fs10 (Call 1 (Call 2 (Const 3 Leaf)))``
val _ = print_eval "branch_call"
  ``max_depth ^fs10 (Branch (Call 1 Leaf) (Const 2 Leaf))``
val _ = print_eval "unknown_deep"
  ``max_depth ^fs10 (Branch Unknown (Call 1 (Const 9 Leaf)))``

(* mk_Branch absorption and structural cases *)
val _ = print_eval "mb_identity" ``mk_Branch (Leaf:call_tree) Leaf``
val _ = print_eval "mb_leaf_left" ``mk_Branch (Leaf:call_tree) (Const 1 Leaf)``
val _ = print_eval "mb_leaf_right" ``mk_Branch (Const 1 (Leaf:call_tree)) Leaf``
val _ = print_eval "mb_unknown_left" ``mk_Branch (Unknown:call_tree) (Const 1 Leaf)``
val _ = print_eval "mb_unknown_right" ``mk_Branch (Const 1 (Leaf:call_tree)) Unknown``
val _ = print_eval "mb_branch"
  ``mk_Branch (Const 1 (Leaf:call_tree)) (Const 2 Leaf)``

(* call_graph structural and Call cases *)
val _ = print_eval "cg_default"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0 (Skip:'a wordLang$prog)``
val _ = print_eval "cg_seq"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0
      (Seq (Skip:'a wordLang$prog) Skip)``
val _ = print_eval "cg_alloc"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0
      (Alloc 7 ((LN:num_set), (LN:num_set)))``
val _ = print_eval "cg_install"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0
      (Install 0 0 0 0 ((LN:num_set), (LN:num_set)))``
val _ = print_eval "cg_call_dest_none"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 7 [] 0
      (Call NONE NONE [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_lookup_miss"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 7 [] 0
      (Call NONE (SOME 9) [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_tail_hit"
  ``call_graph ^funs_hit 7 [] 1 (Call NONE (SOME 2) [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_shortcircuit"
  ``call_graph ^funs_hit 7 [2] 1 (Call NONE (SOME 2) [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_guard"
  ``call_graph ^funs_hit 7 [] 0 (Call NONE (SOME 2) [] NONE:'a wordLang$prog)``

(* full_call_graph hit/miss *)
val _ = print_eval "fcg_miss"
  ``full_call_graph 9 (LN:(num # 'a wordLang$prog) num_map)``
val _ = print_eval "fcg_hit" ``full_call_graph 2 ^funs_hit``

(* max_depth_graphs empty / frame hit / frame miss / whole-code miss *)
val _ = print_eval "mdg_empty"
  ``max_depth_graphs (LN:num num_map) [] [] (LN:(num # 'a wordLang$prog) num_map)
      (LN:(num # 'a wordLang$prog) num_map)``
val _ = print_eval "mdg_frame_hit"
  ``max_depth_graphs ^frame2 [2] [] (LN:(num # 'a wordLang$prog) num_map) ^funs_hit``
val _ = print_eval "mdg_frame_miss"
  ``max_depth_graphs (LN:num num_map) [2] [] (LN:(num # 'a wordLang$prog) num_map) ^funs_hit``
val _ = print_eval "mdg_code_miss"
  ``max_depth_graphs (LN:num num_map) [9] [] (LN:(num # 'a wordLang$prog) num_map)
      (LN:(num # 'a wordLang$prog) num_map)``
