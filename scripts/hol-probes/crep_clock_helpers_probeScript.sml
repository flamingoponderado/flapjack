(*
  Direct HOL observations for the crepSem clock-invariance helpers
  `clock_eq_simp`, `sh_mem_load_clock`, `sh_mem_store_clock` and
  `sh_mem_op_clock`.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:392-419.

  The HOL helper theorems themselves are `[local]` in the script, so the probe
  inlines their defining equations and evaluates concrete instances.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;

val s =
  ``(<| locals := (FEMPTY |+ (1, Word (5w:8 word)));
        globals := FEMPTY;
        code := FEMPTY;
        memory := K (Word (0w:8 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 7;
        be := F;
        ffi := ARB;
        base_addr := (0w:8 word);
        top_addr := (100w:8 word) |> : (8, unit) crepSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "clock_eq_simp_set_var"
  ``(set_var 1 (Word (5w:8 word)) ^s).clock = ^s.clock``;
val _ = print_eval "clock_eq_simp_empty_locals"
  ``(empty_locals ^s).clock = ^s.clock``;
val _ = print_eval "clock_eq_simp_set_globals"
  ``(set_globals (0w:5 word) (Word (5w:8 word)) ^s).clock = ^s.clock``;

val _ = print_eval "sh_mem_load_clock"
  ``case sh_mem_load 1 (3w:8 word) 0 ^s of
      (r,s') => s'.clock = s.clock``;
val _ = print_eval "sh_mem_load_clock_nonzero"
  ``case sh_mem_load 1 (3w:8 word) 1 ^s of
      (r,s') => s'.clock = s.clock``;
val _ = print_eval "sh_mem_store_clock"
  ``case sh_mem_store 1 (3w:8 word) 0 ^s of
      (r,s') => s'.clock = s.clock``;
val _ = print_eval "sh_mem_store_clock_nonzero"
  ``case sh_mem_store 1 (3w:8 word) 1 ^s of
      (r,s') => s'.clock = s.clock``;
val _ = print_eval "sh_mem_op_clock_load"
  ``case sh_mem_op Load 1 (3w:8 word) ^s of
      (r,s') => s'.clock = s.clock``;
val _ = print_eval "sh_mem_op_clock_store8"
  ``case sh_mem_op Store8 1 (3w:8 word) ^s of
      (r,s') => s'.clock = s.clock``;
