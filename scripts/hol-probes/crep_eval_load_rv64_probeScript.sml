(*
  Direct HOL observations for the crepSem Load (word-cell) evaluator case.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:48-51 (`mem_load_def`:
  `if addr IN s.memaddrs then SOME (s.memory addr) else NONE`) and :93-96
  (`eval s (Load addr) = ... mem_load w s`).  The memory cell holds the 64-bit
  word 0x1122334455667788 at address 8 and `memaddrs = {8w}`; a valid load
  returns the wrapped cell, an address outside `memaddrs` returns NONE.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(64,unit) crepSem$state)``;
val s0 = ``(^s with <|
    memory := (\(a : 64 word).
      if a = (8w:64 word) then Word (0x1122334455667788w:64 word)
      else Word (0w:64 word));
    memaddrs := {(8w:64 word)};
    be := F |>)``;
val s1 = ``(^s with <|
    memory := (\(a : 64 word).
      if a = (3w:64 word) then Word (3w:64 word)
      else Word (0w:64 word));
    memaddrs := {(3w:64 word)};
    be := F |>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "mem_load_valid"
  ``crepSem$mem_load (8w:64 word) ^s0``;

val _ = print_eval "mem_load_outside_domain"
  ``crepSem$mem_load (9w:64 word) ^s0``;

val _ = print_eval "eval_load_valid"
  ``crepSem$eval ^s0 (crepLang$Load (crepLang$Const (8w:64 word)))``;

val _ = print_eval "eval_load_outside_domain"
  ``crepSem$eval ^s0 (crepLang$Load (crepLang$Const (9w:64 word)))``;
(* The following observations use the same address and cell as
   compile_exp's `load_one` and panSem's `one_load_one` rows. *)
val _ = print_eval "mem_load_one_load_one"
  ``crepSem$mem_load (3w:64 word) ^s1``;
val _ = print_eval "eval_load_one_load_one"
  ``crepSem$eval ^s1 (crepLang$Load (crepLang$Const (3w:64 word)))``;
