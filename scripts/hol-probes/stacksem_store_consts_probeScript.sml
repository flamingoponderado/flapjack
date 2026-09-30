(*
  Direct HOL-EVAL observations for the stackSem$evaluate_def StoreConsts clause.
  Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:784-788.

  The program is `StoreConsts 4 5 stub`; the base state fixes registers 0..5,
  sets mdomain = UNIV, memory default Word 0w, and uses the two-word bitmap list
  [0x03;0x55].  On the success rows the exact store_const_sem 4 5 transition
  copies the 2-bit pattern 0x03, relocating 0x100w to bitmaps[1] + off = 0x65w
  and returning 0x100w + bytes_in_word = 0x108w, stores 1w into t1=4, t2=5 and
  register 1, and, when use_alloc = T, removes register 0 (unset_var 0).

  Observations cover the four guard outcomes and the two success arms:
  use_store = F -> Error; use_alloc = F with a SOME stub -> Error; the exact
  check_store_consts_opt stub guard failing (empty code) -> Error; and the
  store_const_sem success reached via a NONE stub with use_alloc = T/F and via a
  matching SOME stub inserted at label 7 with use_alloc = T.
*)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun print_eval label q =
  let
    val th0 = EVAL q
    (* store_const_sem updates regs with FUPDATE and removes register 0 with
       FDOMSUB (unset_var 0).  EVAL leaves FLOOKUP over those finite-map
       operations, so rewrite the observations with the lookup lemmas before
       the final evaluation. *)
    val th = QCONV
      (SIMP_CONV (srw_ss()) [DOMSUB_FLOOKUP, DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE]
         THENC EVAL)
      (rhs (concl th0))
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,num,num) stackSem$state``;
val base =
  ``^s with <|
      regs := (FEMPTY |+ (0, Word (0xAAw:64 word)) |+ (1, Word (0w:64 word))
                    |+ (2, Word (0x100w:64 word)) |+ (3, Word (0x10w:64 word))
                    |+ (4, Word (0xDEADw:64 word)) |+ (5, Word (0xBEEFw:64 word)));
      memory := (K (Word (0w:64 word)));
      mdomain := UNIV;
      bitmaps := [0x03w:64 word; 0x55w:64 word];
      code := (LN : 64 stackLang$prog sptree$num_map);
      use_store := T;
      use_alloc := T |>``;
val proj =
  ``\(r:64 stackSem$result option, t:(64,num,num) stackSem$state).
      (r, FLOOKUP t.regs 0, FLOOKUP t.regs 1, FLOOKUP t.regs 2,
       FLOOKUP t.regs 4, FLOOKUP t.regs 5,
       t.memory 0x100w, t.memory 0x108w, t.memory 0x200w,
       t.use_alloc, t.use_store)``;

val _ = print_eval "store_disabled"
  ``^proj (let s0 = ^base with use_store := F in
             stackSem$evaluate (StoreConsts 4 5 NONE, s0))``;
val _ = print_eval "stub_alloc_disabled"
  ``^proj (let s0 = ^base with use_alloc := F in
             stackSem$evaluate (StoreConsts 4 5 (SOME 7), s0))``;
val _ = print_eval "guard_failure"
  ``^proj (let s0 = ^base in
             stackSem$evaluate (StoreConsts 4 5 (SOME 7), s0))``;
val _ = print_eval "success_stub_none_use_alloc_true"
  ``^proj (let s0 = ^base in
             stackSem$evaluate (StoreConsts 4 5 NONE, s0))``;
val _ = print_eval "success_stub_none_use_alloc_false"
  ``^proj (let s0 = ^base with use_alloc := F in
             stackSem$evaluate (StoreConsts 4 5 NONE, s0))``;
val _ = print_eval "success_stub_match_use_alloc_true"
  ``^proj (let s0 = ^base with
             code := insert 7 (Seq (StoreConsts 4 5 NONE) (Return 0)
                               : 64 stackLang$prog) (LN : 64 stackLang$prog sptree$num_map) in
             stackSem$evaluate (StoreConsts 4 5 (SOME 7), s0))``;
