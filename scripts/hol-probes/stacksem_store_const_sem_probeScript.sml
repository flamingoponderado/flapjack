(*
  Direct HOL-EVAL fixture for stackSem$store_const_sem_def.
  Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:729-741
  (plus unset_var_def at :725-727).

  State type (64,num,num): 64-bit words, a num compiler configuration and a num
  oracle state.  The base state fixes registers 0..5, sets mdomain = UNIV, and
  uses the two-word bitmap list [0x03; 0x55].  Register 1 holds the copy start
  index i = 0w, register 2 the destination a = 0x100w, register 3 the offset
  off = 0x10w.  copy_words 0 0x100 0x10 [0x03;0x55] UNIV m reduces the 2-bit
  pattern 0x03 by relocating a with bitmaps[1] + off = 0x55 + 0x10 = 0x65, then
  terminates at the sentinel 0x01 with the returned address a + bytes_in_word =
  0x108.

  Observations cover: the duplicate-register guard failure (SOME Error, state
  unchanged); a non-word operand in register 1 (SOME Error); copy_words NONE
  because the bitmap list is empty (SOME Error, state unchanged); and the two
  success arms use_alloc = T (register 0 removed) and use_alloc = F (register 0
  kept), each reporting the updated registers and memory.
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
      use_alloc := T |>``;
val proj =
  ``\(r:64 stackSem$result option, t:(64,num,num) stackSem$state).
      (r, FLOOKUP t.regs 0, FLOOKUP t.regs 1, FLOOKUP t.regs 2,
       FLOOKUP t.regs 4, FLOOKUP t.regs 5,
       t.memory 0x100w, t.memory 0x108w, t.memory 0x200w, t.use_alloc)``;

val _ = print_eval "guard_duplicate"
  ``^proj (let s0 = ^base in stackSem$store_const_sem 1 5 s0)``;
val _ = print_eval "non_word_operand"
  ``^proj (let s0 = ^base in
             let s1 = s0 with regs := s0.regs |+ (1, Loc 9 9) in
               stackSem$store_const_sem 4 5 s1)``;
val _ = print_eval "copy_words_none"
  ``^proj (let s0 = ^base with bitmaps := ([]:64 word list) in
             stackSem$store_const_sem 4 5 s0)``;
val _ = print_eval "success_use_alloc_true"
  ``^proj (let s0 = ^base in stackSem$store_const_sem 4 5 s0)``;
val _ = print_eval "success_use_alloc_false"
  ``^proj (let s0 = ^base with use_alloc := F in
             stackSem$store_const_sem 4 5 s0)``;
