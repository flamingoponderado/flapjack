(*
  Direct HOL observations for the Store32 case of
  crep_arithProofScript.sml:184-212 `simp_prog_correct`.

  HOL `simp_prog (Store32 exp1 exp2) = Store32 (simp_exp exp1) (simp_exp exp2)`
  (crep_arithScript.sml:87) and `evaluate (Store32 dst src, s)` evaluates both
  operands, requiring `SOME (Word adr)`/`SOME (Word w)`, and stores the low
  `w2w w : word32` through `mem_store_32 s.memory s.memaddrs s.be adr`,
  returning `(NONE, s with memory := m)` on success and `(SOME Error, s)`
  otherwise (crepSemScript.sml:274-280).  The local `mapc` overload is inlined
  as `fun f st. st with code := FMAP_MAP2 f st.code`.  Rows
  `simp_prog_store32`, `evaluate_store32_const`, `evaluate_store32_mapc` and
  `store32_mapc_commute` exercise the successful source equation and the
  code-only `mapc` commutation with the `memory` update; the
  `evaluate_store32_domain_error`, `evaluate_store32_unaligned_error` and
  `evaluate_store32_missing_var` rows pin the non-`Error` premise's failure
  branches (memory-domain, alignment, failed operand).
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val s = ``(s:(8,unit) crepSem$state)``;
val adr = ``(4w:8 word)``;
val val8 = ``(0x11w:8 word)``;
val sStore = ``(^s with <|
    locals := FEMPTY |+ (1, Word (5w:8 word));
    memory := (\(a:8 word).
      if a = (4w:8 word) then Word (0xAAw:8 word) else Word (0w:8 word));
    memaddrs := {(4w:8 word)};
    be := F |>)``;
val sDomain = ``(^s with <|
    locals := FEMPTY |+ (1, Word (5w:8 word));
    memory := (\(a:8 word). Word (0xAAw:8 word));
    memaddrs := ({}:8 word set);
    be := F |>)``;
val mapcF = ``\(st : (8,unit) crepSem$state).
    st with code := FMAP_MAP2 f st.code``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "simp_prog_store32"
  ``crep_arith$simp_prog
      (crepLang$Store32 (crepLang$Const ^adr) (crepLang$Const ^val8)) =
      crepLang$Store32 (crep_arith$simp_exp (crepLang$Const ^adr))
        (crep_arith$simp_exp (crepLang$Const ^val8))``;
val _ = print_eval "evaluate_store32_const"
  ``FST (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const ^adr) (crepLang$Const ^val8), ^sStore)) =
      NONE``;
val _ = print_eval "evaluate_store32_mapc"
  ``FST (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const ^adr) (crepLang$Const ^val8), ^mapcF ^sStore)) =
      NONE``;
val _ = print_eval "store32_mapc_commute"
  ``SND (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const ^adr) (crepLang$Const ^val8), ^mapcF ^sStore)) =
      ^mapcF (SND (crepSem$evaluate
        (crepLang$Store32 (crepLang$Const ^adr) (crepLang$Const ^val8), ^sStore)))``;
val _ = print_eval "evaluate_store32_domain_error"
  ``FST (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const ^adr) (crepLang$Const ^val8), ^sDomain)) =
      SOME crepSem$Error``;
val _ = print_eval "evaluate_store32_unaligned_error"
  ``FST (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const (5w:8 word)) (crepLang$Const ^val8), ^sStore)) =
      SOME crepSem$Error``;
val _ = print_eval "evaluate_store32_missing_var"
  ``FST (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const ^adr) (crepLang$Var 99), ^sStore)) =
      SOME crepSem$Error``;
