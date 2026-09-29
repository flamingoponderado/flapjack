(*
  Direct HOL observations for the StoreByte case of
  crep_arithProofScript.sml:184-212 `simp_prog_correct`.

  HOL `simp_prog (StoreByte dst src) = StoreByte (simp_exp dst) (simp_exp src)`
  (crep_arithScript.sml:88) and `evaluate (StoreByte dst src, s)` evaluates both
  operands into words and stores the low byte through the endian-aware
  `mem_store_byte`, returning `(NONE, s with memory := m)` on success and
  `(SOME Error, s)` when an operand fails or the mapped byte cell lies outside
  `s.memaddrs` (crepSemScript.sml:281-287).  The local `mapc` overload is
  inlined as `fun f st. st with code := FMAP_MAP2 f st.code`.

  Rows `simp_prog_storebyte`, `evaluate_storebyte_success_result` and
  `evaluate_storebyte_mapc_success_result` exercise the successful source
  equation and its preservation under the code-only `mapc`; the three
  `*_error_*` rows pin the non-`Error` premise's failure branches (operand
  failure and out-of-domain byte store), and `storebyte_memory_mapc` pins the
  code-only `mapc` leaving memory untouched.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val s = ``(s:(8,unit) crepSem$state)``;
val dst = ``crepLang$Const (3w:8 word)``;
val mem0 = ``\(a:8 word). Word (0w:8 word)``;
val sStore = ``(^s with <|
    locals := FEMPTY |+ (1, Word (5w:8 word));
    memaddrs := {};
    memory := ^mem0 |>)``;
val sMem = ``(^s with <| memaddrs := UNIV; memory := ^mem0 |>)``;
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

val _ = print_eval "simp_prog_storebyte"
  ``crep_arith$simp_prog (crepLang$StoreByte ^dst (crepLang$Const (7w:8 word))) =
      crepLang$StoreByte (crep_arith$simp_exp ^dst)
        (crep_arith$simp_exp (crepLang$Const (7w:8 word)))``;
val _ = print_eval "evaluate_storebyte_success_result"
  ``FST (crepSem$evaluate (crepLang$StoreByte ^dst (crepLang$Const (7w:8 word)), ^sMem)) =
      NONE``;
val _ = print_eval "evaluate_storebyte_mapc_success_result"
  ``FST (crepSem$evaluate (crepLang$StoreByte ^dst (crepLang$Const (7w:8 word)),
        ^mapcF ^sMem)) =
      NONE``;
val _ = print_eval "evaluate_storebyte_error_domain"
  ``crepSem$evaluate (crepLang$StoreByte ^dst (crepLang$Const (7w:8 word)), ^sStore) =
      (SOME crepSem$Error, ^sStore)``;
val _ = print_eval "evaluate_storebyte_mapc_error_domain"
  ``crepSem$evaluate (crepLang$StoreByte ^dst (crepLang$Const (7w:8 word)),
        ^mapcF ^sStore) =
      (SOME crepSem$Error, ^mapcF ^sStore)``;
val _ = print_eval "evaluate_storebyte_missing_var"
  ``crepSem$evaluate (crepLang$StoreByte ^dst (crepLang$Var 99), ^sStore) =
      (SOME crepSem$Error, ^sStore)``;
val _ = print_eval "storebyte_memory_mapc"
  ``(^mapcF ^sMem).memory = ^sMem.memory``;
