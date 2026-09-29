(*
  Direct HOL observations for the StoreGlob case of
  crep_arithProofScript.sml:184-212 `simp_prog_correct`.

  HOL `simp_prog (StoreGlob g exp) = StoreGlob g (simp_exp exp)`
  (crep_arithScript.sml:89) and `evaluate (StoreGlob dst src, s)` evaluates only
  `src`, returning `(NONE, set_globals dst w s)` on success and
  `(SOME Error, s)` otherwise (crepSemScript.sml:288-291).  The local `mapc`
  overload is inlined as `fun f st. st with code := FMAP_MAP2 f st.code`.
  Rows `simp_prog_storeglob`, `evaluate_storeglob_const`,
  `evaluate_storeglob_mapc` and `storeglob_mapc_commute` exercise the
  successful source equation and the code-only `mapc` commutation with
  `set_globals`; `evaluate_storeglob_missing_var` pins the non-`Error`
  premise's failure branch.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val s = ``(s:(8,unit) crepSem$state)``;
val dst = ``(3w:5 word)``;
val sStore = ``(^s with <|
    locals := FEMPTY |+ (1, Word (5w:8 word));
    globals := FEMPTY |+ ((2w:5 word), Word (9w:8 word)) |>)``;
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

val _ = print_eval "simp_prog_storeglob"
  ``crep_arith$simp_prog (crepLang$StoreGlob ^dst (crepLang$Const (7w:8 word))) =
      crepLang$StoreGlob ^dst (crep_arith$simp_exp (crepLang$Const (7w:8 word)))``;
val _ = print_eval "evaluate_storeglob_const"
  ``crepSem$evaluate (crepLang$StoreGlob ^dst (crepLang$Const (7w:8 word)), ^sStore) =
      (NONE, crepSem$set_globals ^dst (Word (7w:8 word)) ^sStore)``;
val _ = print_eval "evaluate_storeglob_mapc"
  ``crepSem$evaluate (crepLang$StoreGlob ^dst (crepLang$Const (7w:8 word)), ^mapcF ^sStore) =
      (NONE, crepSem$set_globals ^dst (Word (7w:8 word)) (^mapcF ^sStore))``;
val _ = print_eval "storeglob_mapc_commute"
  ``crepSem$set_globals ^dst (Word (7w:8 word)) (^mapcF ^sStore) =
      ^mapcF (crepSem$set_globals ^dst (Word (7w:8 word)) ^sStore)``;
val _ = print_eval "evaluate_storeglob_missing_var"
  ``crepSem$evaluate (crepLang$StoreGlob ^dst (crepLang$Var 99), ^sStore) =
      (SOME crepSem$Error, ^sStore)``;
