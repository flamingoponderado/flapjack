(*
  Direct HOL observations for the If case of
  crep_arithProofScript.sml:184-212 `simp_prog_correct`.

  HOL `simp_prog (If exp c1 c2) = If (simp_exp exp) (simp_prog c1)
  (simp_prog c2)` (crep_arithScript.sml:90) and
  `evaluate (If e c1 c2, s)` evaluates `e`; on `SOME (Word w)` it evaluates
  the branch `if w <> 0w then c1 else c2` at the same state, and otherwise
  returns `(SOME Error, s)` (crepSemScript.sml:307-311).  The local `mapc`
  overload is inlined as `fun st. st with code := FMAP_MAP2 f st.code`.  Rows
  `simp_prog_if`, `evaluate_if_true`, `evaluate_if_true_state`,
  `evaluate_if_false`, `evaluate_if_false_state` exercise both guard values and
  the selected branch state; `evaluate_if_error` pins the non-word/absent
  condition failure branch; and `if_mapc_commute` pins the code-only `mapc`
  commutation with the selected branch update.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val s =
  ``(<| locals := (FEMPTY |+ (1, Word (5w:8 word)) |+ (2, Word (6w:8 word)));
        globals := FEMPTY;
        code := FEMPTY;
        memory := K (Word (0w:8 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w:8 word);
        top_addr := (100w:8 word) |> : (8, unit) crepSem$state)``;
val cTrue = ``(crepLang$Const (1w:8 word))``;
val cFalse = ``(crepLang$Const (0w:8 word))``;
val thenP = ``(crepLang$Assign 1 (crepLang$Const (5w:8 word)))``;
val elseP = ``(crepLang$Assign 2 (crepLang$Const (7w:8 word)))``;
val ifTrue = ``((crepLang$If ^cTrue ^thenP ^elseP) : 8 crepLang$prog)``;
val ifFalse = ``((crepLang$If ^cFalse ^thenP ^elseP) : 8 crepLang$prog)``;
val ifError = ``((crepLang$If (crepLang$Var 99) ^thenP ^elseP) : 8 crepLang$prog)``;
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

val _ = print_eval "simp_prog_if"
  ``crep_arith$simp_prog
      (crepLang$If ^cTrue ^thenP ^elseP) =
      crepLang$If (crep_arith$simp_exp ^cTrue)
        (crep_arith$simp_prog ^thenP) (crep_arith$simp_prog ^elseP)``;
val _ = print_eval "evaluate_if_true"
  ``FST (crepSem$evaluate (^ifTrue, ^s)) = NONE``;
val _ = print_eval "evaluate_if_true_state"
  ``SND (crepSem$evaluate (^ifTrue, ^s)) =
      (^s with locals := ^s.locals |+ (1, Word (5w:8 word)))``;
val _ = print_eval "evaluate_if_false"
  ``FST (crepSem$evaluate (^ifFalse, ^s)) = NONE``;
val _ = print_eval "evaluate_if_false_state"
  ``SND (crepSem$evaluate (^ifFalse, ^s)) =
      (^s with locals := ^s.locals |+ (2, Word (7w:8 word)))``;
val _ = print_eval "evaluate_if_error"
  ``crepSem$evaluate (^ifError, ^s) = (SOME crepSem$Error, ^s)``;
val _ = print_eval "if_mapc_true"
  ``FST (crepSem$evaluate (^ifTrue, ^mapcF ^s)) = NONE``;
val _ = print_eval "if_mapc_commute"
  ``SND (crepSem$evaluate (^ifTrue, ^mapcF ^s)) =
      ^mapcF (SND (crepSem$evaluate (^ifTrue, ^s)))``;
