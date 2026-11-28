module

public import Flapjack.Basis.Pure.MlString.Length
public import Flapjack.CakeParser.PegEval
public import Flapjack.CakeParser.PegExecHelpers
public import Flapjack.CakeParser.PegSyntax
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# The first-order CakeML PEG machine

Counterparts of the state datatypes and the driver of
`cakeml/compiler/parsing/pegexec_cml_foScript.sml`: HOL's `pegresult` (from
`HOL/examples/formal-languages/context-free/pegScript.sml`), the continuation
`kont_fo`, the machine state `evalcase_fo`, the configuration record `peg_fo`,
and `sloc_pexec_def`, `corestep_fo_body_def`, `run_peg_fo_def`,
`peg_exec_fuel_fo_def`, `peg_exec_core_fuel_def` and
`mlstring_nonempty_strlen`.

HOL `string` is `char list`, so the error strings are `List HolChar` and `«»` is
`.implode []`; the token input is `(token # locs) list` and the value stack is
`(mlptree list) option list`, exactly as in the original instantiation.
-/

namespace Flapjack.CakeParser

open Flapjack.Basis.Pure.MlString
open Flapjack.Basis.Pure.MlString.MlString
open Flapjack.Misc.Location
open PegActions
open PegChecks
open PegSyntax
open PegEval
open PegGrammar

/-- Exact HOL `pegresult` (`HOL/examples/formal-languages/context-free/pegScript.sml:34-37`):
`Success 'a 'c ((locs # 'e) option) | Failure locs 'e`. -/
@[hol "HOL/examples/formal-languages/context-free/pegScript.sml" "pegresult"]
inductive PegResult (α β ε : Type) where
  | success : α → β → Option (Locs × ε) → PegResult α β ε
  | failure : Locs → ε → PegResult α β ε

/-- Original `kont_fo`: the defunctionalized continuation stack. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "kont_fo"]
inductive Kont where
  | ksym : PegExpr → Kont → Kont → Kont
  | app1Plain : Unary → Kont → Kont
  | app1Cl : Kont → Kont
  | app1Cr : Kont → Kont
  | app2 : Binary → Kont → Kont
  | dropErr : Kont → Kont
  | addErr : Locs → List HolChar → Kont → Kont
  | cmpErrs : Kont → Kont
  | cmpEO : Option (Locs × List HolChar) → Kont → Kont
  | returnTo : List (Token × Locs) → List (Option (List ParseTree)) → Kont → Kont
  | restoreEO : Option (Locs × List HolChar) → Kont → Kont
  | poplist : Kont → Kont
  | listsym : PegExpr → Kont → Kont
  | done
  | failed

/-- Original `evalcase_fo`: the machine state. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "evalcase_fo"]
inductive EvalCase where
  | ev : PegExpr → List (Token × Locs) → List (Option (List ParseTree))
      → Option (Locs × List HolChar) → List (Locs × List HolChar)
      → Kont → Kont → EvalCase
  | ap : Kont → List (Token × Locs) → List (Option (List ParseTree))
      → Option (Locs × List HolChar) → List (Locs × List HolChar) → EvalCase
  | result : PegResult (List (Token × Locs)) (List ParseTree) (List HolChar) → EvalCase
  | looped

/-- Original `peg_fo`: the machine configuration record. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "peg_fo"]
structure PegFo where
  start : PegExpr
  anyEOF : List HolChar
  tokFALSE : List HolChar
  tokEOF : List HolChar
  notFAIL : List HolChar

/-- Original `sloc_pexec_def`: the location of the next token, or `EOF_fo`. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "sloc_pexec_def"]
def slocPexec : List (Token × Locs) → Locs
  | [] => .locs .eofPt .eofPt
  | (_, l) :: _ => l

/-- Original `corestep_fo_body_def`: one step of the first-order machine. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "corestep_fo_body_def"]
def corestepBody (anyE tokF tokE notF : List HolChar) : EvalCase → EvalCase
  | .ev e i r eo errs k fk =>
    match e with
    | .empty v => .ap k i (some v :: r) eo errs
    | .any m =>
      match i with
      | [] =>
        let err := (.locs .eofPt .eofPt, anyE)
        .ap fk i r (mergeErrOption eo (some err)) (err :: errs)
      | h :: t => .ap k t (some (evalTokenMap m h) :: r) eo errs
    | .token p m =>
      match i with
      | [] =>
        let err := (.locs .eofPt .eofPt, tokE)
        .ap fk i r (mergeErrOption eo (some err)) (err :: errs)
      | h :: t =>
        if evalToken p h then
          .ap k t (some (evalTokenMap m h) :: r) eo errs
        else
          let err := (slocPexec i, tokF)
          .ap fk i r (mergeErrOption eo (some err)) (err :: errs)
    | .nt n u =>
      match ntRule n with
      | some sub => .ev sub i r eo errs (.app1Plain u k) fk
      | none => .looped
    | .seq e1 e2 b =>
      .ev e1 i r eo errs
        (.restoreEO eo (.ksym e2 (.app2 b k) (.cmpEO eo (.returnTo i r fk)))) fk
    | .choice e1 e2 =>
      .ev e1 i r eo errs (.app1Cl k)
        (.returnTo i r (.ksym e2 (.dropErr (.app1Cr k)) (.cmpErrs fk)))
    | .repeat e =>
      .ev e i (none :: r) eo errs (.restoreEO eo (.listsym e k)) (.poplist k)
    | .not e v =>
      .ev e i r eo errs
        (.restoreEO eo (.returnTo i r (.addErr (slocPexec i) notF fk)))
        (.restoreEO eo (.returnTo i (some v :: r) (.dropErr k)))
    | .error err =>
      let e := (slocPexec i, err)
      .ap fk i r (mergeErrOption eo (some e)) (e :: errs)
  | .ap k i r eo errs =>
    match k with
    | .done =>
      match r with
      | [] => .looped
      | none :: _ => .looped
      | some rv :: _ => .result (.success i rv eo)
    | .failed =>
      match errs with
      | [] =>
        match eo with
        | none => .looped
        | some (l, e) => .result (.failure l e)
      | (l, e) :: _ => .result (.failure l e)
    | .dropErr k =>
      match errs with
      | [] => .ap k i r eo []
      | _ :: t => .ap k i r eo t
    | .addErr l e k =>
      .ap k i r (mergeErrOption eo (some (l, e))) ((l, e) :: errs)
    | .cmpErrs k =>
      match errs with
      | [] => .ap k i r eo []
      | [e] => .ap k i r eo [e]
      | (l2, er2) :: _ :: rest => .ap k i r eo ((l2, er2) :: rest)
    | .cmpEO eo1 k =>
      match errs with
      | [] => .ap k i r (mergeErrOption eo1 eo) []
      | (l, err) :: rest =>
        .ap k i r (mergeErrOption eo1 (some (l, err))) ((l, err) :: rest)
    | .ksym e k fk => .ev e i r eo errs k fk
    | .app1Plain u k =>
      match r with
      | some v :: r' => .ap k i (some (evalUnary u v) :: r') eo errs
      | _ => .looped
    | .app1Cl k =>
      match r with
      | some v :: r' => .ap k i (some (evalCombine (.inl v)) :: r') eo errs
      | _ => .looped
    | .app1Cr k =>
      match r with
      | some v :: r' => .ap k i (some (evalCombine (.inr v)) :: r') eo errs
      | _ => .looped
    | .app2 b k =>
      match r with
      | some v1 :: some v2 :: r' =>
        .ap k i (some (evalBinary b v2 v1) :: r') eo errs
      | _ => .looped
    | .returnTo i' r' k => .ap k i' r' eo errs
    | .restoreEO eo' k => .ap k i r eo' errs
    | .listsym e k =>
      .ev e i r eo errs (.restoreEO eo (.listsym e k)) (.poplist k)
    | .poplist k =>
      match errs with
      | [] => .ap k i (poplistval r) eo []
      | _ :: errs' => .ap k i (poplistval r) eo errs'
  | .result res => .result res
  | .looped => .looped

/-- Original `run_peg_fo_def`: run the machine for at most `fuel` steps. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "run_peg_fo_def"]
def runPegFo : Nat → List HolChar → List HolChar → List HolChar → List HolChar
    → EvalCase → EvalCase
  | 0, _, _, _, _, _ => .looped
  | n + 1, anyE, tokF, tokE, notF, st =>
    match st with
    | .result res => .result res
    | .looped => .looped
    | st' => runPegFo n anyE tokF tokE notF (corestepBody anyE tokF tokE notF st')

/-- Original `peg_exec_fuel_fo_def`: start the machine on a grammar expression. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "peg_exec_fuel_fo_def"]
def pegExecFuelFo (fuel : Nat) (e : PegExpr) (i : List (Token × Locs))
    (r : List (Option (List ParseTree))) (eo : Option (Locs × List HolChar))
    (errs : List (Locs × List HolChar)) (k fk : Kont) : EvalCase :=
  runPegFo fuel ((ofString "Didn't expect an EOF").explode)
    ((ofString "Failed to see expected token").explode)
    ((ofString "Failed to see expected token; saw EOF instead").explode)
    ((ofString "Not combinator failed").explode)
    (.ev e i r eo errs k fk)

/-- Original `peg_exec_core_fuel_def`: start on the CakeML top-level nonterminal. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "peg_exec_core_fuel_def"]
def pegExecCoreFuel (fuel : Nat) (i : List (Token × Locs)) : EvalCase :=
  pegExecFuelFo fuel (.nt (.inl .nTopLevelDecs) .id) i [] none [] Kont.done Kont.failed

/-- Original `mlstring_nonempty_strlen`: emptiness agrees with zero length. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "mlstring_nonempty_strlen"]
theorem mlstringNonemptyStrlen (s : MlString) :
    (s ≠ .implode []) ↔ 0 < strlen s := by
  cases s with
  | implode d =>
    cases d with
    | nil => simp [strlen]
    | cons c t => simp [strlen]

end Flapjack.CakeParser
