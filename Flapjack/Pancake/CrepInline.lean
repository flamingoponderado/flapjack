import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.CrepLang.Prog

/-!
Executable support for the Crepe inlining pass.

This file ports the analysis and control-flow-normalization pieces of
CakeML's `crep_inline` theory.  The actual call substitution is intentionally
kept as a later layer; these helpers are useful independently when checking
that an inline candidate has no unreachable tail.
-/

namespace Flapjack

/-- Variable occurrence analysis.  Calls the generic `crepExpVars`; the tagged
    width-indexed `crepExpVarsW` is a definitional delegation of it, so this
    executed use is the identical computation (`flapjack-pxn.18.4.3.82`). -/
def crepVarProg : CrepProg α → List Nat
  | .dec name value body => [name] ++ crepExpVars value ++ crepVarProg body
  | .assign name value => [name] ++ crepExpVars value
  | .primitive names _ arguments => names ++ arguments
  | .store address value | .store32 address value | .storeByte address value =>
      crepExpVars address ++ crepExpVars value
  | .storeGlob _ value => crepExpVars value
  | .seq first second => crepVarProg first ++ crepVarProg second
  | .ite condition thenBranch elseBranch =>
      crepExpVars condition ++ crepVarProg thenBranch ++ crepVarProg elseBranch
  | .while condition body => crepExpVars condition ++ crepVarProg body
  | .call none _ arguments => arguments.flatMap crepExpVars
  | .call (some (names, none)) _ arguments =>
      arguments.flatMap crepExpVars ++ names
  | .call (some (names, some (_, handler))) _ arguments =>
      arguments.flatMap crepExpVars ++ names ++ crepVarProg handler
  | .extCall _ configuration configurationLength array arrayLength =>
      [configuration, configurationLength, array, arrayLength]
  | .return values => values.flatMap crepExpVars
  | .shMem _ name address => name :: crepExpVars address
  | .skip | .break _ | .continue _ | .raise _ | .tick => []
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

def crepVmaxProg (program : CrepProg α) : Nat :=
  (crepVarProg program).foldl max 0

def crepHasReturn : CrepProg α → Bool
  | .dec _ _ body => crepHasReturn body
  | .seq first second => crepHasReturn first || crepHasReturn second
  | .ite _ thenBranch elseBranch =>
      crepHasReturn thenBranch || crepHasReturn elseBranch
  | .while _ body => crepHasReturn body
  | .call none _ _ => true
  | .call (some (_, none)) _ _ => false
  | .call (some (_, some (_, handler))) _ _ => crepHasReturn handler
  | .return _ => true
  | _ => false
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def crepNotBranchRet : CrepProg α → Bool
  | .dec _ _ body => crepNotBranchRet body
  /- CakeML recurses `not_branch_ret` into both `Seq` children
     (`crep_inlineScript.sml:70`); the non-recursive `has_return` test is
     only used for `If`/`While`. -/
  | .seq first second => crepNotBranchRet first && crepNotBranchRet second
  | .ite _ thenBranch elseBranch =>
      !crepHasReturn thenBranch && !crepHasReturn elseBranch
  | .while _ body => !crepHasReturn body
  | .call none _ _ | .call (some (_, none)) _ _ => true
  | .call (some (_, some (_, handler))) _ _ => !crepHasReturn handler
  | _ => true
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! Kernel-checked port of CakeML's
    `not_has_return_imp_not_branch_ret` (`crep_inlineProofScript.sml:1758`):
    a program with no return cannot acquire a return through a branching
    construct.  The handler case is included because handlers are recursive
    Crep programs rather than opaque metadata. -/
private theorem crepHasReturn_false_imp_notBranchRet_aux :
    (program : CrepProg α) →
      crepHasReturn program = false → crepNotBranchRet program = true := by
  intro program
  fun_induction crepHasReturn program with
  | _ => grind only [crepNotBranchRet, crepHasReturn]

inductive CrepEarlyExit where
  | exception
  | return
  | loopExit
  deriving DecidableEq, Repr

/-- Exact port of `early_exit` from
    `cakeml/pancake/crep_inlineScript.sml`: its three constructors are
    `Exn`, `Ret`, and `Loop_exit`, in HOL order. -/
@[hol "cakeml/pancake/crep_inlineScript.sml" "early_exit"]
inductive CrepEarlyExitHOL where
  | exception
  | return
  | loopExit
  deriving DecidableEq, Repr

def crepMergeExit : Option CrepEarlyExit → Option CrepEarlyExit → Option CrepEarlyExit
  | some .return, second => second
  | first, some .return => first
  | some .exception, second => second
  | first, some .exception => first
  | some .loopExit, second => second
  | first, some .loopExit => first
  | none, none => none

/-- Helper for the HOL-carrier unreachability pass. The clause priority is the
    same as HOL's nested case expression in `unreach_elim_def`: Ret cases are
    tested first, then Exn, then Loop_exit. -/
def crepMergeExitHOL : Option CrepEarlyExitHOL → Option CrepEarlyExitHOL →
    Option CrepEarlyExitHOL
  | some .return, second => second
  | first, some .return => first
  | some .exception, second => second
  | first, some .exception => first
  | some .loopExit, second => second
  | first, some .loopExit => first
  | none, none => none

/-- Exact port of Cake `unreach_elim_def`
    (`cakeml/pancake/crep_inlineScript.sml:90-135`) over the exact
    width-indexed `CrepProgHOL` carrier. Source review compared every clause:
    Return/Raise/Break/Continue report their exit; Seq skips its second
    component when the first reports an exit; Dec propagates the body's exit;
    If transforms both branches and merges exits with HOL's return, exception,
    then loop-exit priority; While always reports `NONE`; Call with no return
    info reports Ret, a handler-free returning Call reports no exit, and a
    Call with a handler transforms the handler but discards its exit; all
    other constructors are unchanged with no exit. -/
@[hol "cakeml/pancake/crep_inlineScript.sml" "unreach_elim_def"
  (words_as_type_indexed_bitvec)]
def unreachElimHOLExact {width : Nat} [NeZero width] :
    CrepProgHOL width → CrepProgHOL width × Option CrepEarlyExitHOL
  | .return values => (.return values, some .return)
  | .raise exception => (.raise exception, some .exception)
  | .break label => (.break label, some .loopExit)
  | .continue label => (.continue label, some .loopExit)
  | .seq first second =>
      let (first', firstExit) := unreachElimHOLExact first
      if firstExit.isSome then
        (first', firstExit)
      else
        let (second', secondExit) := unreachElimHOLExact second
        (.seq first' second', secondExit)
  | .dec name value body =>
      let (body', bodyExit) := unreachElimHOLExact body
      (.dec name value body', bodyExit)
  | .ite condition thenBranch elseBranch =>
      let (then', thenExit) := unreachElimHOLExact thenBranch
      let (else', elseExit) := unreachElimHOLExact elseBranch
      (.ite condition then' else', crepMergeExitHOL thenExit elseExit)
  | .while condition body =>
      let (body', _) := unreachElimHOLExact body
      (.while condition body', none)
  | .call none name arguments =>
      (.call none name arguments, some .return)
  | .call (some (names, none)) name arguments =>
      (.call (some (names, none)) name arguments, none)
  | .call (some (names, some (handler, body))) name arguments =>
      let (body', _) := unreachElimHOLExact body
      (.call (some (names, some (handler, body'))) name arguments, none)
  | program => (program, none)

/-- Exact width-indexed port of Cake `var_prog_def`
    (`cakeml/pancake/crep_inlineScript.sml:8-33`). The source clauses are
    preserved in order: declaration/assignment destinations precede expression
    occurrences; call argument occurrences precede return destinations and
    handler occurrences; `StoreGlob` contributes only expression variables;
    ExtCall lists all four variable operands; ShMem lists its name then address;
    Primitive lists destinations then operands. Exception labels and function
    names are not variable occurrences. -/
@[hol "cakeml/pancake/crep_inlineScript.sml" "var_prog_def"
  (words_as_type_indexed_bitvec)]
def crepVarProgHOLExact {width : Nat} [NeZero width] :
    CrepProgHOL width → List Nat
  | .dec name value body =>
      [name] ++ crepExpVarsHOL value ++ crepVarProgHOLExact body
  | .assign name value => [name] ++ crepExpVarsHOL value
  | .primitive names _ arguments => names ++ arguments
  | .store address value | .store32 address value | .storeByte address value =>
      crepExpVarsHOL address ++ crepExpVarsHOL value
  | .storeGlob _ value => crepExpVarsHOL value
  | .seq first second => crepVarProgHOLExact first ++ crepVarProgHOLExact second
  | .ite condition thenBranch elseBranch =>
      crepExpVarsHOL condition ++ crepVarProgHOLExact thenBranch ++
        crepVarProgHOLExact elseBranch
  | .while condition body => crepExpVarsHOL condition ++ crepVarProgHOLExact body
  | .call none _ arguments => arguments.flatMap crepExpVarsHOL
  | .call (some (names, none)) _ arguments =>
      arguments.flatMap crepExpVarsHOL ++ names
  | .call (some (names, some (_, handler))) _ arguments =>
      arguments.flatMap crepExpVarsHOL ++ names ++ crepVarProgHOLExact handler
  | .extCall _ configuration configurationLength array arrayLength =>
      [configuration, configurationLength, array, arrayLength]
  | .return values => values.flatMap crepExpVarsHOL
  | .shMem _ name address => name :: crepExpVarsHOL address
  | .skip | .break _ | .continue _ | .raise _ | .tick => []
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | simp_wf

/-- Exact port of Cake `vmax_prog_def` (`crep_inlineScript.sml:36-38`),
    using the source `MAX_LIST` empty-list convention of zero. -/
@[hol "cakeml/pancake/crep_inlineScript.sml" "vmax_prog_def"
  (words_as_type_indexed_bitvec)]
def crepVmaxProgHOLExact {width : Nat} [NeZero width]
    (program : CrepProgHOL width) : Nat :=
  (crepVarProgHOLExact program).foldl max 0

/-- Argument loading for inlining.  Calls the generic `nestedDecs`; the tagged
    width-indexed `nestedDecsW` is a definitional delegation of it, so this
    executed use is the identical computation (`flapjack-pxn.18.4.3.82`). -/
def crepArgLoad (temporaryNames : List Nat) (arguments : List (CrepExp α))
    (argumentNames : List Nat) (program : CrepProg α) : CrepProg α :=
  nestedDecs temporaryNames arguments
    (nestedDecs argumentNames (temporaryNames.map .var) program)

def crepInlineTail (program : CrepProg α) : CrepProg α :=
  .seq .tick program

def crepTransformEoc (returnNames : List Nat) : CrepProg α → CrepProg α
  | .return values =>
      crepNestedSeq (returnNames.zipWith (fun name value => .assign name value) values)
  | .call none name arguments =>
      .call (some (returnNames, none)) name arguments
  | .call (some (names, none)) name arguments =>
      .call (some (names, none)) name arguments
  | .call (some (names, some (handler, body))) name arguments =>
      .call (some (names, some (handler, crepTransformEoc returnNames body)))
        name arguments
  | .dec name value body => .dec name value (crepTransformEoc returnNames body)
  | .while condition body => .while condition (crepTransformEoc returnNames body)
  | .seq first second =>
      .seq (crepTransformEoc returnNames first) (crepTransformEoc returnNames second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepTransformEoc returnNames thenBranch)
        (crepTransformEoc returnNames elseBranch)
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def crepTransformBranch (loopDepth : Nat) (returnNames : List Nat) :
    CrepProg α → CrepProg α
  | .return values =>
      .seq
        (crepNestedSeq
          (returnNames.zipWith (fun name value => .assign name value) values))
        (.break loopDepth)
  | .call none name arguments =>
      .seq (.call (some (returnNames, none)) name arguments) (.break loopDepth)
  | .call (some (names, none)) name arguments =>
      .call (some (names, none)) name arguments
  | .call (some (names, some (handler, body))) name arguments =>
      .call (some (names, some (handler,
        crepTransformBranch loopDepth returnNames body))) name arguments
  | .dec name value body =>
      .dec name value (crepTransformBranch loopDepth returnNames body)
  | .while condition body =>
      .while condition (crepTransformBranch (loopDepth + 1) returnNames body)
  | .seq first second =>
      .seq (crepTransformBranch loopDepth returnNames first)
        (crepTransformBranch loopDepth returnNames second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepTransformBranch loopDepth returnNames thenBranch)
        (crepTransformBranch loopDepth returnNames elseBranch)
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def crepInlineNontail [OfNat α 0] (program : CrepProg α) (returnNames temporaryReturns
    temporaryNames : List Nat) (arguments : List (CrepExp α))
    (argumentNames : List Nat) : CrepProg α :=
  nestedDecs temporaryReturns (temporaryReturns.map (fun _ => .const 0))
    (.seq
      (crepArgLoad temporaryNames
        arguments argumentNames program)
      (crepNestedSeq
        (returnNames.zipWith (fun name temporary => .assign name (.var temporary))
          temporaryReturns)))

def crepUnreachElim : CrepProg α → CrepProg α × Option CrepEarlyExit
  | .return values => (.return values, some .return)
  | .raise exception => (.raise exception, some .exception)
  | .break label => (.break label, some .loopExit)
  | .continue label => (.continue label, some .loopExit)
  | .seq first second =>
      let (first', firstExit) := crepUnreachElim first
      if firstExit.isSome then
        (first', firstExit)
      else
        let (second', secondExit) := crepUnreachElim second
        (.seq first' second', secondExit)
  | .dec name value body =>
      let (body', bodyExit) := crepUnreachElim body
      (.dec name value body', bodyExit)
  | .ite condition thenBranch elseBranch =>
      let (then', thenExit) := crepUnreachElim thenBranch
      let (else', elseExit) := crepUnreachElim elseBranch
      (.ite condition then' else', crepMergeExit thenExit elseExit)
  | .while condition body =>
      let (body', _) := crepUnreachElim body
      (.while condition body', none)
  | .call none name arguments =>
      (.call none name arguments, some .return)
  | .call (some (names, none)) name arguments =>
      (.call (some (names, none)) name arguments, none)
  | .call (some (names, some (handler, body))) name arguments =>
      let (body', _) := crepUnreachElim body
      (.call (some (names, some (handler, body'))) name arguments, none)
  | program => (program, none)
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | simp_wf

/-! Kernel-checked port of CakeML's
    `not_has_return_imp_unreach_elim` (`crep_inlineProofScript.sml:1765`):
    `unreach_elim` cannot report a return for a program whose executable
    return analysis is false.  The private statement is slightly stronger
    than Cake's self-equality formulation and makes the recursive argument
    explicit; the public theorem below recovers the original statement. -/
private theorem crepHasReturn_false_imp_unreachElim_notReturn_aux :
    (program : CrepProg α) →
      crepHasReturn program = false →
      (crepUnreachElim program).2 ≠ some .return := by
  intro program
  fun_induction crepHasReturn program with
  | case3 condition left right ihLeft ihRight =>
      intro h
      have hLeft := ihLeft (Bool.or_eq_false_iff.mp h).1
      have hRight := ihRight (Bool.or_eq_false_iff.mp h).2
      rcases hl : (crepUnreachElim left).2 with _ | ⟨_ | _ | _⟩ <;>
        rcases hr : (crepUnreachElim right).2 with _ | ⟨_ | _ | _⟩ <;>
        simp_all [crepUnreachElim, crepMergeExit]
  | case9 program => cases program <;> simp_all [crepUnreachElim]
  | _ => grind only [crepUnreachElim, crepMergeExit, crepHasReturn]

end Flapjack
