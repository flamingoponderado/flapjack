import Flapjack.Compiler.Backend.FlatLang
import Flapjack.Misc.Sptree

/-! Analyses used by CakeML flatLang dead-code elimination. These preserve the
original conservative treatment of handlers, calls, and pattern matches. -/

namespace Flapjack.Compiler.Backend.FlatElim
open FlatLang

mutual
/-- Whether evaluating the expression directly avoids a global lookup. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "is_hidden_def"]
def isHidden : Exp → Bool
  | .raise _ e => isHidden e
  | .lit _ _ => true
  | .con _ _ es => allHidden es
  | .varLocal _ _ => true
  | .fn _ _ _ => true
  | .app _ (.globalVarInit _) [e] => isHidden e
  | .if_ _ a b c => isHidden a && isHidden b && isHidden c
  | .mat _ e [(_, rhs)] => isHidden e && isHidden rhs
  | .let_ _ _ a b => isHidden a && isHidden b
  | .letrec _ _ e => isHidden e
  | _ => false

/-- List traversal used for constructor arguments in `isHidden`. -/
def allHidden : List Exp → Bool
  | [] => true
  | e :: es => isHidden e && allHidden es
end

mutual
/-- Patterns guaranteed to match any value in the source analysis. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "total_pat_def"]
def totalPat : Pat → Bool
  | .pany | .pvar _ => true
  | .pcon none ps => totalPatList ps
  | .pas p _ => totalPat p
  | _ => false

/-- The list clauses of HOL `total_pat_def`. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "total_pat_def"]
def totalPatList : List Pat → Bool
  | [] => true
  | p :: ps => totalPat p && totalPatList ps
end

/-- HOL `EXISTS total_pat (MAP FST pes)`. -/
def hasTotalPat : List (Pat × Exp) → Bool
  | [] => false
  | (p, _) :: ps => totalPat p || hasTotalPat ps

mutual
/-- Whether an expression is free of visible effects other than global writes. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "is_pure_def"]
def isPure : Exp → Bool
  | .handle _ e _ => isPure e
  | .lit _ _ => true
  | .con _ _ es => allPure es
  | .varLocal _ _ => true
  | .fn _ _ _ => true
  | .app _ (.globalVarInit _) es => allPure es
  | .if_ _ a b c => isPure a && isPure b && isPure c
  | .mat _ e ps => isPure e && allPureBranches ps && hasTotalPat ps
  | .let_ _ _ a b => isPure a && isPure b
  | .letrec _ _ e => isPure e
  | _ => false

def allPure : List Exp → Bool
  | [] => true
  | e :: es => isPure e && allPure es

def allPureBranches : List (Pat × Exp) → Bool
  | [] => true
  | (_, e) :: es => isPure e && allPureBranches es
end

mutual
/-- Detect dynamic evaluation anywhere in a flat expression. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "has_Eval_def"]
def hasEval : Exp → Bool
  | .app _ op es => op == .src .eval || hasEvalList es
  | .mat _ e ps | .handle _ e ps => hasEval e || hasEvalPats ps
  | .letrec _ fs e => hasEval e || hasEvalFuns fs
  | .raise _ e | .fn _ _ e => hasEval e
  | .con _ _ es => hasEvalList es
  | .if_ _ a b c => hasEval a || hasEval b || hasEval c
  | .let_ _ _ a b => hasEval a || hasEval b
  | _ => false

/-- List clauses of the dynamic-evaluation analysis. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "has_Eval_def"]
def hasEvalList : List Exp → Bool
  | [] => false
  | e :: es => hasEval e || hasEvalList es

/-- Pattern-branch clauses of the dynamic-evaluation analysis. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "has_Eval_def"]
def hasEvalPats : List (Pat × Exp) → Bool
  | [] => false
  | (_, e) :: ps => hasEval e || hasEvalPats ps

/-- Recursive-function clauses of the dynamic-evaluation analysis. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "has_Eval_def"]
def hasEvalFuns : List (AstHOL.VarN × AstHOL.VarN × Exp) → Bool
  | [] => false
  | (_, _, e) :: fs => hasEval e || hasEvalFuns fs
end

/-- Extract a global initialization index. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "dest_GlobalVarInit_def"]
def destGlobalVarInit : Op → Option Nat
  | .globalVarInit n => some n
  | _ => none

/-- Extract a global lookup index. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "dest_GlobalVarLookup_def"]
def destGlobalVarLookup : Op → Option Nat
  | .globalVarLookup n => some n
  | _ => none

mutual
/-- Shared structural traversal for writes and reads. The selector is one of
`destGlobalVarInit` and `destGlobalVarLookup`; this helper has no HOL original. -/
def findGlobals (select : Op → Option Nat) : Exp → NumSet
  | .raise _ e | .fn _ _ e => findGlobals select e
  | .handle _ e ps | .mat _ e ps => sptUnion (findGlobals select e) (findGlobalsPats select ps)
  | .lit _ _ | .varLocal _ _ => .ln
  | .con _ _ es => findGlobalsList select es
  | .app _ op es =>
      let rest := findGlobalsList select es
      match select op with
      | some n => sptInsert n () rest
      | none => rest
  | .if_ _ a b c => sptUnion (findGlobals select a)
      (sptUnion (findGlobals select b) (findGlobals select c))
  | .let_ _ _ a b => sptUnion (findGlobals select a) (findGlobals select b)
  | .letrec _ fs e => sptUnion (findGlobalsFuns select fs) (findGlobals select e)

def findGlobalsList (select : Op → Option Nat) : List Exp → NumSet
  | [] => .ln
  | e :: es => sptUnion (findGlobals select e) (findGlobalsList select es)

def findGlobalsPats (select : Op → Option Nat) : List (Pat × Exp) → NumSet
  | [] => .ln
  | (_, e) :: ps => sptUnion (findGlobals select e) (findGlobalsPats select ps)

def findGlobalsFuns (select : Op → Option Nat) : List (AstHOL.VarN × AstHOL.VarN × Exp) → NumSet
  | [] => .ln
  | (_, _, e) :: fs => sptUnion (findGlobals select e) (findGlobalsFuns select fs)
end

/-- Global locations initialized in an expression, including nested functions. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "find_loc_def"]
def findLoc (e : Exp) : NumSet := findGlobals destGlobalVarInit e

/-- Global locations looked up in an expression, including nested functions. -/
@[hol "cakeml/compiler/backend/flat_elimScript.sml" "find_lookups_def"]
def findLookups (e : Exp) : NumSet := findGlobals destGlobalVarLookup e

end Flapjack.Compiler.Backend.FlatElim
