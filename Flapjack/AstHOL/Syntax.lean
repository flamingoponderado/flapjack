import Flapjack.AstHOL.LitOp
import Flapjack.NamespaceHOL
import Flapjack.Misc.Location

/-!
# `astScript`: type annotations, patterns, expressions and declarations

Counterparts of `cakeml/semantics/astScript.sml` lines 158-262: `ast_t`, `pat`,
`exp`, the `type_def` abbreviation, `dec` and `pat_bindings_def` (with its mutual
`pats_bindings`). HOL `(modN, n) id` is the reviewed `NamespaceHOL.Ident`, `locs`
is `Misc.Location.Locs`, `option` is `Option`, `#` is `×` and `list` is `List`.
Constructor order and payloads match the source; constructor names are lower
camel case.
-/

namespace Flapjack.AstHOL

open Flapjack.NamespaceHOL Flapjack.Misc.Location

/-- Complete original `ast_t` (astScript 158-169). -/
@[hol "cakeml/semantics/astScript.sml" "ast_t"]
inductive AstT where
  | atvar : TvarN → AstT
  | atfun : AstT → AstT → AstT
  | attup : List AstT → AstT
  | atapp : List AstT → Ident ModN TypeN → AstT
  deriving Repr

/-- Complete original `pat` (astScript 172-184). -/
@[hol "cakeml/semantics/astScript.sml" "pat"]
inductive Pat where
  | pany
  | pvar : VarN → Pat
  | plit : Lit → Pat
  | pcon : Option (Ident ModN ConN) → List Pat → Pat
  | pref : Pat → Pat
  | pas : Pat → VarN → Pat
  | ptannot : Pat → AstT → Pat
  deriving Repr

/-- Complete original `exp` (astScript 192-222). -/
@[hol "cakeml/semantics/astScript.sml" "exp"]
inductive Exp where
  | raise : Exp → Exp
  | handle : Exp → List (Pat × Exp) → Exp
  | lit : Lit → Exp
  | con : Option (Ident ModN ConN) → List Exp → Exp
  | var : Ident ModN VarN → Exp
  | fn : VarN → Exp → Exp
  | app : Op → List Exp → Exp
  | log : Lop → Exp → Exp → Exp
  | if_ : Exp → Exp → Exp → Exp
  | mat : Exp → List (Pat × Exp) → Exp
  | let_ : Option VarN → Exp → Exp → Exp
  | letrec : List (VarN × VarN × Exp) → Exp → Exp
  | tannot : Exp → AstT → Exp
  | lannot : Exp → Locs → Exp
  deriving Repr

/-- Original `Type type_def = “:(tvarN list # typeN # (conN # ast_t list) list) list”`
(astScript 224). -/
@[hol "cakeml/semantics/astScript.sml" "type_def"]
abbrev TypeDef := List (List TvarN × TypeN × List (ConN × List AstT))

/-- Complete original `dec` (astScript 227-249). -/
@[hol "cakeml/semantics/astScript.sml" "dec"]
inductive Dec where
  | dlet : Locs → Pat → Exp → Dec
  | dletrec : Locs → List (VarN × VarN × Exp) → Dec
  | dtype : Locs → TypeDef → Dec
  | dtabbrev : Locs → List TvarN → TypeN → AstT → Dec
  | dexn : Locs → ConN → List AstT → Dec
  | dmod : ModN → List Dec → Dec
  | dlocal : List Dec → List Dec → Dec
  | denv : TvarN → Dec
  deriving Repr

mutual
/-- Exact HOL `pat_bindings_def` (astScript 252-262), first conjunct group. -/
@[hol "cakeml/semantics/astScript.sml" "pat_bindings_def"]
def patBindings : Pat → List VarN
  | .pany => []
  | .pvar n => [n]
  | .plit _ => []
  | .pcon _ ps => patsBindings ps
  | .pref p => patBindings p
  | .pas p i => patBindings p ++ [i]
  | .ptannot p _ => patBindings p

/-- The mutual `pats_bindings` clauses of HOL `pat_bindings_def`. -/
@[hol "cakeml/semantics/astScript.sml" "pat_bindings_def"]
def patsBindings : List Pat → List VarN
  | [] => []
  | p :: ps => patsBindings ps ++ patBindings p
end

mutual
/-- Recursively test a predicate at each source expression. The helper
traversals implement HOL's `EVERY` over expression-bearing lists. -/
@[hol "cakeml/semantics/astScript.sml" "every_exp_def"]
def everyExp (predicate : Exp → Bool) (expr : Exp) : Bool :=
  predicate expr && match expr with
  | .raise e | .fn _ e | .tannot e _ | .lannot e _ => everyExp predicate e
  | .handle e clauses | .mat e clauses => everyExp predicate e && everyExpClauses predicate clauses
  | .con _ exprs | .app _ exprs => everyExpList predicate exprs
  | .log _ first second | .let_ _ first second => everyExp predicate first && everyExp predicate second
  | .if_ condition yes no => everyExp predicate condition && everyExp predicate yes && everyExp predicate no
  | .letrec funs body => everyExp predicate body && everyExpFuns predicate funs
  | .lit _ | .var _ => true
termination_by sizeOf expr

private def everyExpList (predicate : Exp → Bool) (exprs : List Exp) : Bool :=
  match exprs with
  | [] => true
  | e :: rest => everyExp predicate e && everyExpList predicate rest
termination_by sizeOf exprs

private def everyExpClauses (predicate : Exp → Bool) (clauses : List (Pat × Exp)) : Bool :=
  match clauses with
  | [] => true
  | (_, e) :: rest => everyExp predicate e && everyExpClauses predicate rest
termination_by sizeOf clauses

private def everyExpFuns (predicate : Exp → Bool) (funs : List (VarN × VarN × Exp)) : Bool :=
  match funs with
  | [] => true
  | (_, _, e) :: rest => everyExp predicate e && everyExpFuns predicate rest
termination_by sizeOf funs
end

end Flapjack.AstHOL
