import Flapjack.TypeSystemHOL
import Flapjack.NamespaceHOL
import Flapjack.AstHOL.Syntax

/-! Type-variable operations and environments for CakeML's declarative type
system. The typing judgments and their metatheory are not yet ported. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "check_freevars_def"]
def checkFreevars (dbmax : Nat) (tvs : List MlString) : SemanticT → Bool
  | .var tv => tvs.contains tv
  | .varDb n => n < dbmax
  | .app ts _ => checkFreevarsList dbmax tvs ts
termination_by t => sizeOf t

/-- Flapjack mutual-recursion helper for checking a list of semantic types. -/
def checkFreevarsList (dbmax : Nat) (tvs : List MlString) : List SemanticT → Bool
  | [] => true
  | t :: ts => checkFreevars dbmax tvs t && checkFreevarsList dbmax tvs ts
termination_by ts => sizeOf ts
end

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "check_freevars_ast_def"]
def checkFreevarsAst (tvs : List MlString) : AstT → Bool
  | .atvar tv => tvs.contains tv
  | .attup ts => checkFreevarsAstList tvs ts
  | .atfun t₁ t₂ => checkFreevarsAst tvs t₁ && checkFreevarsAst tvs t₂
  | .atapp ts _ => checkFreevarsAstList tvs ts
termination_by t => sizeOf t

/-- Flapjack mutual-recursion helper for checking a list of source types. -/
def checkFreevarsAstList (tvs : List MlString) : List AstT → Bool
  | [] => true
  | t :: ts => checkFreevarsAst tvs t && checkFreevarsAstList tvs ts
termination_by ts => sizeOf ts
end

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "deBruijn_inc_def"]
def deBruijnInc (skip amount : Nat) : SemanticT → SemanticT
  | .var tv => .var tv
  | .varDb n => .varDb (if n < skip then n else n + amount)
  | .app ts id => .app (deBruijnIncList skip amount ts) id
termination_by t => sizeOf t

/-- Flapjack mutual-recursion helper for incrementing a list of types. -/
def deBruijnIncList (skip amount : Nat) : List SemanticT → List SemanticT
  | [] => []
  | t :: ts => deBruijnInc skip amount t :: deBruijnIncList skip amount ts
termination_by ts => sizeOf ts
end

mutual
@[hol "cakeml/semantics/typeSystemScript.sml" "deBruijn_subst_def"]
def deBruijnSubst (skip : Nat) (replacement : List SemanticT) : SemanticT → SemanticT
  | .var tv => .var tv
  | .varDb n =>
    if h : skip ≤ n ∧ n < replacement.length + skip then
      replacement[n - skip]'(by omega)
    else if skip ≤ n then .varDb (n - replacement.length) else .varDb n
  | .app ts id => .app (deBruijnSubstList skip replacement ts) id
termination_by t => sizeOf t

/-- Flapjack mutual-recursion helper for substitution in a list of types. -/
def deBruijnSubstList (skip : Nat) (replacement : List SemanticT) : List SemanticT → List SemanticT
  | [] => []
  | t :: ts => deBruijnSubst skip replacement t :: deBruijnSubstList skip replacement ts
termination_by ts => sizeOf ts
end

@[hol "cakeml/semantics/typeSystemScript.sml" "tenv_val_exp"]
inductive TenvValExp where
  | empty
  | bindTvar : Nat → TenvValExp → TenvValExp
  | bindName : MlString → Nat → SemanticT → TenvValExp → TenvValExp

@[hol "cakeml/semantics/typeSystemScript.sml" "bind_tvar_def"]
def bindTvar (tvs : Nat) (env : TenvValExp) : TenvValExp :=
  if tvs = 0 then env else .bindTvar tvs env

@[hol "cakeml/semantics/typeSystemScript.sml" "opt_bind_name_def"]
def optBindName (name : Option MlString) (tvs : Nat) (t : SemanticT) (env : TenvValExp) : TenvValExp :=
  match name with
  | none => env
  | some name => .bindName name tvs t env

@[hol "cakeml/semantics/typeSystemScript.sml" "tveLookup_def"]
def tveLookup (name : MlString) (inc : Nat) : TenvValExp → Option (Nat × SemanticT)
  | .empty => none
  | .bindTvar tvs env => tveLookup name (inc + tvs) env
  | .bindName name' tvs t env =>
    if name' = name then some (tvs, deBruijnInc tvs inc t) else tveLookup name inc env

@[hol "cakeml/semantics/typeSystemScript.sml" "tenv_abbrev"]
abbrev TenvAbbrev := Namespace MlString MlString (List MlString × SemanticT)

@[hol "cakeml/semantics/typeSystemScript.sml" "tenv_ctor"]
abbrev TenvCtor := Namespace MlString MlString (List MlString × List SemanticT × TypeIdent)

@[hol "cakeml/semantics/typeSystemScript.sml" "tenv_val"]
abbrev TenvVal := Namespace MlString MlString (Nat × SemanticT)

@[hol "cakeml/semantics/typeSystemScript.sml" "type_env"]
structure TypeEnv where
  v : TenvVal
  c : TenvCtor
  t : TenvAbbrev

@[hol "cakeml/semantics/typeSystemScript.sml" "extend_dec_tenv_def"]
def extendDecTenv (new old : TypeEnv) : TypeEnv :=
  ⟨nsAppend new.v old.v, nsAppend new.c old.c, nsAppend new.t old.t⟩

@[hol "cakeml/semantics/typeSystemScript.sml" "lookup_varE_def"]
def lookupVarE (id : Ident MlString MlString) (env : TenvValExp) : Option (Nat × SemanticT) :=
  match id with
  | .short name => tveLookup name 0 env
  | .long _ _ => none

@[hol "cakeml/semantics/typeSystemScript.sml" "lookup_var_def"]
def lookupVar (id : Ident MlString MlString) (localEnv : TenvValExp) (env : TypeEnv) : Option (Nat × SemanticT) :=
  match lookupVarE id localEnv with
  | some value => some value
  | none => nsLookup env.v id

@[hol "cakeml/semantics/typeSystemScript.sml" "num_tvs_def"]
def numTvs : TenvValExp → Nat
  | .empty => 0
  | .bindTvar tvs env => tvs + numTvs env
  | .bindName _ _ _ env => numTvs env

@[hol "cakeml/semantics/typeSystemScript.sml" "bind_var_list_def"]
def bindVarList (tvs : Nat) : List (MlString × SemanticT) → TenvValExp → TenvValExp
  | [], env => env
  | (name, t) :: binds, env => .bindName name tvs t (bindVarList tvs binds env)

end Flapjack.TypeSystemHOL
