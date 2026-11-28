module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.HolArb
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-!
# Free variables of source expressions

Lean counterparts of `FV_def` and `FV_dec_def` in
`cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml:639-690`, plus the
`BIGUNION` characterizations `FV_pes_MAP` and `FV_defs_MAP`.

HOL's `set` of a list is a set-builder over membership, `IMAGE` is `Set.image`
and `BIGUNION` is `⋃₀`.  In HOL `DIFF` and `∪` share one left-associative
precedence level, so `FV_defs defs ∪ FV b DIFF set ...` parses as
`(FV_defs defs ∪ FV b) DIFF set ...` (checked by parsing the source term in the
probe build); the Lean `letrec` clause keeps those parentheses, since Lean's
`\` binds tighter than `∪`.  `FV_dec`'s `Lit ARB` is `holArb` at the literal
carrier, and HOL's unspecified clauses for `Dmod`/`Dlocal`/`Denv` are `holArb`
at the set carrier.
-/

namespace Flapjack.SemanticPrimitivesProps
open AstHOL Flapjack.NamespaceHOL

/-- The literal carrier is inhabited, so HOL's `Lit ARB` has a Lean value. -/
local instance freeVarsLitInhabited : Nonempty Lit := ⟨.intLit 0⟩

/-- The set of names bound by a mutually recursive definition group. -/
def letrecBound (defs : List (VarN × VarN × AstHOL.Exp)) : Set (Ident ModN ConN) :=
  {id | ∃ entry ∈ defs, id = Ident.short entry.1}

mutual
/-- Original `FV_def`: the free variables of an expression. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "FV_def"]
def freeVars : AstHOL.Exp → Set (Ident ModN ConN)
  | .raise e => freeVars e
  | .handle e pes => freeVars e ∪ freeVarsPes pes
  | .lit _ => ∅
  | .con _ es => freeVarsList es
  | .var id => {id}
  | .fn x e => freeVars e \ {Ident.short x}
  | .app _ es => freeVarsList es
  | .log _ e1 e2 => freeVars e1 ∪ freeVars e2
  | .if_ e1 e2 e3 => freeVars e1 ∪ freeVars e2 ∪ freeVars e3
  | .mat e pes => freeVars e ∪ freeVarsPes pes
  | .let_ xo e b =>
      freeVars e ∪ (freeVars b \ (match xo with | none => ∅ | some x => {Ident.short x}))
  | .letrec defs b => (freeVarsDefs defs ∪ freeVars b) \ letrecBound defs
  | .tannot e _ => freeVars e
  | .lannot e _ => freeVars e
termination_by e => sizeOf e

/-- The `FV_list` clauses of HOL `FV_def`. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "FV_def"]
def freeVarsList : List AstHOL.Exp → Set (Ident ModN ConN)
  | [] => ∅
  | e :: es => freeVars e ∪ freeVarsList es
termination_by es => sizeOf es

/-- The `FV_pes` clauses of HOL `FV_def`. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "FV_def"]
def freeVarsPes : List (Pat × AstHOL.Exp) → Set (Ident ModN ConN)
  | [] => ∅
  | (p, e) :: pes =>
      (freeVars e \ (fun x => Ident.short x) '' {x | x ∈ patBindings p}) ∪ freeVarsPes pes
termination_by pes => sizeOf pes

/-- The `FV_defs` clauses of HOL `FV_def`. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "FV_def"]
def freeVarsDefs : List (VarN × VarN × AstHOL.Exp) → Set (Ident ModN ConN)
  | [] => ∅
  | (_, x, e) :: defs => (freeVars e \ {Ident.short x}) ∪ freeVarsDefs defs
termination_by defs => sizeOf defs
end

/-- Original `FV_dec_def`: the free variables of a top-level declaration. HOL
defines only the five clauses below; the module/local/env declarations are
unspecified (`ARB`), rendered by `holArb` at the set carrier. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "FV_dec_def"]
noncomputable def freeVarsDec : Dec → Set (Ident ModN ConN)
  | .dlet _ p e => freeVars (.mat e [(p, .lit (holArb Lit))])
  | .dletrec _ defs => freeVars (.letrec defs (.lit (holArb Lit)))
  | .dtype _ _ => ∅
  | .dtabbrev _ _ _ _ => ∅
  | .dexn _ _ _ => ∅
  | _ => holArb (Set (Ident ModN ConN))

/-- Original `FV_pes_MAP`: the pattern-match group is the union over its entries
of the expression's free variables minus the pattern's bindings. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "FV_pes_MAP"]
theorem freeVarsPes_eq_biUnion (pes : List (Pat × AstHOL.Exp)) :
    freeVarsPes pes =
      ⋃₀ ((fun pe => freeVars pe.2 \ (fun x => Ident.short x) '' {x | x ∈ patBindings pe.1})
        '' {pe | pe ∈ pes}) := by
  induction pes with
  | nil => simp [freeVarsPes]
  | cons pe pes ih =>
    obtain ⟨p, e⟩ := pe
    simp [freeVarsPes, ih]

/-- Original `FV_defs_MAP`: the recursive group is the union over its entries of
the body's free variables minus the entry's function name. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "FV_defs_MAP"]
theorem freeVarsDefs_eq_biUnion (ls : List (VarN × VarN × AstHOL.Exp)) :
    freeVarsDefs ls =
      ⋃₀ ((fun entry => freeVars entry.2.2 \ {Ident.short entry.2.1}) '' {entry | entry ∈ ls}) := by
  induction ls with
  | nil => simp [freeVarsDefs]
  | cons entry ls ih =>
    obtain ⟨f, x, e⟩ := entry
    simp [freeVarsDefs, ih]

end Flapjack.SemanticPrimitivesProps
