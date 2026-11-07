import Flapjack.TypeSystemHOL.Expressions
import Flapjack.TypeSystemHOL.Values
import Flapjack.SemanticPrimitivesHOL.Control

/-! Prerequisites for declarative declaration typing. The expression judgment
uses a proved-equivalent branch-list encoding and remains pending full source
and carrier review. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/semantics/typeSystemScript.sml" "check_ctor_tenv_def"]
def checkCtorTenv (env : TenvAbbrev) : TypeDef → Prop
  | [] => True
  | (tvs, name, ctors) :: rest =>
    checkDupCtors (tvs, name, ctors) = true ∧ tvs.Nodup ∧
    (∀ ctor ∈ ctors, ∀ t ∈ ctor.2, checkFreevarsAst tvs t = true ∧ checkTypeNames env t = true) ∧
    name ∉ rest.map (fun (_, name, _) => name) ∧ checkCtorTenv env rest

@[hol "cakeml/semantics/typeSystemScript.sml" "build_ctor_tenv_def"]
def buildCtorTenv (env : TenvAbbrev) : TypeDef → List Nat → TenvCtor
  | [], [] => alistToNs []
  | (tvs, _, ctors) :: rest, id :: ids =>
    nsAppend (buildCtorTenv env rest ids)
      (alistToNs ((ctors.map fun (name, ts) =>
        (name, (tvs, ts.map (typeNameSubst env), id))).reverse))
  | _, _ => alistToNs []

@[hol "cakeml/semantics/typeSystemScript.sml" "tenv_add_tvs_def"]
def tenvAddTvs (tvs : Nat) (bindings : List (MlString × SemanticT)) : List (MlString × (Nat × SemanticT)) :=
  bindings.map (fun (name, t) => (name, (tvs, t)))

/-- Flapjack infrastructure corresponding to the shape of source pattern and
expression determinacy. It uses the unreviewed `TypeE` encoding. -/
def typePeDeterm (env : TypeEnv) (localEnv : TenvValExp) (p : Pat) (e : AstHOL.Exp) : Prop :=
  ∀ t₁ bindings₁ t₂ bindings₂,
    TypeP 0 env p t₁ bindings₁ ∧ TypeE env localEnv e t₁ ∧
    TypeP 0 env p t₂ bindings₂ ∧ TypeE env localEnv e t₂ → bindings₁ = bindings₂

@[hol "cakeml/semantics/typeSystemScript.sml" "tscheme_inst_def"]
def tschemeInst (spec impl : Nat × SemanticT) : Prop :=
  ∃ subst : List SemanticT, subst.length = impl.1 ∧
    checkFreevars impl.1 [] impl.2 = true ∧
    subst.all (checkFreevars spec.1 []) = true ∧
    deBruijnSubst 0 subst impl.2 = spec.2

@[hol "cakeml/semantics/typeSystemScript.sml" "tenvLift_def"]
def tenvLift (name : MlString) (env : TypeEnv) : TypeEnv :=
  ⟨nsLift name env.v, nsLift name env.c, nsLift name env.t⟩

/-- Flapjack rendering of HOL's pointwise `EVERY2` list relation. -/
inductive every2 {α β : Type} (rel : α → β → Prop) : List α → List β → Prop where
  | nil : every2 rel [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} :
      rel x y → every2 rel xs ys → every2 rel (x :: xs) (y :: ys)

/-- Flapjack representation of HOL sets of type identifiers by membership. -/
abbrev TypeIds := Nat → Prop

/-- Flapjack helper for disjointness of two identifier sets. -/
def disjointTypeIds (a b : TypeIds) : Prop := ∀ id, a id → b id → False

/-- Flapjack helper for the union of two identifier sets. -/
def unionTypeIds (a b : TypeIds) : TypeIds := fun id => a id ∨ b id

@[hol "cakeml/semantics/typeSystemScript.sml" "prim_type_nums_def"]
def primTypeNums : List Nat := [0, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14]

/-! `TypeD` and `TypeDs` follow the source declaration rules but depend on the
untagged `TypeE` representation. Their source correspondence remains open;
they are Flapjack infrastructure until that dependency is reviewed. -/
mutual
inductive TypeD : Bool → TypeEnv → Dec → TypeIds → TypeEnv → Prop where
  | value (extra : Bool) (tvs : Nat) (env : TypeEnv) (p : Pat) (e : AstHOL.Exp)
      (t : SemanticT) (bindings : List (MlString × SemanticT)) (loc : Misc.Location.Locs)
      (value : isValue e = true) (distinct : (patBindings p).Nodup)
      (pattern : TypeP tvs env p t bindings) (expression : TypeE env (bindTvar tvs .empty) e t)
      (principal : extra = true → ∀ tvs' bindings' t',
        TypeP tvs' env p t' bindings' ∧ TypeE env (bindTvar tvs' .empty) e t' →
          every2 tschemeInst ((tenvAddTvs tvs' bindings').map Prod.snd)
            ((tenvAddTvs tvs bindings).map Prod.snd)) :
      TypeD extra env (.dlet loc p e) (fun _ => False) ⟨alistToNs (tenvAddTvs tvs bindings), nsEmpty, nsEmpty⟩
  | monomorphic (extra : Bool) (env : TypeEnv) (p : Pat) (e : AstHOL.Exp)
      (t : SemanticT) (bindings : List (MlString × SemanticT)) (loc : Misc.Location.Locs)
      (restricted : extra = true → isValue e = false ∧ typePeDeterm env .empty p e)
      (distinct : (patBindings p).Nodup) (pattern : TypeP 0 env p t bindings)
      (expression : TypeE env .empty e t) :
      TypeD extra env (.dlet loc p e) (fun _ => False) ⟨alistToNs (tenvAddTvs 0 bindings), nsEmpty, nsEmpty⟩
  | recursive (extra : Bool) (env : TypeEnv) (funs : List (MlString × MlString × AstHOL.Exp))
      (bindings : List (MlString × SemanticT)) (tvs : Nat) (loc : Misc.Location.Locs)
      (typed : TypeFuns env (bindVarList 0 bindings (bindTvar tvs .empty)) funs bindings)
      (principal : extra = true → ∀ tvs' bindings',
        TypeFuns env (bindVarList 0 bindings' (bindTvar tvs' .empty)) funs bindings' →
          every2 tschemeInst ((tenvAddTvs tvs' bindings').map Prod.snd)
            ((tenvAddTvs tvs bindings).map Prod.snd)) :
      TypeD extra env (.dletrec loc funs) (fun _ => False) ⟨alistToNs (tenvAddTvs tvs bindings), nsEmpty, nsEmpty⟩
  | datatype (extra : Bool) (env : TypeEnv) (defs : TypeDef) (ids : List Nat)
      (newTypes : TenvAbbrev) (loc : Misc.Location.Locs) (distinct : ids.Nodup)
      (fresh : disjointTypeIds (fun id => id ∈ ids) (fun id => id ∈ 6 :: 1 :: primTypeNums))
      (valid : checkCtorTenv (nsAppend newTypes env.t) defs) (arity : ids.length = defs.length)
      (types : newTypes = alistToNs ((defs.zip ids).map fun ((params, name, _), id) =>
        (name, (params, .app (params.map SemanticT.var) id)))) :
      TypeD extra env (.dtype loc defs) (fun id => id ∈ ids)
        ⟨nsEmpty, buildCtorTenv (nsAppend newTypes env.t) defs ids, newTypes⟩
  | abbreviation (extra : Bool) (env : TypeEnv) (tvs : List MlString) (name : MlString)
      (t : AstT) (loc : Misc.Location.Locs) (free : checkFreevarsAst tvs t = true)
      (names : checkTypeNames env.t t = true) (distinct : tvs.Nodup) :
      TypeD extra env (.dtabbrev loc tvs name t) (fun _ => False)
        ⟨nsEmpty, nsEmpty, nsSing name (tvs, typeNameSubst env.t t)⟩
  | exception (extra : Bool) (env : TypeEnv) (name : MlString) (ts : List AstT) (loc : Misc.Location.Locs)
      (free : ts.all (checkFreevarsAst []) = true) (names : ts.all (checkTypeNames env.t) = true) :
      TypeD extra env (.dexn loc name ts) (fun _ => False)
        ⟨nsEmpty, nsSing name ([], ts.map (typeNameSubst env.t), 3), nsEmpty⟩
  | module_ (extra : Bool) (env : TypeEnv) (name : MlString) (ds : List Dec)
      (ids : TypeIds) (newEnv : TypeEnv) (typed : TypeDs extra env ds ids newEnv) :
      TypeD extra env (.dmod name ds) ids (tenvLift name newEnv)
  | local_ (extra : Bool) (env : TypeEnv) (privateDs publicDs : List Dec)
      (env₁ env₂ : TypeEnv) (ids₁ ids₂ : TypeIds)
      (first : TypeDs extra env privateDs ids₁ env₁)
      (second : TypeDs extra (extendDecTenv env₁ env) publicDs ids₂ env₂)
      (disjoint : disjointTypeIds ids₁ ids₂) :
      TypeD extra env (.dlocal privateDs publicDs) (unionTypeIds ids₁ ids₂) env₂

inductive TypeDs : Bool → TypeEnv → List Dec → TypeIds → TypeEnv → Prop where
  | nil (extra : Bool) (env : TypeEnv) : TypeDs extra env [] (fun _ => False) ⟨nsEmpty, nsEmpty, nsEmpty⟩
  | cons (extra : Bool) (env : TypeEnv) (d : Dec) (ds : List Dec) (env₁ env₂ : TypeEnv)
      (ids₁ ids₂ : TypeIds) (head : TypeD extra env d ids₁ env₁)
      (tail : TypeDs extra (extendDecTenv env₁ env) ds ids₂ env₂)
      (disjoint : disjointTypeIds ids₁ ids₂) :
      TypeDs extra env (d :: ds) (unionTypeIds ids₁ ids₂) (extendDecTenv env₂ env₁)
end

end Flapjack.TypeSystemHOL
