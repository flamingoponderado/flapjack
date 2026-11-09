import Flapjack.TypeSystemHOL.TypeNames

/-! Declarative CakeML pattern typing. The judgments below retain the original
rules; full source and carrier review remains pending. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL

mutual
/-- The original pattern-typing judgment, including constructor instantiation
and source annotation checks. -/
@[hol "cakeml/semantics/typeSystemScript.sml" "type_p"]
inductive TypeP : Nat → TypeEnv → Pat → SemanticT → List (MlString × SemanticT) → Prop where
  | any (tvs : Nat) (env : TypeEnv) (t : SemanticT)
      (free : checkFreevars tvs [] t = true) :
      TypeP tvs env .pany t []
  | var (tvs : Nat) (env : TypeEnv) (name : MlString) (t : SemanticT)
      (free : checkFreevars tvs [] t = true) :
      TypeP tvs env (.pvar name) t [(name, t)]
  | intLit (tvs : Nat) (env : TypeEnv) (n : Int) :
      TypeP tvs env (.plit (.intLit n)) (.app [] 5) []
  | charLit (tvs : Nat) (env : TypeEnv) (c : HolChar) :
      TypeP tvs env (.plit (.char c)) (.app [] 2) []
  | stringLit (tvs : Nat) (env : TypeEnv) (s : MlString) :
      TypeP tvs env (.plit (.strLit s)) (.app [] 8) []
  | word8Lit (tvs : Nat) (env : TypeEnv) (w : BitVec 8) :
      TypeP tvs env (.plit (.word8 w)) (.app [] 12) []
  | word64Lit (tvs : Nat) (env : TypeEnv) (w : BitVec 64) :
      TypeP tvs env (.plit (.word64 w)) (.app [] 11) []
  | constructor (tvs : Nat) (env : TypeEnv) (name : Ident MlString MlString)
      (ps : List Pat) (types : List SemanticT) (params : List MlString) (id : Nat)
      (args : List SemanticT) (bindings : List (MlString × SemanticT))
      (free : args.all (checkFreevars tvs []) = true)
      (arity : args.length = params.length)
      (typed : TypePs tvs env ps (types.map (typeSubst (typeSubstMap (params.zip args)))) bindings)
      (lookup : nsLookup env.c name = some (params, types, id)) :
      TypeP tvs env (.pcon (some name) ps) (.app args id) bindings
  | tuple (tvs : Nat) (env : TypeEnv) (ps : List Pat) (types : List SemanticT)
      (bindings : List (MlString × SemanticT)) (typed : TypePs tvs env ps types bindings) :
      TypeP tvs env (.pcon none ps) (.app types 9) bindings
  | reference (tvs : Nat) (env : TypeEnv) (p : Pat) (t : SemanticT)
      (bindings : List (MlString × SemanticT)) (typed : TypeP tvs env p t bindings) :
      TypeP tvs env (.pref p) (.app [t] 7) bindings
  | asPattern (tvs : Nat) (env : TypeEnv) (p : Pat) (name : MlString) (t : SemanticT)
      (bindings : List (MlString × SemanticT)) (typed : TypeP tvs env p t bindings) :
      TypeP tvs env (.pas p name) t (bindings ++ [(name, t)])
  | annotation (tvs : Nat) (env : TypeEnv) (p : Pat) (t : AstT)
      (bindings : List (MlString × SemanticT))
      (free : checkFreevarsAst [] t = true) (names : checkTypeNames env.t t = true)
      (typed : TypeP tvs env p (typeNameSubst env.t t) bindings) :
      TypeP tvs env (.ptannot p t) (typeNameSubst env.t t) bindings

/-- The mutually defined source judgment for lists of patterns. -/
@[hol "cakeml/semantics/typeSystemScript.sml" "type_p"]
inductive TypePs : Nat → TypeEnv → List Pat → List SemanticT → List (MlString × SemanticT) → Prop where
  | nil (tvs : Nat) (env : TypeEnv) : TypePs tvs env [] [] []
  | cons (tvs : Nat) (env : TypeEnv) (p : Pat) (ps : List Pat)
      (t : SemanticT) (ts : List SemanticT) (bindings rest : List (MlString × SemanticT))
      (head : TypeP tvs env p t bindings) (tail : TypePs tvs env ps ts rest) :
      TypePs tvs env (p :: ps) (t :: ts) (rest ++ bindings)
end

end Flapjack.TypeSystemHOL
