import Flapjack.TypeSystemHOL.Operators

/-! Declarative CakeML expression-typing infrastructure. `TypeE` uses an
inductively encoded branch list in its match and handler rules; HOL instead
states a membership-indexed existential for each branch. This translation
requires an equivalence proof and representation review before the judgments
can be tagged as HOL ports. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL Flapjack.Misc.Location

mutual
inductive TypeE : TypeEnv → TenvValExp → AstHOL.Exp → SemanticT → Prop where
  | intLit (env : TypeEnv) (localEnv : TenvValExp) (n : Int) :
      TypeE env localEnv (.lit (.intLit n)) (.app [] 5)
  | charLit (env : TypeEnv) (localEnv : TenvValExp) (c : HolChar) :
      TypeE env localEnv (.lit (.char c)) (.app [] 2)
  | stringLit (env : TypeEnv) (localEnv : TenvValExp) (s : MlString) :
      TypeE env localEnv (.lit (.strLit s)) (.app [] 8)
  | word8Lit (env : TypeEnv) (localEnv : TenvValExp) (w : BitVec 8) :
      TypeE env localEnv (.lit (.word8 w)) (.app [] 12)
  | word64Lit (env : TypeEnv) (localEnv : TenvValExp) (w : BitVec 64) :
      TypeE env localEnv (.lit (.word64 w)) (.app [] 11)
  | float64Lit (env : TypeEnv) (localEnv : TenvValExp) (w : BitVec 64) :
      TypeE env localEnv (.lit (.float64 w)) (.app [] 14)
  | raise (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp) (t : SemanticT)
      (free : checkFreevars (numTvs localEnv) [] t = true)
      (typed : TypeE env localEnv e (.app [] 3)) :
      TypeE env localEnv (.raise e) t
  | handle (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp)
      (clauses : List (Pat × AstHOL.Exp)) (t : SemanticT)
      (typed : TypeE env localEnv e t) (nonempty : clauses ≠ [])
      (branches : TypeBranches env localEnv (.app [] 3) t clauses) :
      TypeE env localEnv (.handle e clauses) t
  | constructor (env : TypeEnv) (localEnv : TenvValExp) (name : Ident MlString MlString)
      (es : List AstHOL.Exp) (params : List MlString) (id : Nat) (args types : List SemanticT)
      (free : args.all (checkFreevars (numTvs localEnv) []) = true)
      (arity : params.length = args.length)
      (typed : TypeEs env localEnv es (types.map (typeSubst (typeSubstMap (params.zip args)))))
      (lookup : nsLookup env.c name = some (params, types, id)) :
      TypeE env localEnv (.con (some name) es) (.app args id)
  | tuple (env : TypeEnv) (localEnv : TenvValExp) (es : List AstHOL.Exp) (types : List SemanticT)
      (typed : TypeEs env localEnv es types) : TypeE env localEnv (.con none es) (.app types 9)
  | var (env : TypeEnv) (localEnv : TenvValExp) (name : Ident MlString MlString)
      (t : SemanticT) (args : List SemanticT) (tvs : Nat)
      (arity : tvs = args.length) (free : args.all (checkFreevars (numTvs localEnv) []) = true)
      (lookup : lookupVar name localEnv env = some (tvs, t)) :
      TypeE env localEnv (.var name) (deBruijnSubst 0 args t)
  | fn (env : TypeEnv) (localEnv : TenvValExp) (name : MlString) (body : AstHOL.Exp) (t₁ t₂ : SemanticT)
      (free : checkFreevars (numTvs localEnv) [] t₁ = true)
      (typed : TypeE env (.bindName name 0 t₁ localEnv) body t₂) :
      TypeE env localEnv (.fn name body) (.app [t₁, t₂] 4)
  | app (env : TypeEnv) (localEnv : TenvValExp) (op : Op) (es : List AstHOL.Exp)
      (ts : List SemanticT) (t : SemanticT) (typed : TypeEs env localEnv es ts)
      (operator : typeOp op ts t) (free : checkFreevars (numTvs localEnv) [] t = true) :
      TypeE env localEnv (.app op es) t
  | log (env : TypeEnv) (localEnv : TenvValExp) (op : Lop) (e₁ e₂ : AstHOL.Exp)
      (first : TypeE env localEnv e₁ (.app [] 1)) (second : TypeE env localEnv e₂ (.app [] 1)) :
      TypeE env localEnv (.log op e₁ e₂) (.app [] 1)
  | if_ (env : TypeEnv) (localEnv : TenvValExp) (guard yes no : AstHOL.Exp) (t : SemanticT)
      (condition : TypeE env localEnv guard (.app [] 1)) (thenBranch : TypeE env localEnv yes t)
      (elseBranch : TypeE env localEnv no t) : TypeE env localEnv (.if_ guard yes no) t
  | match_ (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp) (clauses : List (Pat × AstHOL.Exp))
      (t₁ t₂ : SemanticT) (typed : TypeE env localEnv e t₁) (nonempty : clauses ≠ [])
      (branches : TypeBranches env localEnv t₁ t₂ clauses) :
      TypeE env localEnv (.mat e clauses) t₂
  | let_ (env : TypeEnv) (localEnv : TenvValExp) (name : Option MlString) (e₁ e₂ : AstHOL.Exp)
      (t₁ t₂ : SemanticT) (value : TypeE env localEnv e₁ t₁)
      (body : TypeE env (optBindName name 0 t₁ localEnv) e₂ t₂) :
      TypeE env localEnv (.let_ name e₁ e₂) t₂
  | letrec (env : TypeEnv) (localEnv : TenvValExp) (funs : List (MlString × MlString × AstHOL.Exp))
      (e : AstHOL.Exp) (t : SemanticT) (bindings : List (MlString × SemanticT))
      (functions : TypeFuns env (bindVarList 0 bindings localEnv) funs bindings)
      (body : TypeE env (bindVarList 0 bindings localEnv) e t) :
      TypeE env localEnv (.letrec funs e) t
  | annotation (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp) (t : AstT)
      (free : checkFreevarsAst [] t = true) (names : checkTypeNames env.t t = true)
      (typed : TypeE env localEnv e (typeNameSubst env.t t)) :
      TypeE env localEnv (.tannot e t) (typeNameSubst env.t t)
  | location (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp) (loc : Locs) (t : SemanticT)
      (typed : TypeE env localEnv e t) : TypeE env localEnv (.lannot e loc) t

inductive TypeEs : TypeEnv → TenvValExp → List AstHOL.Exp → List SemanticT → Prop where
  | nil (env : TypeEnv) (localEnv : TenvValExp) : TypeEs env localEnv [] []
  | cons (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp) (es : List AstHOL.Exp)
      (t : SemanticT) (ts : List SemanticT) (head : TypeE env localEnv e t)
      (tail : TypeEs env localEnv es ts) : TypeEs env localEnv (e :: es) (t :: ts)

inductive TypeFuns : TypeEnv → TenvValExp → List (MlString × MlString × AstHOL.Exp) →
    List (MlString × SemanticT) → Prop where
  | nil (env : TypeEnv) (localEnv : TenvValExp) : TypeFuns env localEnv [] []
  | cons (env : TypeEnv) (localEnv : TenvValExp) (name arg : MlString) (body : AstHOL.Exp)
      (funs : List (MlString × MlString × AstHOL.Exp)) (bindings : List (MlString × SemanticT))
      (t₁ t₂ : SemanticT) (free : checkFreevars (numTvs localEnv) [] (.app [t₁, t₂] 4) = true)
      (typed : TypeE env (.bindName arg 0 t₁ localEnv) body t₂)
      (tail : TypeFuns env localEnv funs bindings) (unique : bindings.lookup name = none) :
      TypeFuns env localEnv ((name, arg, body) :: funs) ((name, .app [t₁, t₂] 4) :: bindings)
/-- Flapjack list encoding of the source branch premises; its equivalence to
HOL's membership-indexed condition is proved separately below. -/
inductive TypeBranches : TypeEnv → TenvValExp → SemanticT → SemanticT → List (Pat × AstHOL.Exp) → Prop where
  | nil (env : TypeEnv) (localEnv : TenvValExp) (input output : SemanticT) :
      TypeBranches env localEnv input output []
  | cons (env : TypeEnv) (localEnv : TenvValExp) (input output : SemanticT)
      (p : Pat) (body : AstHOL.Exp) (rest : List (Pat × AstHOL.Exp))
      (bindings : List (MlString × SemanticT)) (distinct : (patBindings p).Nodup)
      (pattern : TypeP (numTvs localEnv) env p input bindings)
      (expression : TypeE env (bindVarList 0 bindings localEnv) body output)
      (tail : TypeBranches env localEnv input output rest) :
      TypeBranches env localEnv input output ((p, body) :: rest)
end

/-- Flapjack equivalence between the inductive branch-list encoding and the
membership-indexed existential used in the source typing rules. -/
theorem typeBranches_iff (env : TypeEnv) (localEnv : TenvValExp) (input output : SemanticT)
    (clauses : List (Pat × AstHOL.Exp)) :
    TypeBranches env localEnv input output clauses ↔
      ∀ p body, (p, body) ∈ clauses → ∃ bindings,
        (patBindings p).Nodup ∧ TypeP (numTvs localEnv) env p input bindings ∧
          TypeE env (bindVarList 0 bindings localEnv) body output := by
  constructor
  · induction clauses with
    | nil => simp
    | cons first rest ih =>
      rcases first with ⟨pattern, body⟩
      intro h p e member
      cases h with
      | cons _ _ _ _ _ _ bindings distinct typedPattern typedBody tail =>
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · cases equal
          exact ⟨bindings, distinct, typedPattern, typedBody⟩
        · exact ih tail p e member
  · induction clauses with
    | nil => intro _; exact .nil env localEnv input output
    | cons first rest ih =>
      rcases first with ⟨p, body⟩
      intro h
      obtain ⟨bindings, distinct, typedPattern, typedBody⟩ := h p body (by simp)
      apply TypeBranches.cons env localEnv input output p body rest bindings distinct typedPattern typedBody
      apply ih
      intro p' body' member
      exact h p' body' (by simp [member])

/-- Flapjack helper with the source-shaped handler premises. -/
theorem typeE_handle_source (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp)
    (clauses : List (Pat × AstHOL.Exp)) (t : SemanticT)
    (typed : TypeE env localEnv e t) (nonempty : clauses ≠ [])
    (branches : ∀ p body, (p, body) ∈ clauses → ∃ bindings,
      (patBindings p).Nodup ∧ TypeP (numTvs localEnv) env p (.app [] 3) bindings ∧
        TypeE env (bindVarList 0 bindings localEnv) body t) :
    TypeE env localEnv (.handle e clauses) t :=
  .handle env localEnv e clauses t typed nonempty
    ((typeBranches_iff env localEnv (.app [] 3) t clauses).mpr branches)

/-- Flapjack helper with the source-shaped match premises. -/
theorem typeE_match_source (env : TypeEnv) (localEnv : TenvValExp) (e : AstHOL.Exp)
    (clauses : List (Pat × AstHOL.Exp)) (t₁ t₂ : SemanticT)
    (typed : TypeE env localEnv e t₁) (nonempty : clauses ≠ [])
    (branches : ∀ p body, (p, body) ∈ clauses → ∃ bindings,
      (patBindings p).Nodup ∧ TypeP (numTvs localEnv) env p t₁ bindings ∧
        TypeE env (bindVarList 0 bindings localEnv) body t₂) :
    TypeE env localEnv (.mat e clauses) t₂ :=
  .match_ env localEnv e clauses t₁ t₂ typed nonempty
    ((typeBranches_iff env localEnv t₁ t₂ clauses).mpr branches)

end Flapjack.TypeSystemHOL
