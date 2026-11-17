module

public import Flapjack.TypeSoundInvariants.CtorMap
public import Batteries.Data.List.Basic

@[expose] public section

/-! Source value typing. The complete HOL `type_v` judgment is represented
using two finite-support maps and mutually inductive list and namespace premise
relations. The latter are proved equivalent below, but the supported HOL tag
qualifiers do not yet cover this combination; the judgment remains untagged. -/
namespace Flapjack.TypeSoundInvariants
open Flapjack Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

abbrev CtorTypes := HolFiniteMapExact Stamp (List MlString × List SemanticT × TypeIdent)
abbrev StoreTypes := HolFiniteMapExact Nat StoreT

mutual
inductive TypeV : Nat → CtorTypes → StoreTypes → Value → SemanticT → Prop where
  | intLit (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (n : Int) :
      TypeV tvs ctors store (.litv (.intLit n)) Tint
  | charLit (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (c : HolChar) :
      TypeV tvs ctors store (.litv (.char c)) Tchar
  | stringLit (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (s : MlString) :
      TypeV tvs ctors store (.litv (.strLit s)) Tstring
  | word8Lit (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (w : BitVec 8) :
      TypeV tvs ctors store (.litv (.word8 w)) Tword8
  | word64Lit (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (w : BitVec 64) :
      TypeV tvs ctors store (.litv (.word64 w)) Tword64
  | float64Lit (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (w : BitVec 64) :
      TypeV tvs ctors store (.litv (.float64 w)) Tdouble
  | constructor (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes)
      (vs : List Value) (params : List MlString) (stamp : Stamp)
      (args types : List SemanticT) (id : TypeIdent)
      (free : args.all (checkFreevars tvs []) = true) (arity : params.length = args.length)
      (values : TypeVList tvs ctors store vs
        (types.map (typeSubst (typeSubstMap (params.zip args)))))
      (lookup : ctors.lookup stamp = some (params, types, id)) :
      TypeV tvs ctors store (.conv (some stamp) vs) (.app args id)
  | tuple (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes)
      (vs : List Value) (types : List SemanticT)
      (values : TypeVList tvs ctors store vs types) :
      TypeV tvs ctors store (.conv none vs) (Ttup types)
  | closure (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes)
      (env : SemEnv Value) (tenv : TypeEnv) (localEnv : TenvValExp)
      (name : MlString) (body : AstHOL.Exp) (t1 t2 : SemanticT)
      (tenvOk : tenvOk tenv) (localOk : tenvValExpOk localEnv)
      (closed : numTvs localEnv = 0)
      (constructors : nsAll2 (typeCtor ctors) env.c tenv.c)
      (values : TypeVEnv ctors store env.v (addTenvE localEnv tenv.v))
      (free : checkFreevars tvs [] t1 = true)
      (bodyType : TypeE tenv (.bindName name 0 t1 (bindTvar tvs localEnv)) body t2) :
      TypeV tvs ctors store (.closure env name body) (Tfn t1 t2)
  | recclosure (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes)
      (env : SemEnv Value) (funs : List (MlString × MlString × AstHOL.Exp))
      (name : MlString) (t : SemanticT) (tenv : TypeEnv) (localEnv : TenvValExp)
      (bindings : List (MlString × SemanticT))
      (tenvOk : tenvOk tenv) (localOk : tenvValExpOk localEnv)
      (closed : numTvs localEnv = 0)
      (constructors : nsAll2 (typeCtor ctors) env.c tenv.c)
      (values : TypeVEnv ctors store env.v (addTenvE localEnv tenv.v))
      (typed : TypeFuns tenv (bindVarList 0 bindings (bindTvar tvs localEnv)) funs bindings)
      (lookup : bindings.lookup name = some t)
      (distinct : (funs.map Prod.fst).Nodup) (member : name ∈ funs.map Prod.fst) :
      TypeV tvs ctors store (.recclosure env funs name) t
  | reference (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (n : Nat) (t : SemanticT)
      (free : checkFreevars 0 [] t = true) (lookup : store.lookup n = some (.refT t)) :
      TypeV tvs ctors store (.loc true n) (Tref t)
  | byteArray (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (n : Nat)
      (lookup : store.lookup n = some .w8arrayT) :
      TypeV tvs ctors store (.loc true n) Tword8array
  | array (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (n : Nat) (t : SemanticT)
      (free : checkFreevars 0 [] t = true) (lookup : store.lookup n = some (.varrayT t)) :
      TypeV tvs ctors store (.loc true n) (Tarray t)
  | vector (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (vs : List Value) (t : SemanticT)
      (free : checkFreevars 0 [] t = true) (values : ∀ v ∈ vs, TypeV tvs ctors store v t) :
      TypeV tvs ctors store (.vectorv vs) (Tvector t)

/-- Flapjack's mutual encoding of the source `LIST_REL` premise. -/
inductive TypeVList : Nat → CtorTypes → StoreTypes → List Value → List SemanticT → Prop where
  | nil (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) :
      TypeVList tvs ctors store [] []
  | cons (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes) (v : Value) (t : SemanticT)
      (vs : List Value) (ts : List SemanticT) (head : TypeV tvs ctors store v t)
      (tail : TypeVList tvs ctors store vs ts) : TypeVList tvs ctors store (v :: vs) (t :: ts)

/-- Flapjack's witness-based mutual encoding of the source `nsAll2` premise. -/
inductive TypeVEnv : CtorTypes → StoreTypes → Namespace MlString MlString Value →
    Namespace MlString MlString (Nat × SemanticT) → Prop where
  | related (ctors : CtorTypes) (store : StoreTypes)
      (values : Namespace MlString MlString Value) (types : Namespace MlString MlString (Nat × SemanticT))
      (forward : Ident MlString MlString → Value → Nat × SemanticT)
      (backward : Ident MlString MlString → (Nat × SemanticT) → Value)
      (forwardLookup : ∀ id v, nsLookup values id = some v → nsLookup types id = some (forward id v))
      (forwardTyped : ∀ id v, nsLookup values id = some v →
        TypeV (forward id v).1 ctors store v (forward id v).2)
      (forwardModules : ∀ path, nsLookupMod types path = none → nsLookupMod values path = none)
      (backwardLookup : ∀ id entry, nsLookup types id = some entry → nsLookup values id = some (backward id entry))
      (backwardTyped : ∀ id entry, nsLookup types id = some entry →
        TypeV entry.1 ctors store (backward id entry) entry.2)
      (backwardModules : ∀ path, nsLookupMod values path = none → nsLookupMod types path = none) :
      TypeVEnv ctors store values types
end

/-- The inductive packaging of value lists is exactly HOL's pointwise list relation. -/
theorem typeVList_iff (tvs : Nat) (ctors : CtorTypes) (store : StoreTypes)
    (vs : List Value) (ts : List SemanticT) :
    TypeVList tvs ctors store vs ts ↔ List.Forall₂ (TypeV tvs ctors store) vs ts := by
  induction vs generalizing ts with
  | nil =>
      cases ts with
      | nil => exact ⟨fun _ => .nil, fun _ => .nil tvs ctors store⟩
      | cons t ts => constructor <;> intro h <;> cases h
  | cons v vs ih =>
      cases ts with
      | nil => constructor <;> intro h <;> cases h
      | cons t ts =>
          constructor
          · intro h
            cases h with
            | cons _ _ _ _ _ _ _ head tail => exact .cons head ((ih ts).mp tail)
          · intro h
            cases h with
            | cons head tail => exact .cons tvs ctors store v t vs ts head ((ih ts).mpr tail)

/-- The explicit witnesses in the recursive namespace relation are equivalent
    to HOL's two-sided namespace relation. -/
theorem typeVEnv_iff (ctors : CtorTypes) (store : StoreTypes)
    (values : Namespace MlString MlString Value)
    (types : Namespace MlString MlString (Nat × SemanticT)) :
    TypeVEnv ctors store values types ↔
      nsAll2 (fun _ v entry => TypeV entry.1 ctors store v entry.2) values types := by
  classical
  constructor
  · intro h
    cases h with
    | related _ _ _ _ forward backward forwardLookup forwardTyped forwardModules backwardLookup backwardTyped backwardModules =>
      refine ⟨⟨?_, forwardModules⟩, ⟨?_, backwardModules⟩⟩
      · intro id v found
        exact ⟨forward id v, forwardLookup id v found, forwardTyped id v found⟩
      · intro id entry found
        exact ⟨backward id entry, backwardLookup id entry found, backwardTyped id entry found⟩
  · rintro ⟨⟨forward, forwardModules⟩, ⟨backward, backwardModules⟩⟩
    let f : Ident MlString MlString → Value → Nat × SemanticT := fun id v =>
      if h : nsLookup values id = some v then Classical.choose (forward id v h) else (0, Tint)
    let b : Ident MlString MlString → (Nat × SemanticT) → Value := fun id entry =>
      if h : nsLookup types id = some entry then Classical.choose (backward id entry h) else .conv none []
    refine .related ctors store values types f b ?_ ?_ forwardModules ?_ ?_ backwardModules
    · intro id v found
      simpa [f, found] using (Classical.choose_spec (forward id v found)).1
    · intro id v found
      simpa [f, found] using (Classical.choose_spec (forward id v found)).2
    · intro id entry found
      simpa [b, found] using (Classical.choose_spec (backward id entry found)).1
    · intro id entry found
      simpa [b, found] using (Classical.choose_spec (backward id entry found)).2

/-- The source's store-value typing clauses. This remains untagged while the
    recursive value-typing relation and its representation are reviewed. -/
def typeSv (ctors : CtorTypes) (store : StoreTypes) : StoreValue Value → StoreT → Prop
  | .refv value, .refT t => TypeV 0 ctors store value t
  | .w8array _, .w8arrayT => True
  | .varray values, .varrayT t => ∀ value ∈ values, TypeV 0 ctors store value t
  | _, _ => False

/-- A store and its type map have the same domain and agree at every entry. -/
def typeS (ctors : CtorTypes) (values : Store Value) (types : StoreTypes) : Prop :=
  ∀ loc,
    ((∃ t, types.lookup loc = some t) ↔ ∃ v, storeLookup loc values = some v) ∧
    ∀ t v, types.lookup loc = some t ∧ storeLookup loc values = some v → typeSv ctors types v t

/-- Constructor and value namespaces agree with the declarative environment. -/
noncomputable def typeAllEnv (ctors : CtorTypes) (store : StoreTypes)
    (env : SemEnv Value) (tenv : TypeEnv) : Prop :=
  nsAll2 (typeCtor ctors) env.c tenv.c ∧
    nsAll2 (fun _ v entry => TypeV entry.1 ctors store v entry.2) env.v tenv.v

/-- Complete source type-soundness invariant, using the source-shaped value
    relation above. This is untagged until that relation's finite-map and
    recursive premise representations have been reviewed. -/
noncomputable def typeSoundInvariant {σ : Type} (st : State σ) (env : SemEnv Value)
    (ctors : CtorTypes) (store : StoreTypes) (typeIds : TypeIds) (tenv : TypeEnv) : Prop :=
  tenvOk tenv ∧ goodCtMap ctors ∧ consistentCtMap st typeIds ctors ∧
    typeAllEnv ctors store env tenv ∧ typeS ctors st.refs store

end Flapjack.TypeSoundInvariants
