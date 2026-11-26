module

public import Flapjack.TypeSystemHOL.Expressions
public import Flapjack.SemanticPrimitivesHOL
public import Batteries.Data.List.Basic

@[expose] public section

/-! Source typing preserves the shape of function and expression lists. -/
namespace Flapjack.TypeSysProps
open Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL Flapjack.AstHOL
open Flapjack.SemanticPrimitivesHOL

/-- The names in a typed function list equal those in its output bindings. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_funs_MAP_FST"]
theorem typeFunsMapFst (funs : List (MlString × MlString × Flapjack.AstHOL.Exp)) (env : TypeEnv)
    (localEnv : TenvValExp) (bindings : List (MlString × SemanticT)) :
    TypeFuns env localEnv funs bindings → funs.map Prod.fst = bindings.map Prod.fst := by
  induction funs generalizing env localEnv bindings with
  | nil =>
    intro typed
    cases typed
    rfl
  | cons fn funs ih =>
    intro typed
    cases typed <;> simp_all <;> apply ih <;> assumption

/-- Original `type_funs_Tfn`: a binding produced by a typed function list is a
function type whose free variables are checked in the local environment. The
capture shows a vacuous auto-bound `tvs : α` in HOL's binder list; it does not
occur in the statement and is omitted. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_funs_Tfn"]
theorem typeFunsTfn (env : TypeEnv) (localEnv : TenvValExp)
    (funs : List (MlString × MlString × Flapjack.AstHOL.Exp))
    (bindings : List (MlString × SemanticT)) (t : SemanticT) (n : MlString)
    (premise : TypeFuns env localEnv funs bindings ∧ bindings.lookup n = some t) :
    ∃ t₁ t₂ : SemanticT, t = .app [t₁, t₂] 4 ∧
      checkFreevars (numTvs localEnv) [] (.app [t₁, t₂] 4) = true := by
  obtain ⟨typed, found⟩ := premise
  induction funs generalizing env localEnv bindings with
  | nil =>
    cases typed
    simp at found
  | cons fn funs ih =>
    cases typed
    rename_i name arg body bindings' t₁ t₂ unique free typedBody tail
    rw [List.lookup_cons] at found
    cases h : (n == name) with
    | true =>
      simp only [h] at found
      exact ⟨t₁, t₂, (Option.some.inj found).symm, free⟩
    | false =>
      simp only [h] at found
      exact ih env localEnv bindings' tail found

/-- Original `type_funs_lookup`: every function listed in a typed function list
has a binding in its output environment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_funs_lookup"]
theorem typeFunsLookup (fn : MlString) (localEnv : TenvValExp)
    (funs : List (MlString × MlString × Flapjack.AstHOL.Exp))
    (bindings : List (MlString × SemanticT)) (n : MlString) (e : Flapjack.AstHOL.Exp)
    (env : TypeEnv)
    (premise : (fn, n, e) ∈ funs ∧ TypeFuns env localEnv funs bindings) :
    ∃ t : SemanticT, bindings.lookup fn = some t := by
  obtain ⟨mem, typed⟩ := premise
  induction funs generalizing env localEnv bindings with
  | nil => simp at mem
  | cons fn' funs ih =>
    cases typed
    rename_i name arg body bindings' t₁ t₂ unique free typedBody tail
    rw [List.mem_cons] at mem
    rcases mem with head | mem
    · have parts := head
      simp only [Prod.mk.injEq] at parts
      obtain ⟨sameName, _, _⟩ := parts
      subst sameName
      exact ⟨.app [t₁, t₂] 4, List.lookup_cons_self⟩
    · obtain ⟨t, found⟩ := ih localEnv bindings' env mem tail
      have different : (fn == name) = false := by
        cases same : (fn == name) with
        | true =>
          have equal : fn = name := by simpa using same
          rw [equal, unique] at found
          simp at found
        | false => rfl
      rw [List.lookup_cons]
      simp only [different]
      exact ⟨t, found⟩

/-- Original `type_funs_find_recfun`: a function with a binding in a typed
function list's output environment is found by `find_recfun`. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_funs_find_recfun"]
theorem typeFunsFindRecfun (fn : MlString)
    (funs : List (MlString × MlString × AstHOL.Exp))
    (bindings : List (MlString × SemanticT)) (env : TypeEnv) (localEnv : TenvValExp)
    (t : SemanticT)
    (premise : bindings.lookup fn = some t ∧ TypeFuns env localEnv funs bindings) :
    ∃ n e, findRecFun fn funs = some (n, e) := by
  obtain ⟨found, typed⟩ := premise
  induction funs generalizing env localEnv bindings with
  | nil =>
    cases typed
    simp at found
  | cons fn' funs ih =>
    cases typed
    rename_i name arg body bindings' t₁ t₂ unique free typedBody tail
    rw [List.lookup_cons] at found
    cases h : (fn == name) with
    | true =>
      have equal : fn = name := by simpa using h
      subst equal
      exact ⟨arg, body, by simp [findRecFun]⟩
    | false =>
      simp only [h] at found
      obtain ⟨n, e, recfun⟩ := ih bindings' env localEnv found tail
      refine ⟨n, e, ?_⟩
      have different : fn ≠ name := by
        intro same
        rw [same] at h
        simp at h
      simp only [findRecFun, if_neg (Ne.symm different)]
      exact recfun

/-- Original `type_recfun_lookup`: a recursive function found in a typed
function list types its body at the function type bound for its name. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_recfun_lookup"]
theorem typeRecfunLookup (fn : MlString) (funs : List (MlString × MlString × AstHOL.Exp))
    (n : MlString) (e : AstHOL.Exp) (env : TypeEnv) (localEnv : TenvValExp)
    (bindings : List (MlString × SemanticT)) (t₁ t₂ : SemanticT)
    (premise : findRecFun fn funs = some (n, e) ∧ TypeFuns env localEnv funs bindings ∧
      bindings.lookup fn = some (.app [t₁, t₂] 4)) :
    TypeE env (.bindName n 0 t₁ localEnv) e t₂ ∧
      checkFreevars (numTvs localEnv) [] (.app [t₁, t₂] 4) = true := by
  obtain ⟨recfun, typed, found⟩ := premise
  induction funs generalizing env localEnv bindings with
  | nil => simp [findRecFun] at recfun
  | cons fn' funs ih =>
    cases typed
    rename_i name arg body bindings' u₁ u₂ unique free typedBody tail
    simp only [findRecFun] at recfun
    cases eq : (fn == name) with
    | true =>
      have h : name = fn := (beq_iff_eq.mp eq).symm
      rw [if_pos h] at recfun
      have pairEq : (arg, body) = (n, e) := Option.some.inj recfun
      have sameN : arg = n := congrArg Prod.fst pairEq
      have sameE : body = e := congrArg Prod.snd pairEq
      rw [sameN, sameE] at typedBody
      rw [List.lookup_cons] at found
      simp only [eq] at found
      have shapes : ([u₁, u₂] : List SemanticT) = [t₁, t₂] := by
        simpa using Option.some.inj found
      rw [List.cons.injEq] at shapes
      obtain ⟨u1eq, shapes⟩ := shapes
      rw [List.cons.injEq] at shapes
      obtain ⟨u2eq, _⟩ := shapes
      rw [u1eq, u2eq] at typedBody free
      exact ⟨typedBody, free⟩
    | false =>
      have h : ¬ (name = fn) := by
        intro same
        rw [same] at eq
        simp at eq
      rw [if_neg h] at recfun
      rw [List.lookup_cons] at found
      simp only [eq] at found
      obtain ⟨typedE, checked⟩ := ih env localEnv bindings' recfun tail found
      exact ⟨typedE, checked⟩

/-- A typed expression list and its type list have equal lengths. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_es_length"]
theorem typeEsLength (env : TypeEnv) (localEnv : TenvValExp) (es : List Flapjack.AstHOL.Exp)
    (types : List SemanticT) : TypeEs env localEnv es types → es.length = types.length := by
  induction es generalizing env localEnv types with
  | nil => intro typed; cases typed; rfl
  | cons e es ih =>
    intro typed
    cases typed <;> simp_all <;> apply ih <;> assumption

/-- The source `type_pes` definition: every pattern/expression pair in the
list binds distinct names, types its pattern at the first type and its
expression at the second type under the extended local environment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_pes_def"]
def typePes (tvs tvs' : Nat) (env : TypeEnv) (localEnv : TenvValExp)
    (pes : List (Pat × Flapjack.AstHOL.Exp)) (t₁ t₂ : SemanticT) : Prop :=
  ∀ (p : Pat) (e : Flapjack.AstHOL.Exp), (p, e) ∈ pes →
    ∃ bindings : List (MlString × SemanticT),
      (patBindings p).Nodup ∧ TypeP tvs env p t₁ bindings ∧
        TypeE env (bindVarList tvs' bindings localEnv) e t₂

/-- The inductive expression-list judgment is exactly HOL's `LIST_REL` of the
single-expression judgment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_es_list_rel"]
theorem typeEsListRel (es : List Flapjack.AstHOL.Exp) (types : List SemanticT) (env : TypeEnv)
    (localEnv : TenvValExp) :
    TypeEs env localEnv es types ↔ List.Forall₂ (TypeE env localEnv) es types := by
  induction es generalizing types env localEnv with
  | nil =>
    cases types with
    | nil => exact ⟨fun _ => List.Forall₂.nil, fun _ => TypeEs.nil env localEnv⟩
    | cons t ts =>
      refine ⟨?_, ?_⟩
      · intro h
        cases h
      · intro h
        cases h
  | cons e es ih =>
    cases types with
    | nil =>
      refine ⟨?_, ?_⟩
      · intro h
        cases h
      · intro h
        cases h
    | cons t ts =>
      constructor
      · intro h
        cases h
        exact List.Forall₂.cons ‹TypeE env localEnv e t›
          ((ih ts env localEnv).mp ‹TypeEs env localEnv es ts›)
      · intro h
        cases h with
        | cons head tail =>
          exact TypeEs.cons env localEnv e es t ts head ((ih ts env localEnv).mpr tail)

/-- A typed pattern list and its type list have equal lengths. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_ps_length"]
theorem typePsLength (tvs : Nat) (env : TypeEnv) (ps : List Pat) (ts : List SemanticT)
    (bindings : List (MlString × SemanticT)) :
    TypePs tvs env ps ts bindings → ps.length = ts.length := by
  intro typed
  induction ps generalizing ts bindings with
  | nil =>
    cases typed
    rfl
  | cons p ps ih =>
    cases typed
    have length := ih _ _ (by assumption)
    simp only [List.length_cons]
    omega

end Flapjack.TypeSysProps

