module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases

@[expose] public section

/-! Source-shaped cases for the mutual source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Compiler.Backend.BackendCommon

namespace ValueRelSourceCasesReview

/-- The global environment uses the reviewed finite-map representation. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

end ValueRelSourceCasesReview

/-- The original mutual relation's case decomposition. Each list lookup is
bounded in the same conjunct, so guarded optional lookup agrees with HOL EL. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_cases"
  (fmap_as_finite_support := [c, tys])]
theorem valueRel_source_cases :
    (∀ (g : GlobalEnv) (source : Value) (flat : FlatSem.Value), ValueRel g source flat ↔
      (∃ lit, source = .litv lit ∧ flat = .litv lit) ∨
      (∃ stamp ctor xs ys, source = .conv (some stamp) xs ∧ flat = .conv (some ctor) ys ∧
        List.Forall₂ (ValueRel g) xs ys ∧ g.c.lookup (ctor, xs.length) = some stamp) ∨
      (∃ xs ys, source = .conv none xs ∧ flat = .conv none ys ∧ List.Forall₂ (ValueRel g) xs ys) ∨
      (∃ comp env locals name body flatLocal t ts,
        source = .closure { env with v := nsAppend locals env.v } name body ∧
        flat = .closure flatLocal name
          (compileExp t { comp with v := bindLocals ts (name :: flatLocal.v.map Prod.fst) comp.v } body) ∧
        EnvRel g locals flatLocal.v ∧
        GlobalEnvInv g comp (fun n => n ∈ flatLocal.v.map Prod.fst) env ∧
        ts.length = flatLocal.v.length + 1) ∨
      (∃ comp env locals funs name flatLocal t ts,
        source = .recclosure { env with v := nsAppend locals env.v } funs name ∧
        flat = .recclosure flatLocal
          (compileFuns t { comp with v := bindLocals ts (funs.map Prod.fst ++ flatLocal.v.map Prod.fst) comp.v } funs) name ∧
        EnvRel g locals flatLocal.v ∧
        GlobalEnvInv g comp (fun n => n ∈ flatLocal.v.map Prod.fst) env ∧
        ts.length = funs.length + flatLocal.v.length) ∨
      (∃ comp env funs flatEnv name arg body newVars t1 t2,
        source = .recclosure env funs name ∧
        flat = .closure flatEnv arg
          (compileExp t1 { comp with v := nsBindList ((arg, .localName t2 arg) :: newVars) comp.v } body) ∧
        newVars.map Prod.fst = funs.reverse.map Prod.fst ∧
        GlobalEnvInv g comp (fun _ => False) env ∧ flatEnv.v = [] ∧
        findRecFun name funs = some (arg, body) ∧
        ∀ x, x ∈ funs.map Prod.fst → ∃ n y e trace t trace',
          newVars.lookup x = some (.glob trace n) ∧ n < g.v.length ∧
          findRecFun x funs = some (y, e) ∧
          g.v[n]?.getD none = some (.closure flatEnv y
            (compileExp t { comp with v := nsBindList ((y, .localName trace' y) :: newVars) comp.v } e))) ∨
      (∃ loc b, source = .loc b loc ∧ flat = .loc b (loc + 1)) ∨
      (∃ xs ys, source = .vectorv xs ∧ flat = .vectorv ys ∧ List.Forall₂ (ValueRel g) xs ys)) ∧
    (∀ (g : GlobalEnv) source flat, EnvRel g source flat ↔
      (source = nsEmpty ∧ flat = []) ∨
      ∃ name value env flatEnv flatValue, source = nsBind name value env ∧
        flat = (name, flatValue) :: flatEnv ∧ EnvRel g env flatEnv ∧ ValueRel g value flatValue) ∧
    (∀ (g : GlobalEnv) comp shadowers env, GlobalEnvInv g comp shadowers env ↔
      (∀ id v, ¬(∃ name, shadowers name ∧ id = Ident.short name) ∧
        nsLookup env.v id = some v → ∃ n v' t,
          nsLookup comp.v id = some (.glob t n) ∧ n < g.v.length ∧
          g.v[n]?.getD none = some v' ∧ ValueRel g v v') ∧
      (∀ id arity stamp, nsLookup env.c id = some (arity, stamp) →
        ∃ cn group, nsLookup comp.c id = some (cn, group) ∧
          g.c.lookup ((cn, group.map Prod.fst), arity) = some stamp ∧
          ∀ tyId ctors, group = some (tyId, ctors) → g.tys.lookup tyId = some ctors)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g source flat
    constructor
    · intro related
      cases related with
      | literal lit => exact .inl ⟨lit, rfl, rfl⟩
      | constructor stamp ctor xs ys related lookup =>
        exact .inr (.inl ⟨stamp, ctor, xs, ys, rfl, rfl, (valueListRel_iff g xs ys).mp related, lookup⟩)
      | tuple xs ys related =>
        exact .inr (.inr (.inl ⟨xs, ys, rfl, rfl, (valueListRel_iff g xs ys).mp related⟩))
      | closure comp env locals name body flat t ts lr gr len =>
        exact .inr (.inr (.inr (.inl ⟨comp, env, locals, name, body, flat, t, ts, rfl, rfl, lr, gr, len⟩)))
      | recclosure comp env locals funs name flat t ts lr gr len =>
        exact .inr (.inr (.inr (.inr (.inl ⟨comp, env, locals, funs, name, flat, t, ts, rfl, rfl, lr, gr, len⟩))))
      | topRecclosure comp env funs flat name arg body vars t1 t2 names gr empty find closures =>
        exact .inr (.inr (.inr (.inr (.inr (.inl
          ⟨comp, env, funs, flat, name, arg, body, vars, t1, t2, rfl, rfl, names, gr, empty, find, closures⟩)))))
      | location loc b => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨loc, b, rfl, rfl⟩))))))
      | vector xs ys related => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr
          ⟨xs, ys, rfl, rfl, (valueListRel_iff g xs ys).mp related⟩))))))
    · rintro (⟨lit, rfl, rfl⟩ | ⟨stamp, ctor, xs, ys, rfl, rfl, related, lookup⟩ |
        ⟨xs, ys, rfl, rfl, related⟩ | ⟨comp, env, locals, name, body, flat, t, ts, rfl, rfl, lr, gr, len⟩ |
        ⟨comp, env, locals, funs, name, flat, t, ts, rfl, rfl, lr, gr, len⟩ |
        ⟨comp, env, funs, flat, name, arg, body, vars, t1, t2, rfl, rfl, names, gr, empty, find, closures⟩ |
        ⟨loc, b, rfl, rfl⟩ | ⟨xs, ys, rfl, rfl, related⟩)
      · exact .literal g lit
      · exact valueRel_constructor g stamp ctor xs ys related lookup
      · exact valueRel_tuple g xs ys related
      · exact .closure g comp env locals name body flat t ts lr gr len
      · exact .recclosure g comp env locals funs name flat t ts lr gr len
      · exact .topRecclosure g comp env funs flat name arg body vars t1 t2 names gr empty find closures
      · exact .location g loc b
      · exact valueRel_vector g xs ys related
  · intro g source flat
    constructor
    · intro related
      cases related with
      | empty => exact .inl ⟨rfl, rfl⟩
      | bind name value env flatEnv flatValue lr vr =>
        exact .inr ⟨name, value, env, flatEnv, flatValue, rfl, rfl, lr, vr⟩
    · rintro (⟨rfl, rfl⟩ | ⟨name, value, env, flatEnv, flatValue, rfl, rfl, lr, vr⟩)
      · exact .empty g
      · exact .bind g name value env flatEnv flatValue lr vr
  · simpa only [and_imp] using globalEnvInv_iff

end Flapjack.Compiler.Backend.SourceToFlat
