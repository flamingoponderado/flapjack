module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel

@[expose] public section

/-! Source-shaped induction for the mutually recursive source-to-flat
relations. This is Flapjack infrastructure derived from their mutual recursor. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendCommon

namespace ValueRelInductionReview

/-- The global environment uses the reviewed finite-map representation. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

end ValueRelInductionReview

/-- The source relation's mutual induction principle, with its original rule
premises. Guarded optional global lookup agrees with HOL EL at every bounded
index in the premises. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_ind"
  (fmap_as_finite_support := [c, tys])]
theorem valueRel_ind
    (P : GlobalEnv → Value → FlatSem.Value → Prop)
    (Q : GlobalEnv → Namespace ModN VarN Value → List (VarN × FlatSem.Value) → Prop)
    (R : GlobalEnv → Environment → (VarN → Prop) → SemEnv Value → Prop)
    (steps :
      (∀ g lit, P g (.litv lit) (.litv lit)) ∧
      (∀ g stamp ctor xs ys, List.Forall₂ (P g) xs ys ∧
        g.c.lookup (ctor, xs.length) = some stamp → P g (.conv (some stamp) xs) (.conv (some ctor) ys)) ∧
      (∀ g xs ys, List.Forall₂ (P g) xs ys → P g (.conv none xs) (.conv none ys)) ∧
      (∀ g comp env locals name body flat t ts,
        Q g locals flat.v ∧ R g comp (fun n => n ∈ flat.v.map Prod.fst) env ∧ ts.length = flat.v.length + 1 →
        P g (.closure { env with v := nsAppend locals env.v } name body)
          (.closure flat name (compileExp t { comp with v := bindLocals ts (name :: flat.v.map Prod.fst) comp.v } body))) ∧
      (∀ g comp env locals funs name flat t ts,
        Q g locals flat.v ∧ R g comp (fun n => n ∈ flat.v.map Prod.fst) env ∧ ts.length = funs.length + flat.v.length →
        P g (.recclosure { env with v := nsAppend locals env.v } funs name)
          (.recclosure flat (compileFuns t { comp with v := bindLocals ts (funs.map Prod.fst ++ flat.v.map Prod.fst) comp.v } funs) name)) ∧
      (∀ g comp env funs flat name arg body newVars t1 t2,
        newVars.map Prod.fst = funs.reverse.map Prod.fst ∧ R g comp (fun _ => False) env ∧
        flat.v = [] ∧ findRecFun name funs = some (arg, body) ∧
        (∀ x, x ∈ funs.map Prod.fst → ∃ n y e trace t trace',
          newVars.lookup x = some (.glob trace n) ∧ n < g.v.length ∧ findRecFun x funs = some (y, e) ∧
          g.v[n]?.getD none = some (.closure flat y
            (compileExp t { comp with v := nsBindList ((y, .localName trace' y) :: newVars) comp.v } e))) →
        P g (.recclosure env funs name)
          (.closure flat arg (compileExp t1 { comp with v := nsBindList ((arg, .localName t2 arg) :: newVars) comp.v } body))) ∧
      (∀ g loc b, P g (.loc b loc) (.loc b (loc + 1))) ∧
      (∀ g xs ys, List.Forall₂ (P g) xs ys → P g (.vectorv xs) (.vectorv ys)) ∧
      (∀ g, Q g nsEmpty []) ∧
      (∀ g name source env flatEnv flat, Q g env flatEnv ∧ P g source flat →
        Q g (nsBind name source env) ((name, flat) :: flatEnv)) ∧
      (∀ g comp shadowers env,
        (∀ id v, ¬(∃ name, shadowers name ∧ id = Ident.short name) ∧ nsLookup env.v id = some v →
          ∃ n flat t, nsLookup comp.v id = some (.glob t n) ∧ n < g.v.length ∧
            g.v[n]?.getD none = some flat ∧ P g v flat) ∧
        (∀ id arity stamp, nsLookup env.c id = some (arity, stamp) →
          ∃ cn group, nsLookup comp.c id = some (cn, group) ∧
            g.c.lookup ((cn, group.map Prod.fst), arity) = some stamp ∧
            ∀ tyId ctors, group = some (tyId, ctors) → g.tys.lookup tyId = some ctors) →
        R g comp shadowers env)) :
    (∀ g x y, ValueRel g x y → P g x y) ∧
    (∀ g x y, EnvRel g x y → Q g x y) ∧
    (∀ g c sh e, GlobalEnvInv g c sh e → R g c sh e) := by
  obtain ⟨literal, constructor, tuple, closure, recclosure, topRecclosure, location, vector, empty, bind, global⟩ := steps
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro g
    intros
    first
    | refine ValueRel.rec
          (motive_1 := fun x y _ => P g x y)
          (motive_2 := fun xs ys _ => List.Forall₂ (P g) xs ys)
          (motive_3 := fun x y _ => Q g x y)
          (motive_4 := fun c sh e _ => R g c sh e)
          (motive_5 := fun c id v _ => ∃ n flat t, nsLookup c.v id = some (.glob t n) ∧
            n < g.v.length ∧ g.v[n]?.getD none = some flat ∧ P g v flat)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹ValueRel g _ _›
    | refine EnvRel.rec
          (motive_1 := fun x y _ => P g x y)
          (motive_2 := fun xs ys _ => List.Forall₂ (P g) xs ys)
          (motive_3 := fun x y _ => Q g x y)
          (motive_4 := fun c sh e _ => R g c sh e)
          (motive_5 := fun c id v _ => ∃ n flat t, nsLookup c.v id = some (.glob t n) ∧
            n < g.v.length ∧ g.v[n]?.getD none = some flat ∧ P g v flat)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹EnvRel g _ _›
    | refine GlobalEnvInv.rec
          (motive_1 := fun x y _ => P g x y)
          (motive_2 := fun xs ys _ => List.Forall₂ (P g) xs ys)
          (motive_3 := fun x y _ => Q g x y)
          (motive_4 := fun c sh e _ => R g c sh e)
          (motive_5 := fun c id v _ => ∃ n flat t, nsLookup c.v id = some (.glob t n) ∧
            n < g.v.length ∧ g.v[n]?.getD none = some flat ∧ P g v flat)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹GlobalEnvInv g _ _ _›
  all_goals
    first
    | exact literal g
    | exact fun stamp ctor xs ys _ lookup ih => constructor g stamp ctor xs ys ⟨ih, lookup⟩
    | exact fun xs ys _ ih => tuple g xs ys ih
    | exact fun comp env locals name body flat t ts _ _ len lih gih =>
        closure g comp env locals name body flat t ts ⟨lih, gih, len⟩
    | exact fun comp env locals funs name flat t ts _ _ len lih gih =>
        recclosure g comp env locals funs name flat t ts ⟨lih, gih, len⟩
    | exact fun comp env funs flat name arg body vars t1 t2 names _ empty find closures gih =>
        topRecclosure g comp env funs flat name arg body vars t1 t2 ⟨names, gih, empty, find, closures⟩
    | exact location g
    | exact fun xs ys _ ih => vector g xs ys ih
    | exact .nil
    | exact fun _ _ _ _ _ _ ihHead ihTail => .cons ihHead ihTail
    | exact empty g
    | exact fun name source env flatEnv flat _ _ ihEnv ihValue =>
        bind g name source env flatEnv flat ⟨ihEnv, ihValue⟩
    | exact fun comp shadowers env _ constructors ih => global g comp shadowers env ⟨(fun id v pair => ih id v pair.1 pair.2), constructors⟩
    | exact fun _ _ _ n flat t lookup bound slot _ ih => ⟨n, flat, t, lookup, bound, slot, ih⟩

end Flapjack.Compiler.Backend.SourceToFlat
