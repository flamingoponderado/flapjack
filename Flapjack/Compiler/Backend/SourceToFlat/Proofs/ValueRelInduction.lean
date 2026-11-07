import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel

/-! Source-shaped induction for the mutually recursive source-to-flat
relations. This is Flapjack infrastructure derived from their mutual recursor. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendCommon

/-- Premises for induction through the source value, local-environment, and
global-environment relations. Recursive list and lookup premises require the
induction predicate, as in the source induction principle. -/
structure ValueRelInductionSteps (g : GlobalEnv)
    (P : Value → FlatSem.Value → Prop)
    (Q : Namespace ModN VarN Value → List (VarN × FlatSem.Value) → Prop)
    (R : Environment → (VarN → Prop) → SemEnv Value → Prop) : Prop where
  literal : ∀ lit, P (.litv lit) (.litv lit)
  constructor : ∀ stamp ctor xs ys,
    List.Forall₂ P xs ys →
    g.c.lookup (ctor, xs.length) = some stamp → P (.conv (some stamp) xs) (.conv (some ctor) ys)
  tuple : ∀ xs ys, List.Forall₂ P xs ys →
    P (.conv none xs) (.conv none ys)
  closure : ∀ comp env locals name body flat t ts,
    Q locals flat.v →
    R comp (fun n => n ∈ flat.v.map Prod.fst) env → ts.length = flat.v.length + 1 →
    P (.closure { env with v := nsAppend locals env.v } name body)
      (.closure flat name (compileExp t { comp with v := bindLocals ts (name :: flat.v.map Prod.fst) comp.v } body))
  recclosure : ∀ comp env locals funs name flat t ts,
    Q locals flat.v →
    R comp (fun n => n ∈ flat.v.map Prod.fst) env → ts.length = funs.length + flat.v.length →
    P (.recclosure { env with v := nsAppend locals env.v } funs name)
      (.recclosure flat (compileFuns t { comp with v := bindLocals ts (funs.map Prod.fst ++ flat.v.map Prod.fst) comp.v } funs) name)
  topRecclosure : ∀ comp env funs flat name arg body newVars t1 t2,
    newVars.map Prod.fst = funs.reverse.map Prod.fst →
    R comp (fun _ => False) env →
    flat.v = [] → findRecFun name funs = some (arg, body) →
    (∀ x, x ∈ funs.map Prod.fst → ∃ n y e trace t trace',
      newVars.lookup x = some (.glob trace n) ∧ n < g.v.length ∧
      findRecFun x funs = some (y, e) ∧
      g.v[n]?.getD none = some (.closure flat y
        (compileExp t { comp with v := nsBindList ((y, .localName trace' y) :: newVars) comp.v } e))) →
    P (.recclosure env funs name)
      (.closure flat arg (compileExp t1 { comp with v := nsBindList ((arg, .localName t2 arg) :: newVars) comp.v } body))
  location : ∀ loc b, P (.loc b loc) (.loc b (loc + 1))
  vector : ∀ xs ys, List.Forall₂ P xs ys →
    P (.vectorv xs) (.vectorv ys)
  empty : Q nsEmpty []
  bind : ∀ name source env flatEnv flat, Q env flatEnv →
    P source flat → Q (nsBind name source env) ((name, flat) :: flatEnv)
  global : ∀ comp shadowers env,
    (∀ id v, ¬(∃ name, shadowers name ∧ id = Ident.short name) → nsLookup env.v id = some v →
      ∃ n flat t, nsLookup comp.v id = some (.glob t n) ∧ n < g.v.length ∧
        g.v[n]?.getD none = some flat ∧ P v flat) →
    (∀ id arity stamp, nsLookup env.c id = some (arity, stamp) →
      ∃ cn group, nsLookup comp.c id = some (cn, group) ∧
        g.c.lookup ((cn, group.map Prod.fst), arity) = some stamp ∧
        ∀ tyId ctors, group = some (tyId, ctors) → g.tys.lookup tyId = some ctors) →
    R comp shadowers env

/-- The factored relations satisfy the induction rules used by the source
proof, including pointwise hypotheses inside lists and global lookups. -/
theorem valueRel_source_induction (g : GlobalEnv)
    (P : Value → FlatSem.Value → Prop)
    (Q : Namespace ModN VarN Value → List (VarN × FlatSem.Value) → Prop)
    (R : Environment → (VarN → Prop) → SemEnv Value → Prop)
    (steps : ValueRelInductionSteps g P Q R) :
    (∀ x y, ValueRel g x y → P x y) ∧
    (∀ x y, EnvRel g x y → Q x y) ∧
    (∀ c sh e, GlobalEnvInv g c sh e → R c sh e) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intros
    first
    | refine ValueRel.rec
          (motive_1 := fun x y _ => P x y)
          (motive_2 := fun xs ys _ => List.Forall₂ P xs ys)
          (motive_3 := fun x y _ => Q x y)
          (motive_4 := fun c sh e _ => R c sh e)
          (motive_5 := fun c id v _ => ∃ n flat t, nsLookup c.v id = some (.glob t n) ∧
            n < g.v.length ∧ g.v[n]?.getD none = some flat ∧ P v flat)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹ValueRel g _ _›
    | refine EnvRel.rec
          (motive_1 := fun x y _ => P x y)
          (motive_2 := fun xs ys _ => List.Forall₂ P xs ys)
          (motive_3 := fun x y _ => Q x y)
          (motive_4 := fun c sh e _ => R c sh e)
          (motive_5 := fun c id v _ => ∃ n flat t, nsLookup c.v id = some (.glob t n) ∧
            n < g.v.length ∧ g.v[n]?.getD none = some flat ∧ P v flat)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹EnvRel g _ _›
    | refine GlobalEnvInv.rec
          (motive_1 := fun x y _ => P x y)
          (motive_2 := fun xs ys _ => List.Forall₂ P xs ys)
          (motive_3 := fun x y _ => Q x y)
          (motive_4 := fun c sh e _ => R c sh e)
          (motive_5 := fun c id v _ => ∃ n flat t, nsLookup c.v id = some (.glob t n) ∧
            n < g.v.length ∧ g.v[n]?.getD none = some flat ∧ P v flat)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹GlobalEnvInv g _ _ _›
  all_goals
    first
    | exact steps.literal
    | exact fun stamp ctor xs ys _ lookup ih => steps.constructor stamp ctor xs ys ih lookup
    | exact fun xs ys _ ih => steps.tuple xs ys ih
    | exact fun comp env locals name body flat t ts _ _ len lih gih =>
        steps.closure comp env locals name body flat t ts lih gih len
    | exact fun comp env locals funs name flat t ts _ _ len lih gih =>
        steps.recclosure comp env locals funs name flat t ts lih gih len
    | exact fun comp env funs flat name arg body vars t1 t2 names _ empty find closures gih =>
        steps.topRecclosure comp env funs flat name arg body vars t1 t2 names gih empty find closures
    | exact steps.location
    | exact fun xs ys _ ih => steps.vector xs ys ih
    | exact .nil
    | exact fun _ _ _ _ _ _ ihHead ihTail => .cons ihHead ihTail
    | exact steps.empty
    | exact fun name source env flatEnv flat _ _ ihEnv ihValue =>
        steps.bind name source env flatEnv flat ihEnv ihValue
    | exact fun comp shadowers env _ constructors ih => steps.global comp shadowers env ih constructors
    | exact fun _ _ _ n flat t lookup bound slot _ ih => ⟨n, flat, t, lookup, bound, slot, ih⟩

/-- The same induction works uniformly for predicates that also depend on the
global environment, matching the quantifier order of the source induction. -/
theorem valueRel_source_induction_all
    (P : GlobalEnv → Value → FlatSem.Value → Prop)
    (Q : GlobalEnv → Namespace ModN VarN Value → List (VarN × FlatSem.Value) → Prop)
    (R : GlobalEnv → Environment → (VarN → Prop) → SemEnv Value → Prop)
    (steps : ∀ g, ValueRelInductionSteps g (P g) (Q g) (R g)) :
    (∀ g x y, ValueRel g x y → P g x y) ∧
    (∀ g x y, EnvRel g x y → Q g x y) ∧
    (∀ g c sh e, GlobalEnvInv g c sh e → R g c sh e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g x y related
    exact (valueRel_source_induction g (P g) (Q g) (R g) (steps g)).1 x y related
  · intro g x y related
    exact (valueRel_source_induction g (P g) (Q g) (R g) (steps g)).2.1 x y related
  · intro g c sh e related
    exact (valueRel_source_induction g (P g) (Q g) (R g) (steps g)).2.2 c sh e related

end Flapjack.Compiler.Backend.SourceToFlat
