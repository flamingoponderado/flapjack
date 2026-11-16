module

public import Flapjack.Compiler.Inference.EnvRel.Approx
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.TypeSoundInvariants

@[expose] public section

/-! Source-shaped inference/declarative environment relations. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferProps
  Flapjack.TypeSoundInvariants

/-- Source-shaped soundness relation. Untagged because scheme approximation
    uses a normalizer whose off-well-formedness choice is not source-reviewed. -/
noncomputable def envRelSoundModel (s : HolFiniteMapExact Nat InferT)
    (ienv : Env) (tenv : TypeEnv) (tenvE : TenvValExp) : Prop :=
  ienv.infT = tenv.t ∧ ienv.infC = tenv.c ∧
    ∀ x ts, nsLookup ienv.infV x = some ts →
      ∃ tvs t, checkFreevars (tvs + numTvs tenvE) [] t = true ∧
        lookupVar x tenvE tenv = some (tvs, t) ∧
        tschemeApproxModel (numTvs tenvE) s ts (tvs, unconvertT t)

/-- Source-shaped completeness relation, with the same normalizer boundary. -/
noncomputable def envRelCompleteModel (s : HolFiniteMapExact Nat InferT)
    (ienv : Env) (tenv : TypeEnv) (tenvE : TenvValExp) : Prop :=
  ienv.infT = tenv.t ∧ ienv.infC = tenv.c ∧
    ∀ x tvs t, lookupVar x tenvE tenv = some (tvs, t) →
      (∃ n, checkFreevars n [] t = true) ∧
      ∃ tvs2 t2, nsLookup ienv.infV x = some (tvs2, t2) ∧
        tschemeApproxModel (numTvs tenvE) s (tvs, unconvertT t) (tvs2, t2)

/-- Source-shaped top-level environment relation. The two general relations
    above remain untagged pending source review of the normalizer boundary. -/
noncomputable def envRelModel (tenv : TypeEnv) (ienv : Env) : Prop :=
  ienvOk (fun _ => False) ienv ∧ tenvOk tenv ∧
    (∀ x, nsLookupMod ienv.infV x = none ↔ nsLookupMod tenv.v x = none) ∧
    envRelSoundModel HolFiniteMapExact.holEmpty ienv tenv .empty ∧
    envRelCompleteModel HolFiniteMapExact.holEmpty ienv tenv .empty

end Flapjack.Compiler.Inference.EnvRel
