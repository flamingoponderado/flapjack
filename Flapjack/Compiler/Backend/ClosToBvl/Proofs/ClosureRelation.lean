import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InstalledCode
import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Misc.ListEl

/-! Closure representations for the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.ClosProps

private instance : Nonempty BvlSem.Value := ⟨.number 0⟩

private def toBroad (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) := refs.lookup
private def ofBroad (lookup : Nat → Option (BvlSem.Ref BvlSem.Value))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value) := ⟨lookup, support⟩

/-- The canonical reference-map lookup and finite-support codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_clRel_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- The three closure layouts used by the source value simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel"
  (fmap_as_finite_support_parameters := [refs])]
inductive clRel (maxApp : Nat) (fs : Nat → Prop)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (code : Spt (Nat × Bvl.Exp)) :
    (List ClosSem.Value × List BvlSem.Value) → ClosSem.Value → BvlSem.Value → Prop where
  | closure {n x aux c aux1 p env ys} :
      n ≤ maxApp → n ≠ 0 → everyFnLocationSome [x] → everyFnVarsSome [x] →
      compileExpsHOL maxApp [x] aux = ([c], aux1) → codeInstalled aux1 code →
      sptLookup (p + numStubs maxApp) code =
        some (n + 1, .let ((List.range n).map Bvl.Exp.var ++ freeLet (.var n) env.length) c) →
      clRel maxApp fs refs code (env, ys) (.closure (some p) [] env n x)
        (.block 30 (.codePtr (p + numStubs maxApp) :: .number (Int.ofNat (n - 1)) :: ys))
  | singletonRec {n x aux c aux1 p env ys} :
      n ≤ maxApp → n ≠ 0 → everyFnLocationSome [x] → everyFnVarsSome [x] →
      compileExpsHOL maxApp [x] aux = ([c], aux1) → codeInstalled aux1 code →
      sptLookup (p + numStubs maxApp) code =
        some (n + 1, .let ((List.range (n + 1)).map Bvl.Exp.var ++ freeLet (.var n) env.length) c) →
      clRel maxApp fs refs code (env, ys) (.recclosure (some p) [] env [(n, x)] 0)
        (.block 30 (.codePtr (p + numStubs maxApp) :: .number (Int.ofNat (n - 1)) :: ys))
  | mutualRec {exps expsPs ps rs loc r env ys k} :
      exps = expsPs.map Prod.fst → ps = expsPs.map Prod.snd →
      ps = (List.range expsPs.length).map (fun n => loc + numStubs maxApp + 2 * n) →
      rs = expsPs.map (fun ((n, _), p) =>
        .block 30 [.codePtr p, .number (Int.ofNat (n - 1)), .refPtr true r]) →
      ¬ fs r → refs.lookup r = some (.valueArray (rs ++ ys)) →
      1 < exps.length → k < exps.length →
      everyFnLocationSome (exps.map Prod.snd) → everyFnVarsSome (exps.map Prod.snd) →
      closureCodeInstalled maxApp code expsPs env →
      clRel maxApp fs refs code (env, ys) (.recclosure (some loc) [] env exps k) (holEl k rs)

theorem holFmapAsFiniteSupportParamWitness_clRel_subspt_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_clRel_refs refs key

/-- Extending the code tree preserves each closure layout. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_subspt"
  (fmap_as_finite_support_parameters := [refs])]
theorem clRel_subspt {maxApp : Nat} {fs : Nat → Prop}
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    {code1 code2 : Spt (Nat × Bvl.Exp)} {env cl target}
    (related : clRel maxApp fs refs code1 env cl target) (sub : sptSubspt code1 code2) :
    clRel maxApp fs refs code2 env cl target := by
  cases related with
  | closure bound positive loc vars compiled installed lookup =>
      have mem := (sptMem_iff_lookup _ _).2 ⟨_, lookup⟩
      exact .closure bound positive loc vars compiled (codeInstalled_subspt installed sub)
        ((sub _ mem).2.trans lookup)
  | singletonRec bound positive loc vars compiled installed lookup =>
      have mem := (sptMem_iff_lookup _ _).2 ⟨_, lookup⟩
      exact .singletonRec bound positive loc vars compiled (codeInstalled_subspt installed sub)
        ((sub _ mem).2.trans lookup)
  | mutualRec exps ps positions values fresh stored length index loc vars installed =>
      exact .mutualRec exps ps positions values fresh stored length index loc vars
        (closureCodeInstalled_subspt installed sub)

end Flapjack.Compiler.Backend.ClosToBvl
