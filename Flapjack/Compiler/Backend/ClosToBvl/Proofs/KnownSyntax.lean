import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownAddresses
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownOracleFacts
import Flapjack.Compiler.Backend.ClosLetop.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosTicks.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosFvs.Proofs.CodeLocations

/-! Syntax preservation for the whole known-closure pass. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps BackendProps ClosKnown

/-- The known-closure optimizer preserves direct-call syntax. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "kcompile_csyntax_ok"]
theorem kcompile_csyntaxOk (kc x : Option ClosKnown.Config) (es y : List ClosLang.Exp)
    (compiled : ClosKnown.compileSource kc es = (x, y))
    (ok : ClosCall.syntaxOk es) : ClosCall.syntaxOk y := by
  cases kc with
  | none =>
    simp [ClosKnown.compileSource] at compiled
    rcases compiled with ⟨_, rfl⟩
    exact ok
  | some c =>
    rw [ClosKnown.compileSource_eq_compile] at compiled
    cases run : knownListTotal c (ClosFvs.compile es) [] .ln with
    | mk eas next =>
      simp [ClosKnown.compile, run] at compiled
      obtain ⟨_, rfl⟩ := compiled
      have inputVars : everyFnVarsNone (ClosFvs.compile es) := by
        simpa [ClosFvs.compile] using (ClosFvs.removeList_varsNone es 0).mpr ok.2.1
      have inputLoc : everyFnLocationSome (ClosFvs.compile es) := by
        simpa [ClosFvs.compile] using (ClosFvs.removeList_locations es 0).mpr ok.1
      have vars := TraversalSyntax.knownEveryFnVarsNone c (ClosFvs.compile es) [] .ln
        ⟨inputVars, by simp, by simp [globalsApproxVarsNone, sptLookup]⟩
      have locs := TraversalLocations.knownEveryFnLocations c (ClosFvs.compile es) [] .ln
        ⟨inputLoc, by simp, by simp [globalsApproxLocations, sptLookup]⟩
      rw [run] at vars locs
      have bag := TraversalCodeBag.knownCodeLocationsBag c (ClosFvs.compile es) [] .ln eas next run
      have sub : List.Subperm (codeLocations (eas.map Prod.fst)) (codeLocations es) := by
        apply List.subperm_iff_count.mpr
        intro k
        simpa [ClosFvs.compile, ClosFvs.removeList_codeLocations] using bag k
      refine ⟨?_, ?_, ?_⟩
      · simpa [ClosLetop.compileList_locations, ClosTicks.removeList_locations] using locs.1
      · simpa [ClosLetop.compileList_varsNone, ClosTicks.removeList_varsNone] using vars.1
      · obtain ⟨mid, perm, smaller⟩ := List.subperm_iff.mp sub
        have noDup := smaller.nodup (perm.nodup_iff.mpr ok.2.2)
        simpa [ClosLetop.compileList_codeLocations, ClosTicks.removeList_codeLocations] using noDup

end Flapjack.Compiler.Backend.ClosToBvl
