module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SyntaxOracle
public import Flapjack.Compiler.Backend.ClosToBvl.Stubs
public import Flapjack.FiniteMap.AlistExact
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BvlOracle
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.OracleDomains
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonLabelBound
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InitialCodeDomain
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownOracleFacts
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallAddresses
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiInvariants
import Flapjack.Compiler.Backend.ClosNumber.Proofs.VarsNone
import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationAddresses
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants.Original
import Flapjack.Misc.Sptree.ToAList
import Mathlib.Tactic

@[expose] public section

/-! Construction of the complete incremental compiler oracle invariant. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps BackendProps
local instance : Nonempty ClosKnown.Config := ⟨ClosKnown.defaultConfig 0⟩

/-- The source syntax and oracle conditions establish the complete incremental
compiler oracle invariant, including freshness and function annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "syntax_oracle_ok_to_oracle_inv"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem syntaxOracleOk_to_oracleInv {CC R α : Type}
    (prog : List (Nat × Nat × ClosLang.Exp)) (c'' : Config)
    (cc : CC → List (Nat × Nat × Bvl.Exp) → R)
    (es : List ClosLang.Exp)
    (co : Nat → (Nat × Spt ClosKnown.ValApprox × NumSet × α) × ClosSem.Program)
    (c c' : Config)
    (h : syntaxOracleOkCommon c c' es co ∧ compileCommon c es = (c', prog)) :
    let co' := pureCo ClosAnnotate.compileIncSource ∘
      stateCo (ClosCall.condCallCompileInc c.doCall)
        (ClosKnown.knownCo c.knownConf
          (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
            (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)))
    compileOracleInv c.maxApp (HolFiniteMapExact.alistToFmap prog)
      (pureCc (compileInc c.maxApp) cc) co'
      (sptFromAList (sptToAList (initCode c.maxApp) ++
        [(numStubs c.maxApp - 2, 2, forceThunkCode),
         (numStubs c.maxApp - 1, 0, initGlobals c.maxApp (c''.start + numStubs c.maxApp))] ++
        compileProgExpsHOL c.maxApp prog)) cc
      (pureCo (compileInc c.maxApp) ∘ co') := by
  let mco := pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co
  let nco := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) mco
  let kco := ClosKnown.knownCo c.knownConf nco
  let aco := stateCo (ClosCall.condCallCompileInc c.doCall) kco
  let qco := pureCo ClosAnnotate.compileIncSource ∘ aco
  let tco := pureCo (compileInc c.maxApp) ∘ qco
  let tcode := sptFromAList (sptToAList (initCode c.maxApp) ++
        [(numStubs c.maxApp - 2, 2, forceThunkCode),
         (numStubs c.maxApp - 1, 0, initGlobals c.maxApp (c''.start + numStubs c.maxApp))] ++
        compileProgExpsHOL c.maxApp prog)
  change compileOracleInv c.maxApp _ _ qco tcode cc tco
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro i cfg ps eq
    have empty : (mco i).2.2 = [] := by
      have he := h.1.1 i
      cases hen : c.doMti <;>
        simp [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc, hen, he]
    have nodup := compileInc_phases_allDistinct mco i c.maxApp c.doCall (kco i).1.1 c.knownConf empty
    have eq' : (tco i).2 = ps := congrArg Prod.snd eq
    change (compileInc c.maxApp (ClosAnnotate.compileIncSource (aco i).2)).map Prod.fst |>.Nodup at nodup
    change (compileInc c.maxApp (ClosAnnotate.compileIncSource (aco i).2)) = ps at eq'
    simpa [eq'] using nodup
  · intro n p
    have resultConfig : (compileSource c es).1 =
        { c' with start := numStubs c'.maxApp - 1 } := by
      simp [compileSource, h.2]
    have syntax' : syntaxOracleOkCommon c (compileSource c es).1 es co := by
      rw [resultConfig]
      exact (syntaxOracleOkCommon_start c c' (fun _ => numStubs c'.maxApp - 1) es co).2 h.1
    have whole : compileSource c es = ((compileSource c es).1, (compileSource c es).2) := by
      cases compileSource c es; rfl
    have ordered := syntaxOracleOk_bvlFst_monotonic c (compileSource c es).1 es co
      (compileSource c es).2 ⟨syntax', whole⟩
    have countEq : (co 0).1.1 = c'.nextLoc := by
      obtain ⟨v, hv⟩ := h.1.2.2.1
      exact congrArg (fun value => value.1) hv
    have bound : ∀ x, sptDomain tcode x → x < (co 0).1.1 + numStubs c.maxApp := by
      intro x hx
      rw [countEq]
      simp only [tcode, sptDomainFromAList, List.map_append, List.map_cons,
        List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      have stubBound : 2 ≤ numStubs c.maxApp := by simp only [numStubs]; omega
      rcases hx with (stub | first | second) | compiled
      · have domain := (sptMemMapFstToAList (initCode c.maxApp) x).1 stub
        have lt := domain_initCode_lt_numStubs c.maxApp x domain
        omega
      · omega
      · omega
      · exact compileCommon_mapFst_compileProg c es c' prog h.2 compiled
    have ordered' : oracleMonotonic
        (fun entry : α × List (Nat × Nat × Bvl.Exp) => {x | x ∈ entry.2.map Prod.fst})
        (· < ·) (sptDomain tcode) tco := by
      apply oracleMonotonic_subset _ _ _ tco _ tco (· < ·) ?_ ordered
      exact ⟨bound, fun _ => Set.Subset.rfl⟩
    exact disjoint_nthCode_monotonic tcode tco (tco n).2 n ⟨ordered', rfl⟩ p
  · intro n cfg es' ps eq
    have knownLocations : everyFnLocationSome (kco n).2.1 ∧
        everyFnLocationSome ((kco n).2.2.map (fun entry => entry.2.2)) := by
      let base := (ClosNumber.renumberList
        (makeEven (c.nextLoc + max 1 (ClosMti.compile c.doMti c.maxApp es).length))
        (ClosMti.compile c.doMti c.maxApp es)).2
      let known := ClosKnown.compile c.knownConf base
      have guard : c.knownConf.isSome →
          isStateOracle (ClosKnown.compileInc (holThe c.knownConf))
            (pureCo (ClosFvs.compileInc (α := List (Nat × Nat × ClosLang.Exp))
              (β := Nat × Nat × ClosLang.Exp)) ∘ nco) ∧
          (nco 0).1.1 = (holThe known.1).valApproxSpt ∧
          everyFnVarsNone base ∧ everyFnLocationSome base ∧
          (∀ k, everyFnVarsNone (nco k).2.1 ∧ everyFnLocationSome (nco k).2.1) := by
        intro enabled
        have sk := h.1.2.2.2.2.1 enabled
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact sk.2.2.2.1
        · have knownEq : known.1 = c'.knownConf := by
            let source := ClosMti.compile c.doMti c.maxApp es
            let aligned := makeEven (c.nextLoc + max 1 source.length)
            cases hr : ClosNumber.renumberList aligned source with
            | mk next numbered =>
              cases hk : ClosKnown.compile c.knownConf numbered with
              | mk knownConf optimized =>
                cases hc : ClosCall.compile c.doCall optimized with
                | mk called state =>
                  obtain ⟨globals, aux⟩ := state
                  have run := h.2
                  change (let (next, expressions) := ClosNumber.renumberList aligned source
                    let (knownConf, expressions) := ClosKnown.compileSource c.knownConf expressions
                    let (expressions, (globals, auxiliary)) := ClosCall.compile c.doCall expressions
                    ({ c with start := c.nextLoc, nextLoc := next, knownConf := knownConf, callState := (globals, auxiliary) },
                      ClosAnnotate.compileSource (chainExps c.nextLoc expressions ++ auxiliary))) = (c', prog) at run
                  simp only [ClosKnown.compileSource_eq_compile, hr, hk, hc, Prod.mk.injEq] at run
                  have cfg := congrArg Config.knownConf run.1
                  simpa [known, base, source, aligned, hr, hk] using cfg
          have knownSome : known.1.isSome := by
            exact (ClosKnown.compile_isSome c.knownConf base known.1 known.2
              (by change known = (known.1, known.2); exact (Prod.eta known).symm)).2 enabled
          obtain ⟨v, hv⟩ := h.1.2.2.1
          have initial := congrArg (fun value => value.2.1) hv
          change (nco 0).1.1 = _
          change (co 0).1.2.1 = _
          rw [initial, ← knownEq]
          cases hk : known.1 with
          | none => simp [hk] at knownSome
          | some cfg => simp [ClosKnown.optionValApproxSpt, holThe]
        · have before : everyFnVarsNone (ClosMti.compile c.doMti c.maxApp es) := by
            cases hen : c.doMti <;>
              simp [ClosMti.compile, ClosMti.introList_varsNone, sk.2.1]
          exact (ClosNumber.renumberCodeLocs_everyFnVarsNone.1 _ _).2 before
        · exact ClosNumber.renumberCodeLocs_everyFnSome.1 _ _
        · intro k
          constructor
          · have before : everyFnVarsNone (mco k).2.1 := by
              have hk := (h.1.2.2.2.2.2.2.2.1 k).2
              exact (everyFnVarsNone_condMtiCompileInc c.doMti c.maxApp (co k).2).2 hk
            have number := (ClosNumber.renumberCodeLocs_everyFnVarsNone.1
              (makeEven ((mco k).1.1 + max (mco k).2.1.length 1)) (mco k).2.1).2 before
            simpa [nco, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc,
              everyFnVarsNone, fnVarsNoneExp] using number
          · have locs := ClosNumber.renumberCodeLocs_everyFnSome.1
              (makeEven ((mco k).1.1 + max (mco k).2.1.length 1)) (mco k).2.1
            simpa [nco, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc,
              everyFnLocationSome, fnLocationSomeExp] using locs
      have numbered : ∀ k, everyFnLocationSome (nco k).2.1 ∧ (nco k).2.2 = [] := by
        intro k
        have locs := ClosNumber.renumberCodeLocs_everyFnSome.1
          (makeEven ((mco k).1.1 + max (mco k).2.1.length 1)) (mco k).2.1
        have mempty : (mco k).2.2 = [] := by
          have he := h.1.1 k
          cases hen : c.doMti <;>
            simp [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc, hen, he]
        constructor
        · simpa [nco, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc,
            everyFnLocationSome, fnLocationSomeExp] using locs
        · simpa [nco, stateCo, ClosNumber.ignoreTable] using mempty
      have facts := knownCo_facts c.knownConf nco base known.1 known.2
        (by rw [ClosKnown.compileSource_eq_compile]) guard
      exact facts.2.2.2 n numbered
    have calledLocations := everyFnLocationSome_condCallCompileInc (kco n).2 c.doCall (kco n).1.1
    have mainLoc : everyFnLocationSome (aco n).2.1 := calledLocations.1 knownLocations.1
    have codeLoc : everyFnLocationSome ((aco n).2.2.map (fun entry => entry.2.2)) :=
      calledLocations.2 knownLocations
    have annotatedMain := ClosAnnotate.everyFnSome_annotate (aco n).2.1 0 mainLoc
    have annotatedCode := ClosAnnotate.everyFnSome_ann (aco n).2.2 codeLoc
    have varsMain := ClosAnnotate.everyFnVarsSome_annotate 0 (aco n).2.1
    have varsCode := annotateCompile_everyFnVarsSome (aco n).2.2
    have mainEq : (qco n).2.1 = es' := congrArg (fun x => x.2.1) eq
    have codeEq : (qco n).2.2 = ps := congrArg (fun x => x.2.2) eq
    change everyFnLocationSome (qco n).2.1 at annotatedMain
    change everyFnLocationSome ((qco n).2.2.map (fun entry => entry.2.2)) at annotatedCode
    change everyFnVarsSome (qco n).2.1 at varsMain
    change everyFnVarsSome ((qco n).2.2.map (fun entry => entry.2.2)) at varsCode
    rw [mainEq] at annotatedMain varsMain
    rw [codeEq] at annotatedCode varsCode
    refine ⟨annotatedMain, varsMain, ?_, ?_⟩
    · intro entry member
      apply (everyFnLocationSome_every _).1 annotatedCode entry.2.2
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    · intro entry member
      apply (everyFnVarsSome_every _).1 varsCode entry.2.2
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
end Flapjack.Compiler.Backend.ClosToBvl
