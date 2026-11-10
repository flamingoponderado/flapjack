module

public import Flapjack.Compiler.Backend.ClosToBvl.WholeProgram
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonLabelBound
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SortPermutation
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InitialCodeDomain
import Flapjack.Misc.Sptree.ToAList
import Mathlib.Data.List.Nodup

@[expose] public section

/-! Distinct labels in whole-program closure-to-BVL output. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosProps

/-- Whole-program compilation produces pairwise distinct code labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_all_distinct_locs"]
theorem compileSource_allDistinct (c : Config) (e : List ClosLang.Exp) (c' : Config)
    (p : List (Nat × Nat × Bvl.Exp)) (n : Spt Flapjack.Basis.Pure.MlString.MlString)
    (run : compileSource c e = (c', p, n)) : (p.map Prod.fst).Nodup := by
  cases common : compileCommon c e with
  | mk current prog =>
    have distinct := compileCommon_distinctLocations c e current prog common
    have sourceRun :
        ({ current with start := numStubs current.maxApp - 1 },
          codeSort (sptToAList (initCode current.maxApp) ++
            [(numStubs current.maxApp - 2, 2, forceThunkCode)] ++
            [(numStubs current.maxApp - 1, 0, initGlobals current.maxApp
              (numStubs current.maxApp + current.start))] ++
            compileProgExpsHOL current.maxApp prog),
          makeNameAlist ((sptToAList (initCode current.maxApp) ++
            [(numStubs current.maxApp - 2, 2, forceThunkCode)] ++
            [(numStubs current.maxApp - 1, 0, initGlobals current.maxApp
              (numStubs current.maxApp + current.start))] ++
            compileProgExpsHOL current.maxApp prog).map Prod.fst) prog
            (numStubs current.maxApp) c.nextLoc e.length) = (c', p, n) := by
      simpa only [compileSource, common] using run
    cases sourceRun
    rw [codeSort_allDistinct]
    have two : 2 ≤ numStubs current.maxApp := by simp only [numStubs]; omega
    have initialBound : ∀ k ∈ (sptToAList (initCode current.maxApp)).map Prod.fst,
        k < numStubs current.maxApp - 2 := by
      intro k hk
      have domain := (sptMemMapFstToAList (initCode current.maxApp) k).mp hk
      cases hmax : current.maxApp with
      | zero => simp [initCode, sptFromList, sptDomain, hmax] at domain
      | succ q =>
        rw [hmax, domain_initCode (q + 1) (by omega)] at domain
        simp only [numStubs]
        omega
    have compiledDistinct : ((compileProgExpsHOL current.maxApp prog).map Prod.fst).Nodup := by
      rw [map_fst_compileProg]
      have parts := List.nodup_append.mp distinct
      have reverseNodup : (codeLocations (prog.map (fun p => p.2.2))).reverse.Nodup := by
        simpa only [List.nodup_reverse] using parts.2.1
      have base : (prog.map Prod.fst ++ (codeLocations (prog.map (fun p => p.2.2))).reverse).Nodup := by
        apply List.Nodup.append parts.1 reverseNodup
        intro x hx hy
        exact parts.2.2 x hx x (by simpa only [List.mem_reverse] using hy) rfl
      exact base.map (fun _ _ eq => by omega)
    have compiledBound : ∀ k ∈ (compileProgExpsHOL current.maxApp prog).map Prod.fst,
        numStubs current.maxApp ≤ k := by
      intro k hk
      rw [map_fst_compileProg] at hk
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hk
      omega
    have initialDistinct := sptAllDistinctMapFstToAList (initCode current.maxApp)
    have stubDistinct : [numStubs current.maxApp - 2, numStubs current.maxApp - 1].Nodup := by
      have diff : numStubs current.maxApp - 2 ≠ numStubs current.maxApp - 1 := by omega
      simp [diff]
    have preDistinct : ((sptToAList (initCode current.maxApp)).map Prod.fst ++
        [numStubs current.maxApp - 2, numStubs current.maxApp - 1]).Nodup := by
      apply List.Nodup.append initialDistinct stubDistinct
      intro k hk hstubs
      have lower := initialBound k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hstubs
      omega
    have all := List.Nodup.append preDistinct compiledDistinct (by
      intro k hk hc
      have lower := compiledBound k hc
      rcases List.mem_append.mp hk with hinit | hstub
      · have upper := initialBound k hinit
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hstub
        omega)
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
      List.append_assoc, List.cons_append, List.nil_append] using all

end Flapjack.Compiler.Backend.ClosToBvl
