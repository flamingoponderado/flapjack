module

public import Flapjack.Compiler.Backend.ClosToBvl.Common
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.LabelOrigins
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallBounds
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainLocations
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationAddresses
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CodeLocations
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileLength
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationDistinct
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationParity
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants
public import Flapjack.Misc.MakeEven

@[expose] public section

/-! Label bounds for whole-program closure preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- Preprocessing keeps all compiled program labels below its next location. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_common_MAP_FST_compile_prog"]
theorem compileCommon_mapFst_compileProg (c : Config) (es : List ClosLang.Exp)
    (c' : Config) (p : List (Nat × Nat × ClosLang.Exp))
    (run : compileCommon c es = (c', p)) :
    {x | x ∈ (compileProgExpsHOL c.maxApp p).map Prod.fst} ⊆
      {x | x < c'.nextLoc + numStubs c.maxApp} := by
  let source := ClosMti.compile c.doMti c.maxApp es
  let aligned := makeEven (c.nextLoc + max 1 source.length)
  cases hr : ClosNumber.renumberList aligned source with
  | mk next numbered =>
    cases hk : ClosKnown.compile c.knownConf numbered with
    | mk known optimized =>
      cases hc : ClosCall.compile c.doCall optimized with
      | mk called state =>
        obtain ⟨globals, aux⟩ := state
        have run' :
            ({ c with start := c.nextLoc, nextLoc := next, knownConf := known, callState := (globals, aux) },
              ClosAnnotate.compileSource (chainExps c.nextLoc called ++ aux)) = (c', p) := by
          change (let (next, expressions) := ClosNumber.renumberList aligned source
            let (known, expressions) := ClosKnown.compile c.knownConf expressions
            let (expressions, (globals, auxiliary)) := ClosCall.compile c.doCall expressions
            ({ c with start := c.nextLoc, nextLoc := next, knownConf := known, callState := (globals, auxiliary) },
              ClosAnnotate.compileSource (chainExps c.nextLoc expressions ++ auxiliary))) = (c', p) at run
          simpa only [hr, hk, hc] using run
        cases run'
        have nlen := ClosNumber.renumberList_imp_length aligned source next numbered hr
        have klen := ClosKnown.compile_length c.knownConf numbered known optimized hk
        have clen := ClosCall.compile_length c.doCall optimized called (globals, aux) hc
        have nextBound : aligned ≤ next := by
          have bound := ClosNumber.renumberCodeLocs_imp_inc aligned source next numbered (.var .none 0) 0 (.var .none 0)
          exact bound.1 hr
        have even := ClosNumber.renumberCodeLocs_even.1 aligned source (even_makeEven _)
        simp only [hr] at even
        have locs := ClosNumber.renumberList_codeLocations_distinct aligned source
        simp only [hr] at locs
        have optimizedLoc : ∀ x ∈ codeLocations optimized, x ∈ codeLocations numbered := by
          intro x hx
          have counts := ClosKnown.compile_codeLocationsBag c.knownConf known numbered optimized hk x
          have positive : 0 < (codeLocations optimized).count x := List.count_pos_iff.mpr hx
          exact List.count_pos_iff.mp (by omega : 0 < (codeLocations numbered).count x)
        have numberedBound : ∀ x ∈ codeLocations numbered, x < next ∧ x + 1 < next := by
          intro x hx
          have lt := locs.2.2 x hx
          have xe := even.2 x hx
          have ne := even.1
          omega
        have calledLoc : ∀ x ∈ codeLocations (called ++ aux.map (fun t => t.2.2)),
            x ∈ codeLocations numbered := by
          intro x hx
          exact optimizedLoc x (ccompile_locs_subset c optimized called globals aux hc hx)
        have auxLabel : ∀ x ∈ aux.map Prod.fst, x < next := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := ccompile_aux_subset c optimized called globals aux hc hx
          have hy := optimizedLoc y hy
          have bound := numberedBound y hy
          omega
        have chainLabel : ∀ x ∈ (chainExps c.nextLoc called).map Prod.fst, x < next := by
          intro x hx
          rw [mapFst_chainExps_any] at hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          have hi := List.mem_range.mp hi
          have alignBound : c.nextLoc + max 1 source.length ≤ aligned := by
            simp only [aligned, makeEven]
            split <;> omega
          omega
        have annotationNames :
            (ClosAnnotate.compileSource (chainExps c.nextLoc called ++ aux)).map Prod.fst =
              (chainExps c.nextLoc called ++ aux).map Prod.fst := by
          simp [ClosAnnotate.compileSource_eq, List.map_map, Function.comp_def]
        intro x hx
        rw [map_fst_compileProg] at hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have ybound : y < next := by
          rcases List.mem_append.mp hy with entry | location
          · rw [annotationNames, List.map_append] at entry
            rcases List.mem_append.mp entry with chain | auxiliary
            · exact chainLabel y chain
            · exact auxLabel y auxiliary
          · have location' : y ∈ codeLocations
                ((ClosAnnotate.compileSource (chainExps c.nextLoc called ++ aux)).map (fun t => t.2.2)) := by
              simpa using location
            have original := (annotateCompile_codeLocations (chainExps c.nextLoc called ++ aux)).1 location'
            simp only [List.map_append, codeLocations_append, chainExps_codeLocations, List.mem_append] at original
            have old : y ∈ codeLocations (called ++ aux.map (fun t => t.2.2)) := by
              simpa [codeLocations_append] using original
            exact (numberedBound y (calledLoc y old)).1
        change numStubs c.maxApp + y < next + numStubs c.maxApp
        omega

end Flapjack.Compiler.Backend.ClosToBvl
