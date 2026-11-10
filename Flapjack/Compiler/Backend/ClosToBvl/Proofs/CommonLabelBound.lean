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

/-- Whole-program preprocessing preserves the maximum application arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_common_max_app"]
theorem compileCommon_maxApp (c : Config) (es : List ClosLang.Exp)
    (c' : Config) (es' : List (Nat × Nat × ClosLang.Exp))
    (run : compileCommon c es = (c', es')) : c'.maxApp = c.maxApp := by
  simp only [compileCommon] at run
  repeat' split at run
  all_goals simp_all
  all_goals simpa using (congrArg Config.maxApp run.1).symm

/-- Whole-program preprocessing produces distinct entry labels and nested closure locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_common_distinct_locs"]
theorem compileCommon_distinctLocations (c : Config) (es : List ClosLang.Exp)
    (c' : Config) (p : List (Nat × Nat × ClosLang.Exp))
    (run : compileCommon c es = (c', p)) :
    ((p.map Prod.fst) ++ codeLocations (p.map (fun t => t.2.2))).Nodup := by
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
        have even := ClosNumber.renumberCodeLocs_even.1 aligned source (even_makeEven _)
        simp only [hr] at even
        have locs := ClosNumber.renumberList_codeLocations_distinct aligned source
        simp only [hr] at locs
        have optimizedCount : ∀ x, (codeLocations optimized).count x ≤ (codeLocations numbered).count x := by
          intro x
          exact ClosKnown.compile_codeLocationsBag c.knownConf known numbered optimized hk x
        have optimizedLoc : ∀ x ∈ codeLocations optimized, x ∈ codeLocations numbered := by
          intro x hx
          have positive : 0 < (codeLocations optimized).count x := List.count_pos_iff.mpr hx
          exact List.count_pos_iff.mp (by have := optimizedCount x; omega)
        have optimizedNodup : (codeLocations optimized).Nodup := by
          apply List.nodup_iff_count_le_one.mpr
          intro x
          exact Nat.le_trans (optimizedCount x) (List.nodup_iff_count_le_one.mp locs.1 x)
        have calledLoc : ∀ x ∈ codeLocations (called ++ aux.map (fun t => t.2.2)),
            x ∈ codeLocations numbered := by
          intro x hx
          exact optimizedLoc x (ccompile_locs_subset c optimized called globals aux hc hx)
        have calledDistinct : (codeLocations (called ++ aux.map (fun t => t.2.2))).Nodup := by
          cases enabled : c.doCall with
          | false =>
            simp [ClosCall.compile, enabled] at hc
            obtain ⟨rfl, _, rfl⟩ := hc
            simpa using optimizedNodup
          | true =>
            have callsRun : ClosCall.calls optimized (.ln, []) = (called, globals, aux) := by
              simpa [ClosCall.compile, enabled] using hc
            have h := ClosCall.calls_codeLocations_allDistinct optimized (.ln, []) called (globals, aux)
              callsRun (by simpa [codeLocations] using optimizedNodup)
            simpa [codeLocations_append] using h
        have auxDistinct : (aux.map Prod.fst).Nodup := by
          cases enabled : c.doCall with
          | false => simp [ClosCall.compile, enabled] at hc; obtain ⟨_, _, rfl⟩ := hc; simp
          | true =>
            have callsRun : ClosCall.calls optimized (.ln, []) = (called, globals, aux) := by
              simpa [ClosCall.compile, enabled] using hc
            apply ClosCall.calls_allDistinct optimized (.ln, []) called (globals, aux)
            exact ⟨callsRun, by simp, optimizedNodup, by simp⟩
        have auxOrigin : ∀ x ∈ aux.map Prod.fst, ∃ y ∈ codeLocations numbered, x = y + 1 := by
          intro x hx
          obtain ⟨y, hy, eq⟩ := ccompile_aux_subset c optimized called globals aux hc hx
          exact ⟨y, optimizedLoc y hy, by simpa [Nat.succ_eq_add_one] using eq.symm⟩
        have chainUpper : ∀ x ∈ (chainExps c.nextLoc called).map Prod.fst, x < aligned := by
          intro x hx
          rw [mapFst_chainExps_any] at hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          have hi := List.mem_range.mp hi
          have eqLength : called.length = source.length := by omega
          have leAlign : c.nextLoc + max 1 source.length ≤ aligned := by
            simp only [aligned, makeEven]
            split <;> omega
          omega
        have preDistinct : (((chainExps c.nextLoc called ++ aux).map Prod.fst) ++
            codeLocations ((chainExps c.nextLoc called ++ aux).map (fun t => t.2.2))).Nodup := by
          simp only [List.map_append, codeLocations_append, chainExps_codeLocations]
          have calledDistinct' : (codeLocations called ++ codeLocations (aux.map (fun t => t.2.2))).Nodup := by
            simpa [codeLocations_append] using calledDistinct
          have hmid : ((aux.map Prod.fst) ++
              (codeLocations called ++ codeLocations (aux.map (fun t => t.2.2)))).Nodup := by
            apply List.Nodup.append auxDistinct calledDistinct'
            intro x hx hloc
            obtain ⟨y, hy, rfl⟩ := auxOrigin x hx
            have old : y + 1 ∈ codeLocations numbered := calledLoc _ (by simpa [codeLocations_append] using hloc)
            have evenY := even.2 y hy
            have evenNext := even.2 (y + 1) old
            omega
          rw [List.append_assoc]
          apply List.Nodup.append (chainExps_labels_nodup c.nextLoc called) hmid
          intro x hx hrest
          have upper := chainUpper x hx
          rcases List.mem_append.mp hrest with haux | hloc
          · obtain ⟨y, hy, rfl⟩ := auxOrigin x haux
            have lower := locs.2.1 y hy
            omega
          · have old : x ∈ codeLocations numbered := calledLoc _ (by simpa [codeLocations_append] using hloc)
            have lower := locs.2.1 x old
            omega
        have names : (ClosAnnotate.compileSource (chainExps c.nextLoc called ++ aux)).map Prod.fst =
            (chainExps c.nextLoc called ++ aux).map Prod.fst := by
          simp [ClosAnnotate.compileSource_eq, List.map_map, Function.comp_def]
        have annotated := annotateCompile_codeLocations (chainExps c.nextLoc called ++ aux)
        rw [names]
        apply List.Nodup.append
        · exact (List.nodup_append.mp preDistinct).1
        · exact annotated.2 (List.nodup_append.mp preDistinct).2.1
        · intro x hx hy
          exact (List.nodup_append.mp preDistinct).2.2 x hx x (annotated.1 hy) rfl


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
