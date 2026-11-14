import Flapjack.FiniteMap.AlistExact.Append
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonCompiler
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonLabelBound
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallAddresses
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationCodeSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberOracle
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SyntaxOracle
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownSyntax
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownOracleFacts
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.OracleDomains
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiSemantics
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.InstalledSemantics
import Flapjack.Compiler.Backend.ClosNumber.Proofs.Semantics

/-! Whole-program semantics of common closure preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps BackendProps ClosSem
local instance : Nonempty ClosKnown.Config := ⟨ClosKnown.defaultConfig 0⟩

/-- Adding a natural number on the left leaves a number unchanged exactly
when the added number is zero. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "obvious_arith_comm"]
theorem obviousArithComm (a b : Nat) : (a = b + a) ↔ b = 0 := by
  omega

/-- Common closure preprocessing preserves whole-program behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_common_semantics"
  (fmap_as_finite_support_result_observations :=
    [Flapjack.HolFiniteMapExact.holEmpty, Flapjack.HolFiniteMapExact.alistToFmap])]
theorem compileCommon_semantics {C F : Type} (ffi : HolFfiState F) (c c' : Config)
    (co : CompileOracle (Nat × Spt ClosKnown.ValApprox × NumSet × C))
    (cc : Compiler C) (es : List ClosLang.Exp)
    (code : List (Nat × Nat × ClosLang.Exp))
    (premises :
      semantics ffi c.maxApp HolFiniteMapExact.holEmpty co (compileCommonInc c cc) es ≠ .fail ∧
      compileCommon c es = (c', code) ∧
      (∀ n, (co n).2.2 = []) ∧
      (c.doMti → 1 ≤ c.maxApp ∧ (∀ e ∈ es, noMti e) ∧ ∀ n e, e ∈ (co n).2.1 → noMti e) ∧
      (c.doCall → everyFnVarsNone es ∧
        isStateOracle ClosCall.compileInc
          (ClosKnown.knownCo c.knownConf
            (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
              (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co))) ∧
        (co 0).1.2.2.1 = (ClosCall.compile c.doCall (compileIncPostKcompile c es).2).2.1) ∧
      (c.knownConf.isSome → 1 ≤ c.maxApp ∧
        oracleMonotonic (fun entry => setOfBag (elistGlobals entry.2.1)) (· < ·)
          (setOfBag (elistGlobals es)) co ∧
        isStateOracle (ClosKnown.compileInc (holThe c.knownConf))
          (pureCo (ClosFvs.compileIncSource (α := List (Nat × Nat × ClosLang.Exp))
            (β := Nat × Nat × ClosLang.Exp)) ∘
            stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
              (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)) ∧
        (co 0).1.2.1 = (holThe (compileIncPostKcompile c es).1).valApproxSpt ∧
        (∀ n, bagAllDistinct (elistGlobals (co n).2.1) ∧
          ∀ e ∈ (co n).2.1, esgcFree e)) ∧
      ¬ containsAppSome c.maxApp es ∧ ClosKnown.syntaxOk es ∧
      (∀ n, ¬ containsAppSome c.maxApp (co n).2.1 ∧ everyFnVarsNone (co n).2.1) ∧
      isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co) ∧
      (co 0).1.1 ≥ (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length))
        (ClosMti.compile c.doMti c.maxApp es)).1 ∧
      oracleMonotonic (fun entry => {x | x ∈ entry.2.2.map Prod.fst}) (· < ·)
        {x | x < (co 0).1.1}
        (stateCo (ClosCall.condCallCompileInc c.doCall)
          (ClosKnown.knownCo c.knownConf
            (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
              (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co))))) :
    semantics ffi c.maxApp (HolFiniteMapExact.alistToFmap code)
      (pureCo ClosAnnotate.compileIncSource ∘
        stateCo (ClosCall.condCallCompileInc c.doCall)
          (ClosKnown.knownCo c.knownConf
            (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
              (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co))))
      cc [.call .none 0 c'.start []] =
    semantics ffi c.maxApp HolFiniteMapExact.holEmpty co (compileCommonInc c cc) es := by
  obtain ⟨nonFail, compiled, emptyOracle, mti, call, known, appSafe, knownSyntax,
    future, numberOracle, bound, ordered⟩ := premises
  let source := ClosMti.compile c.doMti c.maxApp es
  let aligned := makeEven (c.nextLoc + max 1 source.length)
  cases hr : ClosNumber.renumberList aligned source with
  | mk next numbered =>
    cases hk : ClosKnown.compile c.knownConf numbered with
    | mk knownConf optimized =>
      cases hc : ClosCall.compile c.doCall optimized with
      | mk called state =>
        obtain ⟨globals, aux⟩ := state
        have compiled' :
            ({ c with start := c.nextLoc, nextLoc := next, knownConf := knownConf, callState := (globals, aux) },
              ClosAnnotate.compileSource (chainExps c.nextLoc called ++ aux)) = (c', code) := by
          change (let (next, expressions) := ClosNumber.renumberList aligned source
            let (known, expressions) := ClosKnown.compileSource c.knownConf expressions
            let (expressions, (globals, auxiliary)) := ClosCall.compile c.doCall expressions
            ({ c with start := c.nextLoc, nextLoc := next, knownConf := known, callState := (globals, auxiliary) },
              ClosAnnotate.compileSource (chainExps c.nextLoc expressions ++ auxiliary))) = (c', code) at compiled
          simpa only [ClosKnown.compileSource_eq_compile, hr, hk, hc] using compiled
        cases compiled'
        let mco := pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co
        let ncc := stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (ClosKnown.knownCc c.knownConf
            (stateCc (ClosCall.condCallCompileInc c.doCall)
              (pureCc ClosAnnotate.compileIncSource cc)))
        have mtiEq : semantics ffi c.maxApp HolFiniteMapExact.holEmpty mco ncc source =
            semantics ffi c.maxApp HolFiniteMapExact.holEmpty co (compileCommonInc c cc) es := by
          apply semantics_condMtiCompileInc ffi c.maxApp co c.doMti ncc es
          refine ⟨?_, ?_⟩
          · simpa [compileCommonInc, ncc] using nonFail
          · intro enabled
            obtain ⟨pos, input, oracle⟩ := mti enabled
            refine ⟨?_, pos, input⟩
            intro n
            exact ⟨emptyOracle n, oracle n⟩
        have mtiSafe : semantics ffi c.maxApp HolFiniteMapExact.holEmpty mco ncc source ≠ .fail := by
          rw [mtiEq]
          exact nonFail
        let kcc := ClosKnown.knownCc c.knownConf
          (stateCc (ClosCall.condCallCompileInc c.doCall)
            (pureCc ClosAnnotate.compileIncSource cc))
        let nco := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) mco
        have numberInput : ¬ containsAppSome c.maxApp source := by
          cases enabled : c.doMti <;>
            simpa [source, ClosMti.compile, enabled, ClosMti.introList_containsAppSome] using appSafe
        have numberOracleSafe : ∀ n, (mco n).2.2 = [] ∧
            ¬ containsAppSome c.maxApp (mco n).2.1 := by
          intro n
          cases enabled : c.doMti <;>
            simpa [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc,
              enabled, emptyOracle n, ClosMti.introList_containsAppSome] using (future n).1
        have numberEq : semantics ffi c.maxApp HolFiniteMapExact.holEmpty nco kcc numbered =
            semantics ffi c.maxApp HolFiniteMapExact.holEmpty mco ncc source := by
          have step := ClosNumber.semanticsNumberHOL ffi c.maxApp aligned mco kcc source
            (by simpa [ncc, kcc] using mtiSafe) ⟨numberInput, numberOracleSafe⟩
          simpa [nco, hr] using step
        have numberSafe : semantics ffi c.maxApp HolFiniteMapExact.holEmpty nco kcc numbered ≠ .fail := by
          rw [numberEq]
          exact mtiSafe
        have knownMonotonic (enabled : c.knownConf.isSome) :
            oracleMonotonic (fun entry => setOfBag (elistGlobals entry.2.1)) (· < ·)
              (setOfBag (elistGlobals numbered)) nco := by
          have hm := condMti_monotonic_elistGlobals es co c.doMti c.maxApp (known enabled).2.1
          have hn := numberMonotonic_elistGlobals (setOfBag (elistGlobals source)) mco
            (by simpa [mco, source] using hm)
          have eq := elistGlobals_renumberList aligned source
          rw [hr] at eq
          simpa [nco, eq] using hn
        have numberedSyntax : ClosKnown.syntaxOk numbered := by
          obtain ⟨vars, globals, free⟩ := knownSyntax
          have sourceVars : everyFnVarsNone source := by
            cases enabled : c.doMti <;>
              simpa [source, ClosMti.compile, enabled, ClosMti.introList_varsNone] using vars
          have numberedVars := (ClosNumber.renumberCodeLocs_everyFnVarsNone.1 aligned source).2 sourceVars
          have sourceFree : ∀ e ∈ source, esgcFree e :=
            ClosMti.compile_preserves_esgc_free c.maxApp c.doMti es free
          have numberedFree := ClosNumber.renumberCodeLocs_esgcFree.1 aligned source next numbered ⟨hr, sourceFree⟩
          have bagEq := elistGlobals_renumberList aligned source
          rw [hr] at bagEq
          have sourceBag : elistGlobals source = elistGlobals es :=
            ClosMti.compile_preserves_elist_globals c.maxApp c.doMti es
          refine ⟨by simpa [hr] using numberedVars, ?_, numberedFree⟩
          intro key
          rw [bagEq, sourceBag]
          exact globals key
        have mcoSyntax (enabled : c.knownConf.isSome) (n : Nat) :
            ClosKnown.syntaxOk (mco n).2.1 := by
          have entry := (known enabled).2.2.2.2 n
          have inputVars := (future n).2
          have inputBag : ∀ key, elistGlobals (co n).2.1 key ≤ 1 := entry.1
          have inputFree := entry.2
          have vars : everyFnVarsNone (mco n).2.1 := by
            cases h : c.doMti <;>
              simpa [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc,
                h, ClosMti.introList_varsNone] using inputVars
          have bag : elistGlobals (mco n).2.1 = elistGlobals (co n).2.1 := by
            cases h : c.doMti <;>
              simp [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc,
                h, ClosMti.intro_multi_preserves_elist_globals]
          have free : ∀ e ∈ (mco n).2.1, esgcFree e := by
            cases h : c.doMti with
            | false => simpa [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, h] using inputFree
            | true =>
              have preserved := ClosMti.intro_multi_preserves_esgc_free c.maxApp (co n).2.1 inputFree
              simpa [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc, h] using preserved
          exact ⟨vars, by simpa [bag] using inputBag, free⟩
        have ncoSyntax (enabled : c.knownConf.isSome) (n : Nat) :
            ClosKnown.syntaxOk (nco n).2.1 ∧ (nco n).2.2 = [] := by
          obtain ⟨vars, bag, free⟩ := mcoSyntax enabled n
          have vars' := (ClosNumber.renumberCodeLocs_everyFnVarsNone.1
            (makeEven ((mco n).1.1 + max (mco n).2.1.length 1)) (mco n).2.1).2 vars
          have free' := numberCompileInc_esgcFree (mco n).2.1 (mco n).1.1 free
          have bag' := numberCompileInc_globals (mco n).1.1 (mco n).2.1
          refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · simpa [nco, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc,
                everyFnVarsNone, fnVarsNoneExp] using vars'
            · simpa [nco, stateCo, ClosNumber.ignoreTable, bag'] using bag
            · simpa [nco, stateCo, ClosNumber.ignoreTable] using free'
          · simpa [nco, stateCo, ClosNumber.ignoreTable] using (numberOracleSafe n).1
        have sourceLength : source.length = es.length := by
          exact ClosMti.compile_length c.doMti c.maxApp es
        have postEq : compileIncPostKcompile c es = (knownConf, optimized) := by
          simp only [compileIncPostKcompile]
          change ClosKnown.compile c.knownConf
            (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length)) source).2 = _
          rw [← sourceLength]
          change ClosKnown.compile c.knownConf (ClosNumber.renumberList aligned source).2 = _
          rw [hr]
          exact hk
        have ksyntax (enabled : c.knownConf.isSome) :
            ClosKnown.syntaxOracleOk (holThe c.knownConf) numbered nco
              (holThe knownConf).valApproxSpt := by
          refine ⟨numberedSyntax, ?_, ?_, ?_, ncoSyntax enabled⟩
          · simpa [nco] using (known enabled).2.2.1
          · have first := (known enabled).2.2.2.1
            rw [postEq] at first
            exact first.symm
          · have monotone := knownMonotonic enabled
            change oracleMonotonic (fun entry => {i | 1 ≤ elistGlobals entry.2.1 i}) (· < ·)
              {i | 1 ≤ elistGlobals numbered i} nco at monotone
            simpa only [Nat.one_le_iff_ne_zero] using monotone
        let ccc := stateCc (ClosCall.condCallCompileInc c.doCall)
          (pureCc ClosAnnotate.compileIncSource cc)
        let kco := ClosKnown.knownCo c.knownConf nco
        have knownEq : semantics ffi c.maxApp HolFiniteMapExact.holEmpty kco ccc optimized =
            semantics ffi c.maxApp HolFiniteMapExact.holEmpty nco kcc numbered := by
          apply ClosKnown.semanticsCompile ffi c.maxApp nco kcc numbered c.knownConf knownConf ccc kco optimized
          refine ⟨numberSafe, rfl, rfl, ?_, ?_⟩
          · simpa [ClosKnown.compileSource_eq_compile] using hk
          · intro enabled
            exact ⟨ksyntax enabled, (known enabled).1⟩
        have knownSafe : semantics ffi c.maxApp HolFiniteMapExact.holEmpty kco ccc optimized ≠ .fail := by
          rw [knownEq]
          exact numberSafe
        have numberedCallSyntax : ClosCall.syntaxOk numbered := by
          apply renumberList_callSyntaxOk aligned source next numbered
          refine ⟨hr, ?_⟩
          cases h : c.doMti <;>
            simpa [source, ClosMti.compile, h, ClosMti.introList_varsNone] using knownSyntax.1
        have optimizedSyntax : ClosCall.syntaxOk optimized := by
          apply kcompile_csyntaxOk c.knownConf knownConf numbered optimized _ numberedCallSyntax
          simpa [ClosKnown.compileSource_eq_compile] using hk
        have ncoCallSyntax (n : Nat) : ClosCall.syntaxOk (nco n).2.1 := by
          have vars : everyFnVarsNone (mco n).2.1 := by
            cases h : c.doMti <;>
              simpa [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc,
                h, ClosMti.introList_varsNone] using (future n).2
          let nstart := makeEven ((mco n).1.1 + max (mco n).2.1.length 1)
          have safe := renumberList_callSyntaxOk nstart (mco n).2.1
            (ClosNumber.renumberList nstart (mco n).2.1).1
            (ClosNumber.renumberList nstart (mco n).2.1).2 ⟨(Prod.eta _).symm, vars⟩
          simpa [nco, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc, nstart,
            ClosCall.syntaxOk, everyFnLocationSome, fnLocationSomeExp,
            everyFnVarsNone, fnVarsNoneExp, codeLocations, codeLocationsExp] using safe
        have knownGuard (enabled : c.knownConf.isSome) :
            isStateOracle (ClosKnown.compileInc (holThe c.knownConf))
              (pureCo (ClosFvs.compileIncSource (α := List (Nat × Nat × ClosLang.Exp))
                (β := Nat × Nat × ClosLang.Exp)) ∘ nco) ∧
            (nco 0).1.1 = (holThe knownConf).valApproxSpt ∧
            everyFnVarsNone numbered ∧ everyFnLocationSome numbered ∧
            (∀ n, everyFnVarsNone (nco n).2.1 ∧ everyFnLocationSome (nco n).2.1) := by
          have input := ksyntax enabled
          refine ⟨input.2.1, input.2.2.1.symm, numberedSyntax.1, numberedCallSyntax.1, ?_⟩
          intro n
          exact ⟨(ncoSyntax enabled n).1.1, (ncoCallSyntax n).1⟩
        have facts := knownCo_facts c.knownConf nco numbered knownConf optimized
          (by simpa [ClosKnown.compileSource_eq_compile] using hk) knownGuard
        have orderedN : oracleMonotonic (fun entry => {x | x ∈ codeLocations entry.2.1}) (· < ·)
            {x | x ∈ codeLocations numbered} nco := by
          have hbound : (ClosNumber.renumberList aligned source).1 ≤ (mco 0).1.1 := by
            simpa [mco, pureCo, Function.comp_def, aligned, source, ← sourceLength] using bound
          have result := renumberCodeLocs_monotonic mco aligned source ⟨numberOracle, hbound⟩
          simpa [nco, hr] using result
        have orderedK : oracleMonotonic (fun entry => {x | x ∈ codeLocations entry.2.1}) (· < ·)
            {x | x ∈ codeLocations optimized} kco := by
          exact facts.1 orderedN
        have kcoCallSyntax (n : Nat) : ClosCall.syntaxOk (kco n).2.1 :=
          facts.2.1 n (ncoCallSyntax n)
        have kcoEmpty (n : Nat) : (kco n).2.2 = [] := by
          apply facts.2.2.1 n
          simpa [nco, stateCo, ClosNumber.ignoreTable] using (numberOracleSafe n).1
        let acc := pureCc ClosAnnotate.compileIncSource cc
        let aco := stateCo (ClosCall.condCallCompileInc c.doCall) kco
        have callEq : semantics ffi c.maxApp (HolFiniteMapExact.alistToFmap aux) aco acc called =
            semantics ffi c.maxApp HolFiniteMapExact.holEmpty kco ccc optimized := by
          apply semanticsCondCallCompileInc ffi c.maxApp kco acc optimized called c.doCall globals aux
            (HolFiniteMapExact.alistToFmap aux)
          refine ⟨?_, hc, rfl, ?_⟩
          · simpa [closStateCc, ccc, acc] using knownSafe
          · intro enabled
            refine ⟨optimizedSyntax, ?_, ?_, orderedK, ?_⟩
            · exact (call enabled).2.1
            · have first := (call enabled).2.2
              rw [postEq, hc] at first
              simpa [kco, fst_knownCo, nco, stateCo, mco, pureCo, Function.comp_def] using first.symm
            · intro n
              exact ⟨kcoCallSyntax n, kcoEmpty n⟩
        have callSafe : semantics ffi c.maxApp (HolFiniteMapExact.alistToFmap aux) aco acc called ≠ .fail := by
          rw [callEq]
          exact knownSafe
        have auxDomainMember {key : Nat} (member : key ∈ (HolFiniteMapExact.alistToFmap aux).domain) :
            key ∈ aux.map Prod.fst := by
          change (HolFiniteMapExact.alistToFmap aux).lookup key ≠ none at member
          rw [ClosCall.alistToFmapLookup] at member
          obtain ⟨value, found⟩ := Option.ne_none_iff_exists'.mp member
          exact List.mem_map.mpr ⟨(key, value), holALookup_member aux key value found, rfl⟩
        have numberingBounds := ClosNumber.renumberList_codeLocations_distinct aligned source
        rw [hr] at numberingBounds
        have numberingEven := ClosNumber.renumberCodeLocs_even.1 aligned source (even_makeEven _)
        rw [hr] at numberingEven
        have optimizedInNumbered (key : Nat) (member : key ∈ codeLocations optimized) :
            key ∈ codeLocations numbered := by
          have counts := ClosKnown.compile_codeLocationsBag c.knownConf knownConf numbered optimized hk key
          exact List.count_pos_iff.mp (by have pos := List.count_pos_iff.mpr member; omega)
        have auxBounds (key : Nat) (member : key ∈ (HolFiniteMapExact.alistToFmap aux).domain) :
            aligned < key ∧ key < next := by
          have inKeys := auxDomainMember member
          have subset := ccompile_aux_subset c optimized called globals aux hc inKeys
          obtain ⟨loc, locMember, keyEq⟩ := subset
          have locIn := optimizedInNumbered loc locMember
          have lower := numberingBounds.2.1 loc locIn
          have upper := numberingBounds.2.2 loc locIn
          have locEven := numberingEven.2 loc locIn
          have nextEven := numberingEven.1
          omega
        have numberLength := ClosNumber.renumberList_imp_length aligned source next numbered hr
        have knownLength := ClosKnown.compile_length c.knownConf numbered knownConf optimized hk
        have callLength := ClosCall.compile_length c.doCall optimized called (globals, aux) hc
        have chainLength : called.length = source.length := by omega
        have nextBound : next ≤ (co 0).1.1 := by
          change (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length)) source).1 ≤ _ at bound
          rw [← sourceLength] at bound
          change (ClosNumber.renumberList aligned source).1 ≤ _ at bound
          simpa [hr] using bound
        let chainSet : Set Nat := Set.image (fun i => c.nextLoc + i) {i | i < called.length}
        have chainBelow (x : Nat) (member : x ∈ chainSet) : x < aligned := by
          obtain ⟨i, hi, rfl⟩ := member
          change i < called.length at hi
          have before : c.nextLoc + i < c.nextLoc + max 1 source.length := by omega
          dsimp [aligned, makeEven]
          split <;> omega
        have chainDisjoint : ∀ x, ¬ (x ∈ chainSet ∧ x ∈ (HolFiniteMapExact.alistToFmap aux).domain) := by
          intro x h
          have low := chainBelow x h.1
          have high := (auxBounds x h.2).1
          omega
        have chainSubset : chainSet ∪ (HolFiniteMapExact.alistToFmap aux).domain ⊆
            {x | x < (co 0).1.1} := by
          intro x hx
          rcases hx with hchain | haux
          · have low := chainBelow x hchain
            have alignLe : aligned ≤ next := by
              have prop := ClosNumber.renumberCodeLocs_inc.1 aligned source
              simpa [hr] using prop
            exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le low alignLe) nextBound
          · have high := (auxBounds x haux).2
            exact Nat.lt_of_lt_of_le high nextBound
        have chainOrder : oracleMonotonic oracleCodeNames (· < ·)
            (chainSet ∪ (HolFiniteMapExact.alistToFmap aux).domain) aco := by
          apply oracleMonotonic_subset _ _ _ _ _ _ _ ?_ ordered
          constructor
          · exact chainSubset
          · intro n x hx
            exact hx
        have codeAppend : HolFiniteMapExact.alistToFmap (chainExps c.nextLoc called ++ aux) =
            HolFiniteMapExact.union (HolFiniteMapExact.alistToFmap (chainExps c.nextLoc called))
              (HolFiniteMapExact.alistToFmap aux) :=
          HolFiniteMapExact.alistToFmap_append _ _
        have chainEq : semantics ffi c.maxApp
              (HolFiniteMapExact.alistToFmap (chainExps c.nextLoc called ++ aux)) aco acc
              [.call .none 0 c.nextLoc []] =
            semantics ffi c.maxApp (HolFiniteMapExact.alistToFmap aux) aco acc called := by
          have result := chainExps_semantics_call ffi c.maxApp (HolFiniteMapExact.alistToFmap aux)
            aco acc called c.nextLoc ⟨callSafe, chainDisjoint, chainOrder⟩
          simpa [codeAppend] using result
        have chainSafe : semantics ffi c.maxApp
            (HolFiniteMapExact.alistToFmap (chainExps c.nextLoc called ++ aux)) aco acc
            [.call .none 0 c.nextLoc []] ≠ .fail := by
          rw [chainEq]
          exact callSafe
        have outputVars := callsCompile_callSyntaxOk c.doCall optimized called globals aux hc optimizedSyntax
        have codeVars : everyFnVarsNone ((chainExps c.nextLoc called ++ aux).map (fun p => p.2.2)) := by
          simp only [List.map_append, ClosKnown.everyFnVarsNone_append, chainExps_varsNone]
          exact outputVars
        have oracleVars (n : Nat) : everyFnVarsNone (aco n).2.1 ∧
            everyFnVarsNone ((aco n).2.2.map (fun p => p.2.2)) := by
          have v := (kcoCallSyntax n).2.1
          have vaux : everyFnVarsNone ((kco n).2.2.map (fun p => p.2.2)) := by
            rw [kcoEmpty n]
            simp [everyFnVarsNone]
          have keep := everyFnVarsNone_condCallCompileInc (kco n).2 c.doCall (kco n).1.1
          simpa [aco, stateCo] using And.intro (keep.1 v) (keep.2 ⟨v, vaux⟩)
        have annotationEq := ClosAnnotate.semanticsAnnotate_sourceShape ffi c.maxApp
          (chainExps c.nextLoc called ++ aux) aco cc [.call .none 0 c.nextLoc []]
          (by simpa [acc] using chainSafe)
          ⟨by simp [everyFnVarsNone, fnVarsNoneExp], codeVars, oracleVars⟩
        have fixedCall : ClosAnnotate.annotateSource 0 [.call .none 0 c.nextLoc []] =
            [.call .none 0 c.nextLoc []] := by
          simp [ClosAnnotate.annotateSource, ClosAnnotate.altFreeSource, ClosAnnotate.shiftSource]
        rw [fixedCall] at annotationEq
        simpa [aco, kco, nco, mco] using annotationEq.trans (chainEq.trans (callEq.trans (knownEq.trans (numberEq.trans mtiEq))))

end Flapjack.Compiler.Backend.ClosToBvl
