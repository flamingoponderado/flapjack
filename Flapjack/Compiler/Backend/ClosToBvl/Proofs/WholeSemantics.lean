import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainSyntactic
import Flapjack.Misc.Sptree.FromAList.Lookup
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InitialState
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.OracleInvariant
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WholeDistinct
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonLookup

/-! Whole-program closure-to-BVL compilation preserves semantics. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps BackendProps ClosSem
open Flapjack.Basis.Pure.MlString
local instance : Nonempty ClosKnown.Config := ⟨ClosKnown.defaultConfig 0⟩

/-- The complete closure-to-BVL compilation preserves program behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_semantics"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem compile_semantics {C F : Type} (ffi : HolFfiState F) (c c' : Config)
    (co : CompileOracle (Nat × Spt ClosKnown.ValApprox × NumSet × C))
    (cc : BvlSem.Compiler C) (es : List ClosLang.Exp)
    (prog : List (Nat × Nat × Bvl.Exp)) (names : Spt MlString)
    (premises :
      ClosSem.semantics ffi c.maxApp HolFiniteMapExact.holEmpty co
        (compileCommonInc c (pureCc (compileInc c.maxApp) cc)) es ≠ .fail ∧
      compileSource c es = (c', prog, names) ∧ syntaxOracleOkCommon c c' es co) :
    BvlSem.semantics ffi (sptFromAList prog)
      (pureCo (compileInc c.maxApp) ∘ pureCo ClosAnnotate.compileIncSource ∘
        stateCo (ClosCall.condCallCompileInc c.doCall)
          (ClosKnown.knownCo c.knownConf
            (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
              (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co))))
      cc c'.start =
    ClosSem.semantics ffi c.maxApp HolFiniteMapExact.holEmpty co
      (compileCommonInc c (pureCc (compileInc c.maxApp) cc)) es := by
  obtain ⟨nonFail, compiled, oracle⟩ := premises
  have allDistinct := compileSource_allDistinct c es c' prog names compiled
  cases common : compileCommon c es with
  | mk current sourceCode =>
    let all := sptToAList (initCode current.maxApp) ++
      [(numStubs current.maxApp - 2, 2, forceThunkCode)] ++
      [(numStubs current.maxApp - 1, 0, initGlobals current.maxApp
        (numStubs current.maxApp + current.start))] ++
      compileProgExpsHOL current.maxApp sourceCode
    have sourceRun :
        ({ current with start := numStubs current.maxApp - 1 }, codeSort all,
          makeNameAlist (all.map Prod.fst) sourceCode (numStubs current.maxApp) c.nextLoc es.length) =
          (c', prog, names) := by
      simpa only [compileSource, common, all] using compiled
    cases sourceRun
    have currentMax : current.maxApp = c.maxApp := compileCommon_maxApp c es current sourceCode common
    have sourceOracle : syntaxOracleOkCommon c current es co := by
      apply (syntaxOracleOkCommon_start c current (fun _ => numStubs current.maxApp - 1) es co).mp
      exact oracle
    have originalNodup : (all.map Prod.fst).Nodup := (codeSort_allDistinct all).mp allDistinct
    have targetCode : sptFromAList (codeSort all) = sptFromAList all := sort_fromAList all originalNodup
    have commonFields :
        current.nextLoc = (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length))
          (ClosMti.compile c.doMti c.maxApp es)).1 ∧
        current.knownConf = (compileIncPostKcompile c es).1 ∧
        current.callState.1 = (ClosCall.compile c.doCall (compileIncPostKcompile c es).2).2.1 := by
      let source := ClosMti.compile c.doMti c.maxApp es
      let aligned := makeEven (c.nextLoc + max 1 source.length)
      have length : source.length = es.length := by
        cases h : c.doMti <;> simp [source, ClosMti.compile, h, ClosMti.introList_length]
      cases hr : ClosNumber.renumberList aligned source with
      | mk next numbered =>
        cases hk : ClosKnown.compile c.knownConf numbered with
        | mk nextKnown optimized =>
          cases hc : ClosCall.compile c.doCall optimized with
          | mk called state =>
            obtain ⟨globals, aux⟩ := state
            have run := common
            change (let (next, expressions) := ClosNumber.renumberList aligned source
              let (known, expressions) := ClosKnown.compileSource c.knownConf expressions
              let (expressions, (globals, auxiliary)) := ClosCall.compile c.doCall expressions
              ({ c with start := c.nextLoc, nextLoc := next, knownConf := known, callState := (globals, auxiliary) },
                ClosAnnotate.compileSource (chainExps c.nextLoc expressions ++ auxiliary))) = (current, sourceCode) at run
            simp only [ClosKnown.compileSource_eq_compile, hr, hk, hc, Prod.mk.injEq] at run
            have cfg := run.1
            have post : compileIncPostKcompile c es = (nextKnown, optimized) := by
              simp only [compileIncPostKcompile]
              change ClosKnown.compile c.knownConf
                (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length)) source).2 = _
              rw [← length]
              change ClosKnown.compile c.knownConf (ClosNumber.renumberList aligned source).2 = _
              rw [hr]
              exact hk
            have numbered : (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length))
                (ClosMti.compile c.doMti c.maxApp es)).1 = next := by
              change (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length)) source).1 = next
              rw [← length]
              change (ClosNumber.renumberList aligned source).1 = next
              simp [hr]
            rw [post, hc, numbered]
            cases cfg
            simp
    have callOrder := syntaxOracleOk_callFst_monotonic c current es co sourceCode ⟨sourceOracle, common⟩
    have sourceOracleParts := sourceOracle
    simp only [syntaxOracleOkCommon] at sourceOracleParts
    obtain ⟨empty, mti, ⟨v, initial⟩, call, known, appSafe, knownSyntax, future, numberOracle⟩ := sourceOracleParts
    have initialNext : (co 0).1.1 = current.nextLoc := congrArg (fun z => z.1) initial
    have initialKnown : (co 0).1.2.1 = ClosKnown.optionValApproxSpt current.knownConf :=
      congrArg (fun z => z.2.1) initial
    have initialCall : (co 0).1.2.2.1 = current.callState.1 := congrArg (fun z => z.2.2.1) initial
    have commonHypotheses :
        ClosSem.semantics ffi c.maxApp HolFiniteMapExact.holEmpty co
          (compileCommonInc c (pureCc (compileInc c.maxApp) cc)) es ≠ .fail ∧
        compileCommon c es = (current, sourceCode) ∧
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
          (∀ n, bagAllDistinct (elistGlobals (co n).2.1) ∧ ∀ e ∈ (co n).2.1, esgcFree e)) ∧
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
                (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)))) := by
      refine ⟨nonFail, common, empty, mti, ?_, ?_, appSafe, knownSyntax, future, numberOracle, ?_, callOrder⟩
      · intro enabled
        exact ⟨(call enabled).1, (call enabled).2, initialCall.trans commonFields.2.2⟩
      · intro enabled
        obtain ⟨pos, _, monotone, state, safe⟩ := known enabled
        refine ⟨pos, monotone, state, ?_, safe⟩
        have postSome : (compileIncPostKcompile c es).1.isSome := by
          unfold compileIncPostKcompile
          cases h : ClosKnown.compile c.knownConf
            (ClosNumber.renumberList (makeEven (c.nextLoc + max 1 es.length))
              (ClosMti.compile c.doMti c.maxApp es)).2 with
          | mk next out =>
            simpa [h] using (ClosKnown.compile_isSome c.knownConf _ next out h).2 enabled
        rw [commonFields.2.1] at initialKnown
        cases h : (compileIncPostKcompile c es).1 with
        | none => simp [h] at postSome
        | some cfg => simpa [h, ClosKnown.optionValApproxSpt, holThe] using initialKnown
      · rw [← commonFields.1]
        exact le_of_eq initialNext.symm
    have commonEq := compileCommon_semantics ffi c current co (pureCc (compileInc c.maxApp) cc)
      es sourceCode commonHypotheses
    have lookupEntry (key arity : Nat) (body : Bvl.Exp)
        (member : (key, arity, body) ∈ all) :
        sptLookup key (sptFromAList all) = some (arity, body) := by
      rw [sptLookupFromAList]
      exact holALookup_of_distinct_member all key (arity, body) ⟨originalNodup, member⟩
    have lookupGeneric (n : Nat) (hn : n < c.maxApp) :
        sptLookup (genericAppFnLocation n) (sptFromAList all) =
          some (n + 2, generateGenericApp c.maxApp n) := by
      have positive : 0 < current.maxApp := by omega
      have h := (initCode_ok current.maxApp positive).1 n (by omega)
      rw [currentMax] at h
      apply lookupEntry
      simp [all, sptMemToAList, currentMax, h]
    have lookupPartial (total previous : Nat) (ht : total < c.maxApp) (hp : previous < total) :
        sptLookup (partialAppFnLocation c.maxApp total previous) (sptFromAList all) =
          some (total - previous + 1, generatePartialAppClosureFn total previous) := by
      have positive : 0 < current.maxApp := by omega
      have h := (initCode_ok current.maxApp positive).2 total previous ⟨by omega, hp⟩
      rw [currentMax] at h
      apply lookupEntry
      simp [all, sptMemToAList, currentMax, h]
    have lookupForce : sptLookup (numStubs c.maxApp - 2) (sptFromAList all) =
        some (2, forceThunkCode) := by
      apply lookupEntry
      simp [all, currentMax]
    have lookupInitial : sptLookup (numStubs c.maxApp - 1) (sptFromAList all) =
        some (0, initGlobals c.maxApp (numStubs c.maxApp + current.start)) := by
      apply lookupEntry
      simp [all, currentMax]
    have installedExtend (entries : List (Nat × Nat × Bvl.Exp))
        (installed : codeInstalled entries (sptFromAList (compileProgExpsHOL c.maxApp sourceCode))) :
        codeInstalled entries (sptFromAList all) := by
      intro entry member
      have found := installed entry member
      rw [sptLookup_sptFromAList] at found
      have inCompiled := sptAListLookup_mem entry.1 (compileProgExpsHOL c.maxApp sourceCode) entry.2 found
      obtain ⟨key, arity, body⟩ := entry
      apply lookupEntry
      simp [all, currentMax, inCompiled]
    have compiledBody (name arity : Nat) (body : ClosLang.Exp)
        (found : (HolFiniteMapExact.alistToFmap sourceCode).lookup name = some (arity, body)) :
        ∃ aux1 body2 aux2, compileExpsHOL c.maxApp [body] aux1 = ([body2], aux2) ∧
          sptLookup (name + numStubs c.maxApp) (sptFromAList all) = some (arity, body2) ∧
          codeInstalled aux2 (sptFromAList all) := by
      have lookup : holALookup sourceCode name = some (arity, body) := by
        simpa [ClosCall.alistToFmapLookup] using found
      obtain ⟨aux1, body2, aux2, run, member, installed⟩ :=
        alookup_compileCommon c es current sourceCode name arity body ⟨common, lookup⟩
      refine ⟨aux1, body2, aux2, run, ?_, installedExtend aux2 installed⟩
      apply lookupEntry
      have included := holALookup_member _ _ _ member
      simp [all, currentMax, included]
    have compiledInstalled : codeInstalled (compileProgExpsHOL c.maxApp sourceCode) (sptFromAList all) := by
      apply codeInstalled_fromAList_strong all (compileProgExpsHOL c.maxApp sourceCode)
      refine ⟨originalNodup, ?_⟩
      dsimp [all]
      rw [currentMax]
      exact List.infix_append_right
    have initRel : initCodeRelation (HolFiniteMapExact.alistToFmap sourceCode) (sptFromAList all) c.maxApp := by
      refine ⟨lookupGeneric, ?_, compiledBody⟩
      intro total previous ⟨ht, hp⟩
      have h := lookupPartial total previous ht hp
      have eq : total + 1 - previous = total - previous + 1 := by omega
      simpa [eq] using h
    let aco := pureCo ClosAnnotate.compileIncSource ∘
      stateCo (ClosCall.condCallCompileInc c.doCall)
        (ClosKnown.knownCo c.knownConf
          (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
            (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)))
    have sourceSafe : ClosSem.semantics ffi c.maxApp (HolFiniteMapExact.alistToFmap sourceCode)
        aco (pureCc (compileInc c.maxApp) cc) [.call .none 0 current.start []] ≠ .fail := by
      rw [show ClosSem.semantics ffi c.maxApp (HolFiniteMapExact.alistToFmap sourceCode)
        aco (pureCc (compileInc c.maxApp) cc) [.call .none 0 current.start []] =
        ClosSem.semantics ffi c.maxApp HolFiniteMapExact.holEmpty co
          (compileCommonInc c (pureCc (compileInc c.maxApp) cc)) es from commonEq]
      exact nonFail
    have oracleInv : compileOracleInv c.maxApp (HolFiniteMapExact.alistToFmap sourceCode)
        (pureCc (compileInc c.maxApp) cc) aco (sptFromAList all) cc
        (pureCo (compileInc c.maxApp) ∘ aco) := by
      have result := syntaxOracleOk_to_oracleInv sourceCode current cc es co c current ⟨sourceOracle, common⟩
      simpa [aco, all, currentMax, Nat.add_comm] using result
    have sourceAnnotations :
        everyFnLocationSome (sourceCode.map (fun entry => entry.2.2)) ∧
        everyFnVarsSome (sourceCode.map (fun entry => entry.2.2)) := by
      let source := ClosMti.compile c.doMti c.maxApp es
      let aligned := makeEven (c.nextLoc + max 1 source.length)
      cases hr : ClosNumber.renumberList aligned source with
      | mk next numbered =>
        cases hk : ClosKnown.compile c.knownConf numbered with
        | mk nextKnown optimized =>
          cases hc : ClosCall.compile c.doCall optimized with
          | mk called state =>
            obtain ⟨globals, aux⟩ := state
            have run := common
            change (let (next, expressions) := ClosNumber.renumberList aligned source
              let (known, expressions) := ClosKnown.compileSource c.knownConf expressions
              let (expressions, (globals, auxiliary)) := ClosCall.compile c.doCall expressions
              ({ c with start := c.nextLoc, nextLoc := next, knownConf := known, callState := (globals, auxiliary) },
                ClosAnnotate.compileSource (chainExps c.nextLoc expressions ++ auxiliary))) = (current, sourceCode) at run
            simp only [ClosKnown.compileSource_eq_compile, hr, hk, hc, Prod.mk.injEq] at run
            have sourceVars : everyFnVarsNone source := by
              cases h : c.doMti <;> simpa [source, ClosMti.compile, h, ClosMti.introList_varsNone] using knownSyntax.1
            have numOk := renumberList_callSyntaxOk aligned source next numbered ⟨hr, sourceVars⟩
            have optOk := kcompile_csyntaxOk c.knownConf nextKnown numbered optimized
              (by simpa [ClosKnown.compileSource_eq_compile] using hk) numOk
            have calledOk := ccompile_everyFnLocationSome optimized c.doCall called globals aux ⟨optOk.1, hc⟩
            have chainLoc := (chainExps_fnLocationSome_iff c.nextLoc called).2 calledOk.1
            have before : everyFnLocationSome ((chainExps c.nextLoc called ++ aux).map (fun p => p.2.2)) := by
              rw [List.map_append, everyFnLocationSome_every]
              intro body member
              rcases List.mem_append.mp member with left | right
              · exact (everyFnLocationSome_every _).mp chainLoc body left
              · exact (everyFnLocationSome_every _).mp calledOk.2 body right
            have loc := compile_everyFnSome (chainExps c.nextLoc called ++ aux) before
            have vars := annotateCompile_everyFnVarsSome (chainExps c.nextLoc called ++ aux)
            rw [run.2] at loc vars
            exact ⟨loc, vars⟩
    have locations (name arity : Nat) (body : ClosLang.Exp)
        (found : (HolFiniteMapExact.alistToFmap sourceCode).lookup name = some (arity, body)) :
        everyFnLocationSome [body] := by
      have lookup : holALookup sourceCode name = some (arity, body) := by
        simpa [ClosCall.alistToFmapLookup] using found
      have member := holALookup_member _ _ _ lookup
      apply (everyFnLocationSome_every _).mp sourceAnnotations.1 body
      exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
    have vars (name arity : Nat) (body : ClosLang.Exp)
        (found : (HolFiniteMapExact.alistToFmap sourceCode).lookup name = some (arity, body)) :
        everyFnVarsSome [body] := by
      have lookup : holALookup sourceCode name = some (arity, body) := by
        simpa [ClosCall.alistToFmapLookup] using found
      have member := holALookup_member _ _ _ lookup
      apply (everyFnVarsSome_every _).mp sourceAnnotations.2 body
      exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
    have bvlEq := compileProgSemantics_source ffi c.maxApp
      (HolFiniteMapExact.alistToFmap sourceCode) aco (pureCc (compileInc c.maxApp) cc)
      current.start (sptFromAList all) sourceCode (compileProgExpsHOL c.maxApp sourceCode)
      (numStubs c.maxApp - 1) cc (pureCo (compileInc c.maxApp) ∘ aco)
      ⟨sourceSafe, compiledBody, rfl, initRel, locations, vars, lookupInitial, lookupForce, oracleInv, compiledInstalled⟩
    rw [targetCode]
    simpa [aco, currentMax] using bvlEq.trans commonEq

end Flapjack.Compiler.Backend.ClosToBvl
