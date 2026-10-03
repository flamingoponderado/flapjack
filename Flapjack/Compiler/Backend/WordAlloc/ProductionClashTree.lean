import Flapjack.Compiler.Backend.WordAlloc.ProductionInstructionClashTree
import Flapjack.Compiler.Backend.WordAlloc.ProductionBufferClashTree
import Flapjack.Compiler.Backend.WordAlloc.ProductionCutsetContext
import Flapjack.Compiler.Backend.WordAlloc.ProductionCallInputs
import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorWrapperInputs
import Flapjack.Compiler.Backend.WordAlloc.ProductionForced

namespace Flapjack.WordAlloc
open RegAlloc RiscV.CakeRegAlloc Flapjack.Compiler.Encoders.Asm

/-! Whole actual/native clash-tree producer assembly. These are untagged
implementation equations; original getClashTree is already ported. The real
program encoder and complete recursive producer structure are retained. -/

private theorem namesSet_wf (names : List Nat) :
    sptWf (LoopToWord.toNumSetHOL names) = true := by
  rw [toNumSet_production]
  exact sptWfFromAList _

private theorem namesSet_lookup (names : List Nat) (key : Nat) :
    sptLookup key (LoopToWord.toNumSetHOL names) =
      if key ∈ names then some () else none := by
  rw [toNumSet_production, sptLookup_sptFromAList]
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [List.map_cons, sptAListLookup, List.mem_cons]
      by_cases equal : key = name
      · simp only [equal, if_true, true_or]
      · simp only [equal, if_false, false_or, ih]

private theorem namesSet_eraseDups (names : List Nat) :
    LoopToWord.toNumSetHOL names.eraseDups = LoopToWord.toNumSetHOL names := by
  apply (sptEqThm _ _ ⟨namesSet_wf _, namesSet_wf _⟩).mpr
  intro key
  simp only [namesSet_lookup, List.mem_eraseDups]

private theorem namesSet_fromList (names : List Nat) :
    LoopToWord.toNumSetHOL (NumSet.fromList names) = LoopToWord.toNumSetHOL names := by
  rw [toNumSet_production, numSetFromList_production, ← toNumSet_production]

private theorem namesSet_append (left right : List Nat) :
    LoopToWord.toNumSetHOL (left ++ right) =
      sptUnion (LoopToWord.toNumSetHOL left) (LoopToWord.toNumSetHOL right) := by
  rw [← callReturnInsertion_append, callReturnInsertion_union _ _ (namesSet_wf _)]

private theorem callSet_native (left right : List Nat) :
    LoopToWord.toNumSetHOL (wordClashTreeCallSet left right) =
      sptUnion (LoopToWord.toNumSetHOL left) (LoopToWord.toNumSetHOL right) := by
  rw [toNumSet_production, callSet_production]

private theorem emptyCallInsertion (names : List Nat) :
    numsetListInsert names .ln = LoopToWord.toNumSetHOL names := by
  simpa only [LoopToWord.toNumSetHOL, List.append_nil] using
    callReturnInsertion_append names []

private theorem exceptionInsertion_union (name : Nat) (cutset : NumSet)
    (wf : sptWf cutset = true) :
    sptInsert name () cutset = sptUnion (LoopToWord.toNumSetHOL [name]) cutset := by
  simpa only [numsetListInsert] using callReturnInsertion_union [name] cutset wf

/-- Complete original clash-tree producer on the real accepted source encoder,
including arbitrary loop contexts. Ordered deltas and both recursive children
are retained; canonical unit maps represent the actual list-backed sets.
This proves producer correspondence, without assuming an output tree or any
successful allocator execution. -/
theorem clashTree_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (frames : List (List Nat × List Nat)) :
    productionClashTreeToNative (wordClashTree program frames) =
      getClashTree native (frames.map wordCutsetsToHOL) := by
  cases program
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction <;> simp [wordLangProgToHOL, hi] at encoded
    subst native
    simpa only [wordClashTree, getClashTree] using
      instructionClashTree_production instruction _ hi
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp only [wordLangProgToHOL, hb, Option.map_some, Option.some.injEq] at encoded
      subst native
      simpa only [wordClashTree, getClashTree] using clashTree_production body nb hb frames
  case seq first second =>
    cases hf : wordLangProgToHOL first <;> cases hs : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, hf, hs] at encoded
    subst native
    simp only [wordClashTree, getClashTree, productionClashTreeToNative,
      clashTree_production first _ hf, clashTree_production second _ hs]
  case ite cmp register right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    cases right <;> simp only [wordClashTree, getClashTree, productionClashTreeToNative,
      clashTree_production yes _ hy, clashTree_production no _ hn, Option.map_none]
  case loop names body exits =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp [wordLangProgToHOL, hb] at encoded
      subst native
      simp only [wordClashTree, getClashTree, productionClashTreeToNative,
        ← toNumSet_production, clashTree_production body nb hb,
        List.map_cons, wordCutsetsToHOL]
  case «break» index =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordClashTree, getClashTree]
    rw [← loopFrame_production]
    cases found : wordClashTreeFindLoopFrame index frames with
    | none => simp [productionClashTreeToNative, sptFromAList]
    | some frame =>
      rcases frame with ⟨entryNames, exitNames⟩
      simp [productionClashTreeToNative, wordCutsetsToHOL, toNumSet_production]
  case «continue» index =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordClashTree, getClashTree]
    rw [← loopFrame_production]
    cases found : wordClashTreeFindLoopFrame index frames with
    | none => simp [productionClashTreeToNative, sptFromAList]
    | some frame =>
      rcases frame with ⟨entryNames, exitNames⟩
      simp [productionClashTreeToNative, wordCutsetsToHOL, toNumSet_production]
  case shareInst operator name address =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    exact shareInstClashTree_production operator name address frames
  case alloc destination sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordClashTree, getClashTree, productionClashTreeToNative,
      wordCutsetsToHOL, ← toNumSet_production, callSet_native]
  case install a b c d sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordClashTree, getClashTree, productionClashTreeToNative,
      wordCutsetsToHOL, ← toNumSet_production, callSet_native]
  case ffi name a b c d sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordClashTree, getClashTree, productionClashTreeToNative,
      wordCutsetsToHOL, ← toNumSet_production, callSet_native]
  case call returns destination arguments handler =>
    cases hReturns : returns with
    | none =>
      cases hHandler : handler with
      | none =>
          simp [wordLangProgToHOL, hReturns, hHandler] at encoded
          subst native
          simp only [wordClashTree, getClashTree, productionClashTreeToNative,
            ← toNumSet_production, namesSet_eraseDups, emptyCallInsertion]
      | some h =>
          rcases h with ⟨exception, body, l1, l2⟩
          cases hb : wordLangProgToHOL body with
          | none => simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          | some nb =>
              simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
              subst native
              simp only [wordClashTree, getClashTree, productionClashTreeToNative,
                ← toNumSet_production, namesSet_fromList,
                namesSet_eraseDups, emptyCallInsertion]
    | some r =>
      rcases r with ⟨values, sets, body, l1, l2⟩
      let cutset := sptUnion (LoopToWord.toNumSetHOL sets.1) (LoopToWord.toNumSetHOL sets.2)
      have cutsetWf : sptWf cutset = true :=
        sptWfUnion _ _ ⟨namesSet_wf _, namesSet_wf _⟩
      have returnSet := callReturnInsertion_union values cutset cutsetWf
      dsimp only [cutset] at returnSet
      cases hb : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, hReturns, hb] at encoded
      | some nb =>
        cases hHandler : handler with
        | none =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simp only [wordClashTree, wordClashTreeCallCutSet, getClashTree,
            productionClashTreeToNative, wordCutsetsToHOL,
            ← toNumSet_production, callSet_native, namesSet_append,
            emptyCallInsertion, returnSet,
            clashTree_production body nb hb]
        | some h =>
          rcases h with ⟨exception, handlerBody, h1, h2⟩
          cases hh : wordLangProgToHOL handlerBody with
          | none => simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
          | some nh =>
            simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
            subst native
            have exceptionSet := exceptionInsertion_union exception cutset cutsetWf
            dsimp only [cutset] at exceptionSet
            simp only [wordClashTree, getClashTree, productionClashTreeToNative,
              wordCutsetsToHOL, Option.map_some, ← toNumSet_production,
              callSet_native, emptyCallInsertion,
              returnSet, exceptionSet,
              clashTree_production body nb hb,
              clashTree_production handlerBody nh hh]
  all_goals simp only [wordLangProgToHOL, Option.some.injEq] at encoded
  all_goals subst native
  all_goals simp only [wordClashTree, getClashTree, productionClashTreeToNative,
    expressionReads_production]
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hReturns]
    try rw [hHandler]
    try simp
    all_goals omega

/-- Source-routed allocator result using the actual complete clash-tree and
forced-pair producers. Their correspondence and all input validity/bounds
are derived from encoder acceptance; no producer equality or successful
allocation result is supplied as a premise.

The stack-only list is the canonical original producer rendering here. Its
equality to actual cakeGetStackOnly, and the heuristic producer linkage,
remain separate executed-route obligations. This is implementation/caller
infrastructure, not a duplicate HOL allocator-correctness theorem. -/
theorem allocatorWrapperFromProductionTree {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (algorithm : Algorithm) (entries : Option (NatInfoMap Nat)) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) :
    ∃ colours : NatInfoMap Nat,
      regAlloc algorithm (entries.map sptFromAList) limit moves
        (getClashTree native []) (getForced config native []) (getStackOnly native) =
          .success (sptFromAList colours) ∧
      cakeDoRegAlloc algorithm.toProduction
        (entries.map (cakeSpillCostMap (cakeMkBij (wordClashTree program [])).nextNode))
        limit moves (wordClashTree program []) (cakeGetForced program)
        ((sptToAList (getStackOnly native)).map Prod.fst) = some colours := by
  have treeEq : productionClashTreeToNative (wordClashTree program []) =
      getClashTree native [] := by
    simpa only [List.map_nil] using clashTree_production program native encoded []
  have forcedEq := getForced_production config target program native encoded
  have valid := productionAllocator_setsWf program native encoded
  have bounds : ∀ pair ∈ cakeGetForced program,
      cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (wordClashTree program [])).toAllocator) pair.1 <
        (cakeMkBij (wordClashTree program [])).nextNode ∧
      cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (wordClashTree program [])).toAllocator) pair.2 <
        (cakeMkBij (wordClashTree program [])).nextNode := by
    rw [forcedEq]
    intro pair member
    have sourceMembers := getForcedInGetClashTree native [] config pair member
    constructor
    · apply producedAllocator_name_bound
      rw [treeEq]
      exact sourceMembers.1
    · apply producedAllocator_name_bound
      rw [treeEq]
      exact sourceMembers.2
  have composed := regAlloc_production algorithm entries limit moves
    (wordClashTree program []) (cakeGetForced program)
    ((sptToAList (getStackOnly native)).map Prod.fst) bounds
  have stackRoundtrip := clashTreeCodec_roundtrip (.set (getStackOnly native)) valid.2
  simp only [nativeClashTreeToProduction, productionClashTreeToNative,
    ClashTree.set.injEq] at stackRoundtrip
  simpa only [treeEq, forcedEq, stackRoundtrip] using composed

end Flapjack.WordAlloc
