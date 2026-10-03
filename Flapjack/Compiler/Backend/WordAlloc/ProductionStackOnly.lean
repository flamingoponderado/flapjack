import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnlyCache
import Flapjack.Compiler.Backend.WordAlloc.ProductionClashTree
import Flapjack.Compiler.Backend.WordAlloc.GetStackOnly

namespace Flapjack.WordAlloc
open RiscV RiscV.CakeRegAlloc Compiler.Encoders.Asm RegAlloc

/-! Complete actual fast stack-only source analysis. Untagged implementation
correspondence to the reviewed native getStackOnly, using the real accepted
program encoder and derived cache/distinct-name invariants. -/

abbrev stackStateTree (state : CakeStackOnlyState) : Spt Unit × Spt Unit :=
  stackPairTree (stackStatePair state)

private theorem moveResult (x y : Nat) (state : CakeStackOnlyState)
    (valid : StackStateValid state) :
    stackStateTree (cakeStackOnlyMergeMove x y state) = mergeStackOnly (x, y) (stackStateTree state) ∧
      StackStateValid (cakeStackOnlyMergeMove x y state) := by
  have result := stackCache_move x y state valid
  refine ⟨?_, result.2⟩
  exact (congrArg stackPairTree result.1).trans (stackMove_production x y state.ts state.fs valid.1.1)

private theorem movesResult (moves : List (Nat × Nat)) (state : CakeStackOnlyState)
    (valid : StackStateValid state) :
    stackStateTree (moves.foldr (fun move state => cakeStackOnlyMergeMove move.1 move.2 state) state) =
      moves.foldr mergeStackOnly (stackStateTree state) ∧
    StackStateValid (moves.foldr (fun move state => cakeStackOnlyMergeMove move.1 move.2 state) state) := by
  induction moves with
  | nil => exact ⟨rfl, valid⟩
  | cons move moves ih =>
      have result := moveResult move.1 move.2 _ ih.2
      refine ⟨?_, result.2⟩
      simpa only [List.foldr_cons, Prod.eta, ih.1] using result.1

private theorem removeResult (keys : List Nat) (state : CakeStackOnlyState)
    (valid : StackStateValid state) :
    stackStateTree (cakeStackOnlyDeleteMany keys state) = removeTempStack keys (stackStateTree state) ∧
      StackStateValid (cakeStackOnlyDeleteMany keys state) := by
  have result := stackCache_remove keys state valid
  refine ⟨?_, result.2⟩
  exact (congrArg stackPairTree result.1).trans (stackRemove_production keys state.ts state.fs valid.1.1)

private theorem mergeResult (base left right : CakeStackOnlyState)
    (hb : StackStateValid base) (hl : StackStateValid left) (hr : StackStateValid right) :
    stackStateTree (cakeStackOnlyMergeSets base left right) =
      mergeStackSets (stackStateTree base) (stackStateTree left) (stackStateTree right) ∧
      StackStateValid (cakeStackOnlyMergeSets base left right) := by
  have result := stackCache_merge base left right hb hl hr
  exact ⟨(congrArg stackPairTree result.1).trans (stackMerge_production (stackStatePair base) (stackStatePair left) (stackStatePair right)), result.2⟩

private theorem treeResult (tree : WordClashTree) (state : CakeStackOnlyState)
    (valid : StackStateValid state) :
    stackStateTree (match tree with
      | .delta writes reads => cakeStackOnlyDeleteMany (writes ++ reads) state
      | _ => state) =
      (match productionClashTreeToNative tree with
      | .delta writes reads => removeTempStack (writes ++ reads) (stackStateTree state)
      | _ => stackStateTree state) ∧
    StackStateValid (match tree with
      | .delta writes reads => cakeStackOnlyDeleteMany (writes ++ reads) state
      | _ => state) := by
  cases tree <;> first | exact removeResult _ _ valid | exact ⟨rfl, valid⟩

private theorem programTreeResult {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (state : CakeStackOnlyState) (valid : StackStateValid state) :
    stackStateTree (match wordClashTree program [] with
      | .delta writes reads => cakeStackOnlyDeleteMany (writes ++ reads) state
      | _ => state) =
      (match getClashTree native [] with
      | .delta writes reads => removeTempStack (writes ++ reads) (stackStateTree state)
      | _ => stackStateTree state) ∧
    StackStateValid (match wordClashTree program [] with
      | .delta writes reads => cakeStackOnlyDeleteMany (writes ++ reads) state
      | _ => state) := by
  have result := treeResult (wordClashTree program []) state valid
  rw [clashTree_production (width := width) program native encoded []] at result
  simpa only [List.map_nil] using result

/-- The complete executed fast analysis agrees with native source semantics
and preserves the actual cached invariant on every accepted program. -/
theorem stackOnlyAux_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (state : CakeStackOnlyState) (valid : StackStateValid state) :
    stackStateTree (cakeGetStackOnlyAuxFast state program) = getStackOnlyAux (stackStateTree state) native ∧
      StackStateValid (cakeGetStackOnlyAuxFast state program) := by
  cases program
  case move priority moves =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux] using movesResult moves state valid
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux] using
      stackOnlyAux_production body _ hb state valid
  case loop names body exits =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux] using
      stackOnlyAux_production body _ hb state valid
  case seq first second =>
    cases hf : wordLangProgToHOL first <;> cases hs : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, hf, hs] at encoded
    subst native
    have secondResult := stackOnlyAux_production second _ hs state valid
    have firstResult := stackOnlyAux_production first _ hf _ secondResult.2
    simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux, secondResult.1] using firstResult
  case ite cmp condition right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    have yr := stackOnlyAux_production yes _ hy state valid
    have nr := stackOnlyAux_production no _ hn state valid
    have joined := mergeResult state _ _ valid yr.2 nr.2
    cases right <;>
      simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux, joined.1, yr.1, nr.1] using
        removeResult _ _ joined.2
  case call returns destination arguments handler =>
    cases hReturns : returns with
    | none =>
      cases hHandler : handler with
      | none =>
        simp [wordLangProgToHOL, hReturns, hHandler] at encoded
        subst native
        simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux] using And.intro (Eq.refl (stackStateTree state)) valid
      | some h =>
        rcases h with ⟨exception, body, l1, l2⟩
        cases hb : wordLangProgToHOL body <;>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
        subst native
        simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux] using And.intro (Eq.refl (stackStateTree state)) valid
    | some r =>
      rcases r with ⟨values, sets, body, l1, l2⟩
      cases hb : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, hReturns, hb] at encoded
      | some nb =>
        have br := stackOnlyAux_production body nb hb state valid
        cases hHandler : handler with
        | none =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux] using br
        | some h =>
          rcases h with ⟨exception, handlerBody, h1, h2⟩
          cases hh : wordLangProgToHOL handlerBody <;>
            simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
          subst native
          have hr := stackOnlyAux_production handlerBody _ hh state valid
          simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux, br.1, hr.1] using
            mergeResult state _ _ valid br.2 hr.2
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction with
    | none => simp [wordLangProgToHOL, hi] at encoded
    | some nativeInstruction =>
      simp [wordLangProgToHOL, hi] at encoded
      subst native
      have result := treeResult (wordClashTree (.inst instruction) []) state valid
      have tree := clashTree_production (width := width) (.inst instruction) (.inst nativeInstruction)
        (by simp [wordLangProgToHOL, hi]) []
      rw [tree] at result
      simp only [List.map_nil] at result
      simp only [cakeGetStackOnlyAuxFast, getStackOnlyAux]
      exact result
  case alloc destination sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux, wordClashTree, getClashTree] using
      And.intro (Eq.refl (stackStateTree state)) valid
  case install a b c d sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux, wordClashTree, getClashTree] using
      And.intro (Eq.refl (stackStateTree state)) valid
  case ffi name a b c d sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simpa only [cakeGetStackOnlyAuxFast, getStackOnlyAux, wordClashTree, getClashTree] using
      And.intro (Eq.refl (stackStateTree state)) valid
  case shareInst operator name address =>
    cases operator
    all_goals
      have result := programTreeResult (width := width) _ native encoded state valid
      simp only [wordLangProgToHOL, Option.some.injEq] at encoded
      subst native
      simpa [cakeGetStackOnlyAuxFast, getStackOnlyAux, wordClashTree, getClashTree,
        stackStateTree, wordClashTreeFindLoopFrame, cakeStackOnlyDeleteMany, removeTempStack] using result
  all_goals
    have result := programTreeResult (width := width) _ native encoded state valid
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simpa [cakeGetStackOnlyAuxFast, getStackOnlyAux, wordClashTree, getClashTree,
      stackStateTree, wordClashTreeFindLoopFrame, cakeStackOnlyDeleteMany, removeTempStack] using result
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hReturns]
    try rw [hHandler]
    try simp
    all_goals omega

/-- Complete actual forced-stack list producer from the real empty initial
state, rendered canonically as the native sparse map. -/
theorem stackOnly_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    stackNamesTree (cakeGetStackOnly program) = getStackOnly native := by
  have result := stackOnlyAux_production program native encoded
    (cakeStackOnlyStateOfPair ([], [])) (stackState_initial ([], []) ⟨by simp, by simp⟩)
  exact congrArg Prod.snd result.1

end Flapjack.WordAlloc
