import Flapjack.Compiler.Backend.WordAlloc.GetStackOnly
import Flapjack.Misc.Sptree.Wf
import Flapjack.Compiler.Backend.RegAlloc.ProductionInputCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorInputs

namespace Flapjack.WordAlloc

/-! Production boundary infrastructure without an independent HOL original.
These lemmas establish native sparse-tree representation invariants; they do
not establish allocator success or correspondence of the complete producer. -/

def StackOnlySetsWf (trees : Spt Unit × Spt Unit) : Prop :=
  sptWf trees.1 = true ∧ sptWf trees.2 = true

theorem removeTempStack_setsWf (keys : List Nat) (trees : Spt Unit × Spt Unit)
    (wf : StackOnlySetsWf trees) : StackOnlySetsWf (removeTempStack keys trees) := by
  refine ⟨?_, wf.2⟩
  change sptWf (keys.foldr sptDelete trees.1) = true
  induction keys with
  | nil => exact wf.1
  | cons key keys ih => exact sptWfDelete _ key ih

theorem mergeStackOnly_setsWf (move : Nat × Nat) (trees : Spt Unit × Spt Unit)
    (wf : StackOnlySetsWf trees) : StackOnlySetsWf (mergeStackOnly move trees) := by
  rcases move with ⟨x, y⟩
  rcases trees with ⟨temporary, fixed⟩
  rcases wf with ⟨ht, hf⟩
  simp only [mergeStackOnly]
  by_cases lookup : sptLookup x temporary = some () <;>
    by_cases alloc : isAllocVar y = true <;>
    by_cases physical : isPhyVar y = true <;>
    by_cases stack : isStackVar x = true
  all_goals simp only [lookup, alloc, physical, stack, if_true, if_false, StackOnlySetsWf]
  all_goals exact ⟨by first | exact sptWfInsert _ _ _ ht | exact sptWfDelete _ _ ht | exact ht,
    by first | exact sptWfInsert _ _ _ hf | exact hf⟩

theorem mergeStackSets_setsWf (initial left right : Spt Unit × Spt Unit)
    (hi : StackOnlySetsWf initial) (hl : StackOnlySetsWf left)
    (hr : StackOnlySetsWf right) : StackOnlySetsWf (mergeStackSets initial left right) := by
  exact ⟨sptWfUnion _ _ ⟨sptWfInter _ _, sptWfUnion _ _
    ⟨sptWfDifference _ _ ⟨hl.1, hi.1⟩, sptWfDifference _ _ ⟨hr.1, hi.1⟩⟩⟩,
    sptWfUnion _ _ ⟨hl.2, hr.2⟩⟩

theorem stackOnlyMoves_setsWf (moves : List (Nat × Nat))
    (trees : Spt Unit × Spt Unit) (wf : StackOnlySetsWf trees) :
    StackOnlySetsWf (moves.foldr mergeStackOnly trees) := by
  induction moves with
  | nil => exact wf
  | cons move moves ih => exact mergeStackOnly_setsWf move _ ih

/-- The analysis starts from well-formed trees and never imports program cutsets
into its result. Thus this invariant needs no program-set hypothesis. -/
theorem getStackOnlyAux_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (trees : Spt Unit × Spt Unit)
    (wf : StackOnlySetsWf trees) : StackOnlySetsWf (getStackOnlyAux trees program) := by
  induction trees, program using getStackOnlyAux.induct with
  | case1 trees priority moves => exact stackOnlyMoves_setsWf moves trees wf
  | case2 trees first second ihSecond ihFirst => exact ihFirst (ihSecond wf)
  | case3 trees cmp condition first second register ihFirst ihSecond =>
      exact removeTempStack_setsWf _ _
        (mergeStackSets_setsWf trees _ _ wf (ihFirst wf) (ihSecond wf))
  | case4 trees cmp condition first second value ihFirst ihSecond =>
      exact removeTempStack_setsWf _ _
        (mergeStackSets_setsWf trees _ _ wf (ihFirst wf) (ihSecond wf))
  | case5 trees body ih => exact ih wf
  | case6 trees target arguments handler => exact wf
  | case7 trees target arguments values cutsets returnHandler l1 l2 ih => exact ih wf
  | case8 trees target arguments values cutsets returnHandler l1 l2 exception body h1 h2 ihReturn ihBody =>
      exact mergeStackSets_setsWf trees _ _ wf (ihReturn wf) (ihBody wf)
  | case9 trees names body exits ih => exact ih wf
  | case10 trees program noMove noSeq noIte noMust noCall noLoop writes reads equation =>
      cases program <;> first
        | exact False.elim (noMove _ _ rfl)
        | exact False.elim (noSeq _ _ rfl)
        | exact False.elim (noIte _ _ _ _ _ rfl)
        | exact False.elim (noMust _ rfl)
        | exact False.elim (noCall _ _ _ _ rfl)
        | exact False.elim (noLoop _ _ _ rfl)
        | simpa only [getStackOnlyAux, equation] using removeTempStack_setsWf (writes ++ reads) trees wf
  | case11 trees program noMove noSeq noIte noMust noCall noLoop noDelta =>
      cases program <;> first
        | exact False.elim (noMove _ _ rfl)
        | exact False.elim (noSeq _ _ rfl)
        | exact False.elim (noIte _ _ _ _ _ rfl)
        | exact False.elim (noMust _ rfl)
        | exact False.elim (noCall _ _ _ _ rfl)
        | exact False.elim (noLoop _ _ _ rfl)
        | (simp only [getStackOnlyAux]; first | exact wf | (split <;> first | exact wf | exact False.elim (noDelta _ _ ‹_›)))

theorem getStackOnly_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : sptWf (getStackOnly program) = true :=
  (getStackOnlyAux_setsWf program (.ln, .ln) ⟨rfl, rfl⟩).2

/-- Input representation invariant on syntax, independent of clash-tree output.
Only constructors carrying sets or recursive programs impose obligations. -/
def WordAllocatorProgramSetsWf {width : Nat} : WordLangProgHOL (BitVec width) → Prop
  | .seq first second => WordAllocatorProgramSetsWf first ∧ WordAllocatorProgramSetsWf second
  | .ite _ _ _ first second => WordAllocatorProgramSetsWf first ∧ WordAllocatorProgramSetsWf second
  | .mustTerminate body => WordAllocatorProgramSetsWf body
  | .loop names body exits => StackOnlySetsWf (names, exits) ∧ WordAllocatorProgramSetsWf body
  | .alloc _ sets | .install _ _ _ _ sets | .ffi _ _ _ _ _ sets => StackOnlySetsWf sets
  | .call returns _ _ handler =>
      (match returns with
       | none => True
       | some (_, sets, body, _, _) => StackOnlySetsWf sets ∧ WordAllocatorProgramSetsWf body) ∧
      (match handler with
       | none => True
       | some (_, body, _, _) => WordAllocatorProgramSetsWf body)
  | _ => True
termination_by program => sizeOf program

theorem numsetListInsert_setsWf (names : List Nat) (tree : NumSet)
    (wf : sptWf tree = true) : sptWf (numsetListInsert names tree) = true := by
  induction names with
  | nil => exact wf
  | cons name names ih => exact sptWfInsert _ _ _ ih

private theorem contextSet_setsWf (context : List (NumSet × NumSet))
    (wf : ∀ pair ∈ context, StackOnlySetsWf pair) (index : Nat) :
    sptWf ((context[index]?).map Prod.fst |>.getD .ln) = true ∧
    sptWf ((context[index]?).map Prod.snd |>.getD .ln) = true := by
  cases equation : context[index]? with
  | none => exact ⟨rfl, rfl⟩
  | some pair =>
      exact wf pair (List.mem_of_getElem? equation)

theorem getClashTree_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (context : List (NumSet × NumSet))
    (programWf : WordAllocatorProgramSetsWf program)
    (contextWf : ∀ pair ∈ context, StackOnlySetsWf pair) :
    RegAlloc.NativeClashTreeSetsWf (getClashTree program context) := by
  induction program, context using getClashTree.induct with
  | case3 instruction context =>
      simp only [getClashTree]
      unfold getDeltaInst
      split <;> try trivial
      all_goals split <;> trivial
  | case7 first second context ihFirst ihSecond =>
      simp only [WordAllocatorProgramSetsWf] at programWf
      simp only [getClashTree, RegAlloc.NativeClashTreeSetsWf]
      exact ⟨ihFirst programWf.1 contextWf, ihSecond programWf.2 contextWf⟩
  | case8 cmp condition first second context register ihFirst ihSecond =>
      simp only [WordAllocatorProgramSetsWf] at programWf
      simp only [getClashTree, RegAlloc.NativeClashTreeSetsWf]
      exact ⟨True.intro, (by intro set eq; cases eq), ihFirst programWf.1 contextWf,
        ihSecond programWf.2 contextWf⟩
  | case9 cmp condition first second context value ihFirst ihSecond =>
      simp only [WordAllocatorProgramSetsWf] at programWf
      simp only [getClashTree, RegAlloc.NativeClashTreeSetsWf]
      exact ⟨True.intro, (by intro set eq; cases eq), ihFirst programWf.1 contextWf,
        ihSecond programWf.2 contextWf⟩
  | case10 body context ih =>
      simp only [WordAllocatorProgramSetsWf] at programWf
      simpa only [getClashTree] using ih programWf contextWf
  | case25 names body exits context ih =>
      simp only [WordAllocatorProgramSetsWf] at programWf
      simp only [getClashTree, RegAlloc.NativeClashTreeSetsWf]
      have input := programWf.1
      have bodyWf := ih programWf.2 (by
        intro pair member
        rcases List.mem_cons.mp member with equal | member
        · subst pair; exact input
        · exact contextWf pair member)
      exact ⟨input.1, input.2, bodyWf, input.1⟩
  | case26 index context => simpa only [getClashTree, RegAlloc.NativeClashTreeSetsWf] using (contextSet_setsWf context contextWf index).2
  | case27 index context => simpa only [getClashTree, RegAlloc.NativeClashTreeSetsWf] using (contextSet_setsWf context contextWf index).1
  | case28 target arguments handler context => simpa only [getClashTree, RegAlloc.NativeClashTreeSetsWf] using numsetListInsert_setsWf arguments .ln rfl
  | case29 target arguments context values sets body l1 l2 ih =>
      simp only [WordAllocatorProgramSetsWf] at programWf
      simp only [getClashTree, RegAlloc.NativeClashTreeSetsWf]
      have cutset := sptWfUnion _ _ programWf.1.1
      exact ⟨sptWfUnion _ _ ⟨cutset, numsetListInsert_setsWf arguments .ln rfl⟩,
        numsetListInsert_setsWf values _ cutset, ih programWf.1.2 contextWf⟩
  | case30 target arguments context values sets body l1 l2 exception handler h1 h2 ihReturn ihHandler =>
      simp only [WordAllocatorProgramSetsWf] at programWf
      simp only [getClashTree, RegAlloc.NativeClashTreeSetsWf]
      have cutset := sptWfUnion _ _ programWf.1.1
      refine ⟨?_, ⟨numsetListInsert_setsWf values _ cutset, ihReturn programWf.1.2 contextWf⟩,
        sptWfInsert _ _ _ cutset, ihHandler programWf.2 contextWf⟩
      intro set equal
      cases equal
      exact sptWfUnion _ _ ⟨cutset, numsetListInsert_setsWf arguments .ln rfl⟩
  | _ =>
      simp_all [WordAllocatorProgramSetsWf, StackOnlySetsWf, getClashTree,
        RegAlloc.NativeClashTreeSetsWf, sptWfUnion]

private theorem productionNumSet_setsWf (names : List Nat) :
    sptWf (LoopToWord.toNumSetHOL names) = true := by
  induction names with
  | nil => rfl
  | cons name names ih => exact sptWfInsert _ _ _ ih

private theorem productionCutsets_setsWf (sets : List Nat × List Nat) :
    StackOnlySetsWf (wordCutsetsToHOL sets) :=
  ⟨productionNumSet_setsWf sets.1, productionNumSet_setsWf sets.2⟩

/-- The executed program carrier encoder constructs canonical sparse trees at
all loop/cutset fields. Accepted encoding supplies the input invariant without
assuming anything about the clash-tree or allocator output. -/
theorem productionProgram_setsWf {width : Nat}
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    WordAllocatorProgramSetsWf native := by
  cases program
  case inst instruction =>
    cases equation : wordLangInstToHOL instruction <;> simp [wordLangProgToHOL, equation] at encoded
    subst native
    simp [WordAllocatorProgramSetsWf]
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp only [wordLangProgToHOL, hb, Option.map_some, Option.some.injEq] at encoded
      subst native
      simpa only [WordAllocatorProgramSetsWf] using productionProgram_setsWf body nb hb
  case seq left right =>
    cases hl : wordLangProgToHOL left <;> cases hr : wordLangProgToHOL right <;>
      simp [wordLangProgToHOL, hl, hr] at encoded
    subst native
    simp [WordAllocatorProgramSetsWf, productionProgram_setsWf left _ hl, productionProgram_setsWf right _ hr]
  case ite cmp register right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    simp [WordAllocatorProgramSetsWf, productionProgram_setsWf yes _ hy, productionProgram_setsWf no _ hn]
  case loop names body exits =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp [wordLangProgToHOL, hb] at encoded
      subst native
      simp only [WordAllocatorProgramSetsWf]
      exact ⟨⟨productionNumSet_setsWf _, productionNumSet_setsWf _⟩, productionProgram_setsWf body nb hb⟩
  case call returns target arguments handler =>
    cases hReturns : returns with
    | none =>
      cases hHandler : handler with
      | none => simp [wordLangProgToHOL, hReturns, hHandler] at encoded; subst native; simp [WordAllocatorProgramSetsWf]
      | some h =>
        rcases h with ⟨exception, body, l1, l2⟩
        cases hb : wordLangProgToHOL body with
        | none => simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
        | some nb =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simp [WordAllocatorProgramSetsWf, productionProgram_setsWf body nb hb]
    | some r =>
      rcases r with ⟨values, sets, body, l1, l2⟩
      cases hb : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, hReturns, hb] at encoded
      | some nb =>
        cases hHandler : handler with
        | none =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simp [WordAllocatorProgramSetsWf, productionCutsets_setsWf, productionProgram_setsWf body nb hb]
        | some h =>
          rcases h with ⟨exception, hbody, h1, h2⟩
          cases hh : wordLangProgToHOL hbody with
          | none => simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
          | some nh =>
            simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
            subst native
            simp [WordAllocatorProgramSetsWf, productionCutsets_setsWf, productionProgram_setsWf body nb hb, productionProgram_setsWf hbody nh hh]
  all_goals simp only [wordLangProgToHOL, Option.some.injEq] at encoded
  all_goals subst native
  all_goals simp [WordAllocatorProgramSetsWf, productionCutsets_setsWf]
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hReturns]
    try rw [hHandler]
    try simp
    all_goals omega

/-- Both original allocator input sets are valid on the accepted production
encoding route. The premise is encoder acceptance, not target evaluation. -/
theorem productionAllocator_setsWf {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    RegAlloc.NativeClashTreeSetsWf (getClashTree native []) ∧
    sptWf (getStackOnly native) = true :=
  ⟨getClashTree_setsWf native [] (productionProgram_setsWf program native encoded)
    (by simp), getStackOnly_setsWf native⟩

end Flapjack.WordAlloc
