module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.Semantics.WordSem.State
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Less
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Arith
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.LongDiv
public import Flapjack.Compiler.Backend.DataToWord.CallTree
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.NumberVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberEl
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.DivCodeAssum
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StateRel

@[expose] public section

/-! Supporting lemmas of the data-to-word division assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Shifting a word right by one less than its width leaves its sign bit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_bit_lsr_dimindex_1"
  (words_as_type_indexed_bitvec)]
theorem wordBit_lsr_dimindex_1 {width : Nat} [NeZero width] (w1 : BitVec width) :
    (w1 >>> (width - 1)).getLsbD 0 = true ↔ w1.msb = true := by
  have pos := NeZero.pos width
  rw [BitVec.getLsbD_ushiftRight, Nat.add_zero, BitVec.msb_eq_getLsbD_last]

/-- The bound on an optional sum is independent of the summand order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "option_le_add_comm"]
theorem optionLe_add_comm (a b c : Option Nat) :
    optionLe (wordSemOptionAdd a b) c → optionLe (wordSemOptionAdd b a) c := by
  cases a <;> cases b <;> cases c <;> simp [wordSemOptionAdd, optionLe]; omega

/-- Every adjusted live name recovers a source live name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IN_adjust_set_IN"]
theorem in_adjustSet_in {α : Type} (y : Nat) (x : Spt α) :
    sptDomain (adjustSet x) y → sptDomain x ((y - 2) / 2) := by
  intro member
  obtain ⟨n, rfl, present⟩ := (Proofs.Gc.adjustSet_domain x y).mp member
  have : (adjustVar n - 2) / 2 = n := by simp only [adjustVar]; omega
  rw [this]
  exact present



/-- Shape of a successful source integer `div`. Private infrastructure for the
HOL proof, with no separate HOL declaration. -/
theorem divSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.intOp .div) values source = .val (result, resultState)) :
    ∃ a b next, values = [.number a, .number b] ∧ b ≠ 0 ∧
      DataSem.doSpace (.intOp .div) values source = some next ∧
      result = .number (a.fdiv b) ∧
      resultState = DataSem.doStack (.intOp .div) values
        (DataSem.doLimSafe next (.intOp .div) values) := by
  cases sp : DataSem.doSpace (.intOp .div) values source with
  | none => simp [DataSem.doApp, sp] at run
  | some next =>
    cases intResult : DataSem.doIntApp .div values with
    | none => simp [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] at run
    | some v =>
      have r : result = v ∧ resultState = DataSem.doStack (.intOp .div) values
          (DataSem.doLimSafe next (.intOp .div) values) := by
        simpa [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] using run.symm
      match values, intResult with
      | [.number a, .number b], intResult =>
        by_cases hb : b = 0 <;> simp_all [DataSem.doIntApp]

/-- Shape of a successful source integer `mod`. Private infrastructure for the
HOL proof, with no separate HOL declaration. -/
theorem modSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.intOp .mod) values source = .val (result, resultState)) :
    ∃ a b next, values = [.number a, .number b] ∧ b ≠ 0 ∧
      DataSem.doSpace (.intOp .mod) values source = some next ∧
      result = .number (a.fmod b) ∧
      resultState = DataSem.doStack (.intOp .mod) values
        (DataSem.doLimSafe next (.intOp .mod) values) := by
  cases sp : DataSem.doSpace (.intOp .mod) values source with
  | none => simp [DataSem.doApp, sp] at run
  | some next =>
    cases intResult : DataSem.doIntApp .mod values with
    | none => simp [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] at run
    | some v =>
      have r : result = v ∧ resultState = DataSem.doStack (.intOp .mod) values
          (DataSem.doLimSafe next (.intOp .mod) values) := by
        simpa [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] using run.symm
      match values, intResult with
      | [.number a, .number b], intResult =>
        by_cases hb : b = 0 <;> simp_all [DataSem.doIntApp]


/-- Assignment followed by a tail. Private infrastructure for the HOL proof. -/
theorem divEvalAssignSeq {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : WordSemStateFiniteExact.wordExp s expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (WordSemStateFiniteExact.setVar key v s) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Sequential evaluation without `fix_clock`. Private infrastructure for the HOL proof. -/
theorem divEvalSeq {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl

/-- The sequential-evaluation `match` agrees with HOL's `λ(res,s1). if res = NONE …`
continuation used in `eval_Call_Arith`. Private infrastructure for the HOL proof. -/
theorem divSeqIfMatch {width : Nat} [NeZero width] {C F : Type}
    (E : Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (k : WordSemStateFiniteExact width C F → Option (WordSemResult width) × WordSemStateFiniteExact width C F) :
    (match E with
      | (none, s1) => k s1
      | (some res, s1) => (some res, s1)) =
    (if E.1 = none then k E.2 else (E.1, E.2)) := by
  rcases E with ⟨_ | _, _⟩ <;> simp

/-- Both operands untagged and non-negative clears the generated tag test.
Private infrastructure for the HOL proof. -/
theorem divTagZero {width : Nat} [NeZero width] (x y : BitVec width)
    (hx0 : ¬ x.getLsbD 0 = true) (hy0 : ¬ y.getLsbD 0 = true)
    (hxm : ¬ x.msb = true) (hym : ¬ y.msb = true) :
    ((x ||| y) ||| ((x ||| y) >>> (width - 1))) &&& 1 = 0 := by
  apply (StackAlloc.word_and_one_eq_0_iff _).mpr
  have hm : ¬ ((x ||| y) >>> (width - 1)).getLsbD 0 = true := by
    rw [wordBit_lsr_dimindex_1, BitVec.msb_or]
    simp_all
  simp_all [BitVec.getLsbD_or]

/-- A clear tag test means both operands are untagged with clear sign bits.
Private infrastructure for the HOL proof. -/
theorem divTagZero_inv {width : Nat} [NeZero width] (x y : BitVec width)
    (h : ((x ||| y) ||| ((x ||| y) >>> (width - 1))) &&& 1 = 0) :
    ¬ x.getLsbD 0 = true ∧ ¬ y.getLsbD 0 = true ∧ ¬ x.msb = true ∧ ¬ y.msb = true := by
  have bit := (StackAlloc.word_and_one_eq_0_iff _).mp h
  have hm : ¬ ((x ||| y) >>> (width - 1)).getLsbD 0 = true := by
    intro hh; apply bit; simp [BitVec.getLsbD_or, hh]
  rw [wordBit_lsr_dimindex_1, BitVec.msb_or] at hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hx; apply bit; simp [BitVec.getLsbD_or, hx]
  · intro hy; apply bit; simp [BitVec.getLsbD_or, hy]
  · intro hx; apply hm; simp [hx]
  · intro hy; apply hm; simp [hy]

/-- Assigning a small natural number to a source variable and its tagged word to the
adjusted target variable preserves the state relation. Private infrastructure for the
HOL proof (its `IMP_memory_rel_Number`/`memory_rel_insert` steps). -/
theorem divSetSmallNat {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (src : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (dest n : Nat)
    (related : stateRel conf l1 l2 src target none locs) (bound : n < 2 ^ (width - 3)) :
    stateRel conf l1 l2 (DataSem.setVar dest (.number (n : Int)) src)
      (WordSemStateFiniteExact.setVar (adjustVar dest) (.word (BitVec.ofNat width n <<< (2 : Nat))) target)
      none locs := by
  apply stateRel_insertRoot conf l1 l2 src target locs dest (.number (n : Int)) _ related
  rcases related with ⟨_, _, _, _, _, _, good, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩
  exact impMemoryRel_number_num3 conf target.be (holThe src.tstamps) src.refs src.space
    target.store target.memory target.mdomain _ n ⟨good, bound, hmem⟩

/-- Signed division of two non-negative tagged small numbers is their untagged quotient.
Private infrastructure for the HOL proof (`word_quot_def`/`DIV_DIV_DIV_MULT` steps). -/
theorem divTaggedQuot {width : Nat} [NeZero width] (n1 n2 : Nat)
    (b1 : 4 * n1 < 2 ^ width) (b2 : 4 * n2 < 2 ^ width)
    (m1 : ¬ (BitVec.ofNat width (4 * n1)).msb = true) (m2 : ¬ (BitVec.ofNat width (4 * n2)).msb = true) :
    (BitVec.ofNat width (4 * n1)).sdiv (BitVec.ofNat width (4 * n2)) = BitVec.ofNat width (n1 / n2) := by
  simp only [Bool.not_eq_true] at m1 m2
  rw [BitVec.sdiv_eq, m1, m2]
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat width (4 * n1) / BitVec.ofNat width (4 * n2)).toNat = _
  simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2]
  rw [Nat.mul_div_mul_left _ _ (by decide : 0 < 4)]
  exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))).symm

/-- Both long-division stubs are among the compiled stubs (a copy of the private
membership fact in `Bignum/DivCodeAssum.lean`). Private infrastructure. -/
theorem divLongDivStubMembers {width : Nat} [NeZero width] (c : Config) :
    (longDivLocation, 4, longDivCode c) ∈ stubs (width := width) c ∧
    (longDiv1Location, 7, longDiv1Code c) ∈ stubs (width := width) c := by
  simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
      fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
      replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
      divLocation, modLocation, compare1Location, compareLocation, equal1Location,
      equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
      byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
      installLocation, installCodeLocation, installDataLocation, dummyLocation,
      appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
      unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]

/-- A terminating `MustTerminate` body restores the outer clock and depth. Private
infrastructure (copy of the private helper in `Bignum/DivCodeAssum.lean`). -/
theorem divMustTerminateRun {width : Nat} [NeZero width] {C F : Type}
    (s s1 : WordSemStateFiniteExact width C F) (p : WordLangProgHOL (BitVec width))
    (h0 : ¬ s.termdep = 0)
    (h : WordSemStateFiniteExact.evaluate p
      { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } = (none, s1)) :
    WordSemStateFiniteExact.evaluate (.mustTerminate p) s =
      (none, { s1 with clock := s.clock, termdep := s.termdep }) := by
  rw [WordSemStateFiniteExact.evaluate, dif_neg h0, h]

/-- The environment restored after a call equals the cut it saved. Private
infrastructure (as `lessRestoredCuts` in `Less.lean`). -/
theorem divRestoredCuts {width : Nat} [NeZero width] (names : WordLangCutsetsHOL)
    (env first second : Spt (WordLocW width)) (p permute : Nat → Nat → Nat)
    (entries : List (Nat × WordLocW width))
    (cut : wordSemCutEnvs names env = some (first, second))
    (run : wordSemEnvToList second p = (entries, permute)) :
    sptFromAList (sptToAList first) = first ∧ sptFromAList entries = second := by
  have wf := cutEnvs_wf names env first second cut
  constructor
  · apply (sptEqThm _ _ ⟨sptWfFromAList _, wf.1⟩).2
    intro key
    exact sptLookup_sptFromAList_sptToAList key first
  · apply (sptEqThm _ _ ⟨sptWfFromAList _, wf.2⟩).2
    intro key
    rw [sptLookup_sptFromAList]
    exact (wordSemEnvToListLookupEquiv second p entries permute run).1 key

/-- Evaluate the returning call into the long-division stub from its established
premises. Private infrastructure (adapted from `lessDirectCall` in `Less.lean`). -/
theorem divLongDivDirectCall {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (s returned restored : WordSemStateFiniteExact width C F) (names : WordLangCutsetsHOL)
    (first second : Spt (WordLocW width)) (n l A B : Nat) (x y res : BitVec width)
    (args : s.getVars [1, A, B] = some [.word 0, .word x, .word y])
    (code : sptLookup longDivLocation s.code = some (4, longDivCode conf))
    (cut : wordSemCutEnvs names s.locals = some (first, second))
    (live : ¬ sptDomainEmpty names.1) (clock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate (longDivCode conf)
      (WordSemStateFiniteExact.callEnv [.loc n l, .word 0, .word x, .word y]
        (sptLookup longDivLocation s.stackSize)
        (WordSemStateFiniteExact.pushEnv (first, second) none (WordSemStateFiniteExact.decClock s))) =
      (some (.result (.loc n l) [.word res]), returned))
    (pop : WordSemStateFiniteExact.popEnv returned = some restored)
    (domain : sptDomainEqUnion restored.locals first second) :
    WordSemStateFiniteExact.evaluate
      (.call (some ([1], names, .skip, n, l)) (some longDivLocation) [1, A, B] none) s =
      (none, WordSemStateFiniteExact.setVars [1] [.word res] restored) := by
  rw [WordSemStateFiniteExact.evaluate]
  simp only [args, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc,
    wordSemFindCode, code, List.length_cons, live, not_false_eq_true,
    List.nodup_cons, List.mem_nil_iff, cut, clock]
  simp
  rw [WordSemStateFiniteExact.fix_clock_evaluate]
  erw [run]
  simp only [List.length_cons, List.length_nil, not_true_eq_false, false_or, if_false]
  rw [pop]
  simp [domain, WordSemStateFiniteExact.evaluate]

/-- Stack-bound algebra for the long-division stub call: the stub's possible maxima lie
between the caller's used stack and the source bound. Private infrastructure. -/
theorem divCallStackAlgebra (targetMax sourceMax used ld ld1 mx : Option Nat)
    (oldMax : optionLe targetMax sourceMax) (usedMax : optionLe used targetMax)
    (mxCases : mx = Option.map₂ max (Option.map₂ max targetMax used) (Option.map₂ (· + ·) used ld) ∨
      mx = Option.map₂ max (Option.map₂ max (Option.map₂ max targetMax used) (Option.map₂ (· + ·) used ld))
        (Option.map₂ (· + ·) used ld1)) :
    optionLe mx (Option.map₂ max sourceMax (Option.map₂ (· + ·) (Option.map₂ max ld ld1) used)) ∧
      optionLe used mx := by
  rcases mxCases with rfl | rfl <;>
    cases targetMax <;> cases sourceMax <;> cases used <;> cases ld <;> cases ld1 <;>
      simp_all [optionLe] <;> omega

/-- `smallNum` at the related architecture flag is `smallInt` at the word width
(HOL `small_num_small_int`, restated here because its port in `Add.lean` imports
this module). Private infrastructure. -/
theorem divSmallNumEq (width : Nat) [NeZero width] (good : goodDimindex width) (arch : Bool)
    (archEq : arch = true ↔ width = 64) :
    DataSem.smallNum arch = smallInt width := by
  funext i
  rcases good with h | h <;> subst width <;> cases arch <;> simp at archEq <;>
    norm_num [DataSem.smallNum, smallInt]

/-- The common prefix of the division and remainder code: the tag test value. -/
theorem divTagPrefix {width : Nat} [NeZero width] {C F : Type}
    (target : WordSemStateFiniteExact width C F) (a1 a2 : Nat) (x y : BitVec width)
    (fast slow : WordLangProgHOL (BitVec width))
    (hx : target.getVar (adjustVar a1) = some (.word x))
    (hy : target.getVar (adjustVar a2) = some (.word y)) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 1 (.op .or [.var (adjustVar a1), .var (adjustVar a2)]),
      .assign 1 (.op .or [.var 1, shiftVar .lsr 1 (width - 1)]),
      .ite .test 1 (.imm 1) fast slow]) target =
    WordSemStateFiniteExact.evaluate (.ite .test 1 (.imm 1) fast slow)
      ((target.setVar 1 (.word (x ||| y))).setVar 1
        (.word ((x ||| y) ||| ((x ||| y) >>> (width - 1))))) := by
  simp only [wordListSeq]
  rw [divEvalAssignSeq target 1 _ (.word (x ||| y)) _ (by
    simp [WordSemStateFiniteExact.wordExp, theWords, wordOpHOL, wordOp, hx, hy, OrOp.or,
      BitVec.or_zero])]
  rw [divEvalAssignSeq _ 1 _ (.word ((x ||| y) ||| ((x ||| y) >>> (width - 1)))) _ (by
    have h1 : sptLookup 1 (target.setVar 1 (.word (x ||| y))).locals = some (.word (x ||| y)) := by
      simp [WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    simp [WordSemStateFiniteExact.wordExp, theWords, wordOpHOL, wordOp, OrOp.or, BitVec.or_zero,
      Bignum.wordExpShiftVar, h1, SemanticPrimitivesProps.shiftLookup, WordSemStateFiniteExact.getVar])]


/-- The small-operand branch of `assignDiv`, copied from its `let fast`.
Proof infrastructure with no separate HOL declaration. -/
def assignDivFast {width : Nat} [NeZero width] (conf : Config) (secn l dest : Nat)
    (names : Option NumSet) (first second : Nat) : WordLangProgHOL (BitVec width) :=
  if conf.hasDiv then wordListSeq [
      .inst (.arith (.div 1 (adjustVar first) (adjustVar second))),
      .assign (adjustVar dest) (shiftVar .lsl 1 2)]
    else if conf.hasLongdiv then wordListSeq [
      .assign 1 (.const 0), .inst (.arith (.longDiv 1 3 1 (adjustVar first) (adjustVar second))),
      .assign (adjustVar dest) (shiftVar .lsl 1 2)]
    else wordListSeq [
      .assign 1 (.const 0),
      .mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, secn, l + 1))
        (some longDivLocation) [1, adjustVar first, adjustVar second] none),
      .assign (adjustVar dest) (shiftVar .lsl 1 2)]

/-- The bignum branch of `assignDiv`: the `Div_location` stub call and result move.
Proof infrastructure with no separate HOL declaration. -/
def assignDivSlow {width : Nat} [NeZero width] (secn l dest : Nat)
    (names : Option NumSet) (first second : Nat) : WordLangProgHOL (BitVec width) :=
  wordListSeq [
      .mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, secn, l))
        (some divLocation) [adjustVar first, adjustVar second] none),
      .move 2 [(adjustVar dest, 1)]]

/-- `assignDiv` is the tag prefix followed by the two branches above. -/
theorem assignDiv_split {width : Nat} [NeZero width] (conf : Config) (secn l dest : Nat)
    (names : Option NumSet) (first second : Nat) :
    (assignDiv (width := width) conf secn l dest names first second).1 = wordListSeq [
      .assign 1 (.op .or [.var (adjustVar first), .var (adjustVar second)]),
      .assign 1 (.op .or [.var 1, shiftVar .lsr 1 (width - 1)]),
      .ite .test 1 (.imm 1) (assignDivFast conf secn l dest names first second)
        (assignDivSlow secn l dest names first second)] := rfl

/-- The statement of HOL `eval_Call_Arith` (`data_to_word_bignumProofScript.sml`),
rendered from its typed capture `eval_Call_Arith_typed`.  It is untagged: the
theorem itself is being ported separately (via `AnyArith_thm`), and the
division and remainder assignment proofs below take this statement as their
only extra hypothesis until that port lands.  HOL's free variables become the
outer binders, followed by HOL's own `∀ index r`; `get_names names_opt` is
`names.getD .ln`. -/
def EvalCallArithStmt (width : Nat) [NeZero width] (C F : Type) : Prop :=
  ∀ (c : Config) (l1 l2 : Nat) (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (names : Option NumSet) (a1 a2 : Nat) (i1 i2 : Int)
    (x : DataSem.State C F) (dest n l : Nat) (index : Nat) (r : Int),
    Proofs.Gc.stateRel c l1 l2 s t none locs ∧ names ≠ none ∧ 1 < t.termdep ∧
    DataSem.getVars [a1, a2] s.locals = some [.number i1, .number i2] ∧
    DataSem.cutStateOpt names s = some x ∧ Bignum.intOp index i1 i2 = some r →
    ∃ (q : Option (WordSemResult width)) (r' : WordSemStateFiniteExact width C F),
      (match WordSemStateFiniteExact.evaluate
          (.mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, n, l))
            (some (Bignum.arithLocation index)) [adjustVar a1, adjustVar a2] none)) t with
        | (res, s1) =>
          if res = none then
            WordSemStateFiniteExact.evaluate (wordListSeq [.move 2 [(adjustVar dest, 1)]]) s1
          else (res, s1)) = (q, r') ∧
      (let max := wordSemOptionMax s.stackMax
          (wordSemOptionAdd (wordSemStackSize t.stack)
            (wordSemOptionAdd t.localsSize
              (wordSemOptionMax (sptLookup (Bignum.arithLocation index) t.stackSize)
                (WordDepth.maxDepth t.stackSize anyArithCallTree))));
        optionLe r'.stackMax max ∧
        (q = some .notEnoughSpace →
          r'.ffi = s.ffi ∧
          (c.gcKind ≠ .none ∧ DataSem.noThunksInRefs s.refs →
            let il := DataSem.bignumSize s.limits.arch64Bit i1;
            let jl := DataSem.bignumSize s.limits.arch64Bit i2;
            il + jl ≤ 2 ^ c.lenSize →
              s.limits.heapLimit < 2 * il + 2 * jl + DataSem.sizeOfHeapArgs [.number i1, .number i2] x)) ∧
        (q ≠ some .notEnoughSpace →
          Proofs.Gc.stateRel c l1 l2
            { x with locals := sptInsert dest (.number r) x.locals, space := 0, stackMax := max }
            r' none locs ∧ q = none))

open Classical in
/-- Draft of HOL `assign_Div` under `EvalCallArithStmt`. -/
theorem assignDiv_correct {width : Nat} [NeZero width] {C F : Type}
    (evalCallArith : EvalCallArithStmt width C F)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .intOp .div)
    (related : Proofs.Gc.stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        Proofs.Gc.stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  subst op
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some names =>
    obtain ⟨wordCut, words, cutWord, getWord, lens1, lens2, relCut, relCutWord⟩ :=
      stateRel_cutStateOpt_some conf l1 l2 source target locs args values names cut ⟨related, argsEq, cutEq⟩
    obtain ⟨a, b, next, valuesEq, bne, spaceEq, resultEq, stateEq⟩ := divSource values cut resultState result run
    subst values result resultState
    obtain ⟨a1, a2, rfl⟩ : ∃ a1 a2, args = [a1, a2] := by
      match args, lens1 with
      | [a1, a2], _ => exact ⟨a1, a2, rfl⟩
    obtain ⟨v1, v2, rfl⟩ : ∃ v1 v2, words = [v1, v2] := by
      match words, lens2 with
      | [v1, v2], _ => exact ⟨v1, v2, rfl⟩
    have sread : DataSem.getVar a1 source.locals = some (.number a) ∧
        DataSem.getVar a2 source.locals = some (.number b) := by
      simp only [DataSem.getVars, DataSem.getVar] at argsEq ⊢
      revert argsEq
      cases h1 : sptLookup a1 source.locals <;> cases h2 : sptLookup a2 source.locals <;> simp
    have tread : sptLookup (adjustVar a1) target.locals = some v1 ∧
        sptLookup (adjustVar a2) target.locals = some v2 := by
      simp only [List.map, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar] at getWord
      revert getWord
      cases h1 : sptLookup (adjustVar a1) target.locals <;>
        cases h2 : sptLookup (adjustVar a2) target.locals <;> simp
    obtain ⟨x, rfl, xSmall, xNat⟩ := stateRel_numberImp conf l1 l2 source target locs a1 a v1 related sread.1 tread.1
    obtain ⟨y, rfl, ySmall, yNat⟩ := stateRel_numberImp conf l1 l2 source target locs a2 b v2 related sread.2 tread.2
    have hx : target.getVar (adjustVar a1) = some (.word x) := tread.1
    have hy : target.getVar (adjustVar a2) = some (.word y) := tread.2
    let tag := (x ||| y) ||| ((x ||| y) >>> (width - 1))
    let t2 := (target.setVar 1 (.word (x ||| y))).setVar 1 (.word tag)
    have prefixEval := divTagPrefix target a1 a2 x y
      (assignDivFast conf n l dest (some names) a1 a2)
      (assignDivSlow n l dest (some names) a1 a2) hx hy
    have compiled : (compileAssign conf n l dest (.intOp .div) [a1, a2] (some names)).1 =
        (assignDiv (width := width) conf n l dest (some names) a1 a2).1 := by
      simp [compileAssign, arg2]
    have get1 : t2.getVar 1 = some (.word tag) := by
      simp [t2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
    have rel2 : stateRel conf l1 l2 source t2 none locs := by
      have h1 := (stateRel_insertOdd conf l1 l2 source target none locs 1 (.word (x ||| y)) rfl).symm ▸ related
      exact (stateRel_insertOdd conf l1 l2 source (target.setVar 1 (.word (x ||| y))) none locs 1
        (.word tag) rfl).symm ▸ h1
    by_cases fastTag : tag &&& 1 = 0
    · obtain ⟨x0, y0, xm, ym⟩ := divTagZero_inv x y fastTag
      obtain ⟨a0, xEq⟩ := xNat ⟨xm, x0⟩
      obtain ⟨b0, yEq⟩ := yNat ⟨ym, y0⟩
      have sa : smallInt width a := xSmall.mp x0
      have sb : smallInt width b := ySmall.mp y0
      have good : goodDimindex width := related.2.2.2.2.2.2.1
      obtain ⟨n1, rfl⟩ : ∃ n1 : Nat, a = n1 := ⟨a.toNat, (Int.toNat_of_nonneg a0).symm⟩
      obtain ⟨n2, rfl⟩ : ∃ n2 : Nat, b = n2 := ⟨b.toNat, (Int.toNat_of_nonneg b0).symm⟩
      simp only [Int.toNat_natCast] at xEq yEq
      have n2pos : 0 < n2 := by omega
      have bound1 : n1 < 2 ^ (width - 3) := by
        rcases good with h | h <;> subst h <;> simp [smallInt] at sa <;> omega
      have bound2 : n2 < 2 ^ (width - 3) := by
        rcases good with h | h <;> subst h <;> simp [smallInt] at sb <;> omega
      have b1 : 4 * n1 < 2 ^ width := by
        rcases good with h | h <;> subst h <;> simp at bound1 ⊢ <;> omega
      have b2 : 4 * n2 < 2 ^ width := by
        rcases good with h | h <;> subst h <;> simp at bound2 ⊢ <;> omega
      have qEq : (n1 : Int).fdiv (n2 : Int) = ((n1 / n2 : Nat) : Int) := by
        simp [Int.fdiv_eq_ediv_of_nonneg]
      have qBound : n1 / n2 < 2 ^ (width - 3) := lt_of_le_of_lt (Nat.div_le_self _ _) bound1
      have nextRel : stateRel conf l1 l2 next target none locs := by
        simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
        subst next
        rcases relCut with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
          htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
        refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
          hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
        exact memoryRel_zeroSpace conf target.be (holThe cut.tstamps) cut.refs
          cut.space target.store target.memory target.mdomain _ hmem
      let src := DataSem.doStack (.intOp .div) [.number (n1 : Int), .number (n2 : Int)]
        (DataSem.doLimSafe next (.intOp .div) [.number (n1 : Int), .number (n2 : Int)])
      have srcRel : stateRel conf l1 l2 src target none locs :=
        stateRel_doStack conf l1 l2 _ target locs _ _
          (stateRel_doLimSafe conf l1 l2 next target locs _ _ nextRel)
      have srcRel2 : stateRel conf l1 l2 src t2 none locs := by
        have h1 := (stateRel_insertOdd conf l1 l2 src target none locs 1 (.word (x ||| y)) rfl).symm ▸ srcRel
        exact (stateRel_insertOdd conf l1 l2 src (target.setVar 1 (.word (x ||| y))) none locs 1
          (.word tag) rfl).symm ▸ h1
      have testTrue : wordSemWordCmp .test (.word tag) (.word (1 : BitVec width)) = some true := by
        simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
        change (tag &&& (1 : BitVec width) == 0) = true
        exact beq_iff_eq.mpr fastTag
      have iteEval : WordSemStateFiniteExact.evaluate
          (.ite .test 1 (.imm 1) (assignDivFast conf n l dest (some names) a1 a2)
            (assignDivSlow n l dest (some names) a1 a2)) t2 =
          WordSemStateFiniteExact.evaluate (assignDivFast conf n l dest (some names) a1 a2) t2 := by
        rw [WordSemStateFiniteExact.evaluate, get1]
        simp only [WordSemStateFiniteExact.getVarImm, testTrue]
      suffices key : ∃ T : WordSemStateFiniteExact width C F,
          WordSemStateFiniteExact.evaluate (assignDivFast conf n l dest (some names) a1 a2) t2 =
            (none, T.setVar (adjustVar dest) (.word (BitVec.ofNat width (n1 / n2) <<< (2 : Nat)))) ∧
          stateRel conf l1 l2 src T none locs by
        obtain ⟨T, evalT, relT⟩ := key
        refine ⟨none, T.setVar (adjustVar dest) (.word (BitVec.ofNat width (n1 / n2) <<< (2 : Nat))),
          ?_, by simp, fun _ => ⟨?_, rfl⟩⟩
        · rw [compiled, assignDiv_split, prefixEval, iteEval, evalT]
        · rw [qEq]
          exact divSetSmallNat conf l1 l2 src T locs dest (n1 / n2) relT qBound
      have t2read : ∀ k, k ≠ 1 → sptLookup k t2.locals = sptLookup k target.locals := by
        intro k hk
        simp [t2, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ hk]
      have adj1 : adjustVar a1 ≠ 1 := by simp [adjustVar]
      have adj2 : adjustVar a2 ≠ 1 := by simp [adjustVar]
      have yNe : (BitVec.ofNat width (4 * n2) : BitVec width) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt b2] at this
        omega
      have quot := divTaggedQuot n1 n2 b1 b2 (xEq ▸ xm) (yEq ▸ ym)
      let q : BitVec width := BitVec.ofNat width (n1 / n2)
      have shiftStore : ∀ s1 : WordSemStateFiniteExact width C F,
          sptLookup 1 s1.locals = some (.word q) →
          WordSemStateFiniteExact.evaluate (.assign (adjustVar dest) (shiftVar .lsl 1 2)) s1 =
            (none, s1.setVar (adjustVar dest) (.word (q <<< (2 : Nat)))) := by
        intro s1 h1
        simp [WordSemStateFiniteExact.evaluate, Bignum.wordExpShiftVar, h1,
          SemanticPrimitivesProps.shiftLookup]
      by_cases hd : conf.hasDiv
      · refine ⟨t2.setVar 1 (.word q), ?_, ?_⟩
        · have instRun : WordSemStateFiniteExact.inst
              (.arith (.div 1 (adjustVar a1) (adjustVar a2))) t2 = some (t2.setVar 1 (.word q)) := by
            simp [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
              WordSemStateFiniteExact.getVar, t2read _ adj1, t2read _ adj2, tread.1, tread.2, xEq, yEq,
              quot, q]
            exact yNe
          have instEval : WordSemStateFiniteExact.evaluate
              (.inst (.arith (.div 1 (adjustVar a1) (adjustVar a2)))) t2 = (none, t2.setVar 1 (.word q)) := by
            rw [WordSemStateFiniteExact.evaluate, instRun]
          simp only [assignDivFast, hd, if_true, wordListSeq]
          rw [divEvalSeq, instEval]
          exact shiftStore _ (by simp [WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same])
        · exact (stateRel_insertOdd conf l1 l2 src t2 none locs 1 (.word q) rfl).symm ▸ srcRel2
      by_cases hl : conf.hasLongdiv
      · let s0 := t2.setVar 1 (.word (0 : BitVec width))
        let rem : BitVec width := BitVec.ofNat width (4 * n1 % (4 * n2))
        have qNat : 4 * n1 / (4 * n2) = n1 / n2 := Nat.mul_div_mul_left _ _ (by decide)
        have qLt : n1 / n2 < 2 ^ width := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
        refine ⟨(s0.setVar 3 (.word rem)).setVar 1 (.word q), ?_, ?_⟩
        · have s0read : ∀ k, k ≠ 1 → sptLookup k s0.locals = sptLookup k target.locals := by
            intro k hk
            simp [s0, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ hk, ← t2read _ hk]
          have instRun : WordSemStateFiniteExact.inst
              (.arith (.longDiv 1 3 1 (adjustVar a1) (adjustVar a2))) s0 =
              some ((s0.setVar 3 (.word rem)).setVar 1 (.word q)) := by
            have s01 : sptLookup 1 s0.locals = some (.word (0 : BitVec width)) := by
              simp [s0, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
            simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
              WordSemStateFiniteExact.getVar, s0read _ adj1, s0read _ adj2, tread.1, tread.2, s01]
            have d0 : (BitVec.ofNat width (4 * n2)).toNat ≠ 0 := by
              simp [Nat.mod_eq_of_lt b2]; omega
            simp [xEq, yEq, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, qNat, qLt, rem, q,
              WordSemStateFiniteExact.setVar]
            omega
          have assign0 : WordSemStateFiniteExact.evaluate (.assign 1 (.const 0)) t2 = (none, s0) := by
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, s0]
          have instEval : WordSemStateFiniteExact.evaluate
              (.inst (.arith (.longDiv 1 3 1 (adjustVar a1) (adjustVar a2)))) s0 =
              (none, (s0.setVar 3 (.word rem)).setVar 1 (.word q)) := by
            rw [WordSemStateFiniteExact.evaluate, instRun]
          simp only [assignDivFast, hd, hl, if_true, if_false, Bool.false_eq_true, wordListSeq]
          rw [divEvalSeq, assign0]
          simp only
          rw [divEvalSeq, instEval]
          exact shiftStore _ (by simp [WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same])
        · have r0 := (stateRel_insertOdd conf l1 l2 src t2 none locs 1 (.word 0) rfl).symm ▸ srcRel2
          have r3 := (stateRel_insertOdd conf l1 l2 src s0 none locs 3 (.word rem) rfl).symm ▸ r0
          exact (stateRel_insertOdd conf l1 l2 src (s0.setVar 3 (.word rem)) none locs 1 (.word q) rfl).symm ▸ r3
      · let s0 := t2.setVar 1 (.word (0 : BitVec width))
        let rem : BitVec width := BitVec.ofNat width (4 * n1 % (4 * n2))
        have qNat : 4 * n1 / (4 * n2) = n1 / n2 := Nat.mul_div_mul_left _ _ (by decide)
        obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
          cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
        let initial := {s0 with clock := wordSemMustTerminateLimit width, termdep := s0.termdep - 1}
        let entry := WordSemStateFiniteExact.callEnv [.loc n (l + 1), .word 0, .word x, .word y]
          (sptLookup longDivLocation target.stackSize)
          (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
        have members := divLongDivStubMembers (width := width) conf
        have code0 : sptLookup longDivLocation target.code = some (4, longDivCode conf) :=
          related.2.2.2.2.1.2.1 _ members.1
        have code1 : sptLookup longDiv1Location target.code = some (7, longDiv1Code conf) :=
          related.2.2.2.2.1.2.1 _ members.2
        have clockBound : 2 ^ width < wordSemMustTerminateLimit width - 1 :=
          dimwordLessMustTerminateLimit width good
        have pre : Misc.Multiword.singleDivPre (0 : BitVec width) x y := by
          refine ⟨by rw [yEq]; exact yNe, ?_⟩
          simp [xEq, yEq, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, qNat]
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
        have sdiv : Misc.Multiword.singleDiv (0 : BitVec width) x y = (q, rem) := by
          simp [Misc.Multiword.singleDiv, xEq, yEq, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, qNat, q, rem]
        obtain ⟨ck, mx, stubEval, mxCases⟩ := Bignum.evaluateLongDivCode' entry n (l + 1) conf ()
          0 x y q rem ⟨pre, sdiv,
            by simpa [entry, initial, s0, t2, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
              WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.setVar] using code1,
            by simp [entry, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
            by simp [entry, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
            by simp [entry, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
            by simp [entry, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
            by simp [entry, initial, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
              WordSemStateFiniteExact.decClock]; omega,
            good⟩
        cases envEq : wordSemEnvToList cutSecond target.permute with
        | mk entries permute =>
          obtain ⟨firstRestored, secondRestored⟩ :=
            divRestoredCuts (adjustSets names) target.locals cutFirst cutSecond target.permute permute
              entries cutPair envEq
          let returned := {entry with clock := ck, locals := .ln, localsSize := some 0, store := entry.store.updateEq (.temp 28, .word rem), stackMax := mx}
          let restored := {returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList cutFirst)), stack := target.stack, localsSize := target.localsSize}
          have popRun : WordSemStateFiniteExact.popEnv returned = some restored := by
            simp only [returned, restored, entry, WordSemStateFiniteExact.callEnv,
              WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.popEnv,
              WordSemStateFiniteExact.decClock, initial, s0, t2, WordSemStateFiniteExact.setVar, envEq]
          have domain : sptDomainEqUnion restored.locals cutFirst cutSecond := by
            intro key
            change sptMem key (sptUnion (sptFromAList entries) (sptFromAList (sptToAList cutFirst))) ↔ _
            rw [secondRestored, firstRestored, sptMem_sptUnion]
            exact or_comm
          have cutAt : wordSemCutEnvs (adjustSets names) initial.locals = some (cutFirst, cutSecond) := by
            simpa [initial, s0, t2, WordSemStateFiniteExact.setVar, cutEnvs_adjustSets_insertOdd] using cutPair
          have argsAt : initial.getVars [1, adjustVar a1, adjustVar a2] = some [.word 0, .word x, .word y] := by
            have r1 : sptLookup (adjustVar a1) initial.locals = some (.word x) := by
              simp only [initial, s0, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ adj1]
              rw [t2read _ adj1]; exact tread.1
            have r2 : sptLookup (adjustVar a2) initial.locals = some (.word y) := by
              simp only [initial, s0, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ adj2]
              rw [t2read _ adj2]; exact tread.2
            have r0 : sptLookup 1 initial.locals = some (.word (0 : BitVec width)) := by
              simp [initial, s0, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
            simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, r0, r1, r2]
          have neClock : initial.clock ≠ 0 := by
            change wordSemMustTerminateLimit width ≠ 0
            omega
          have namesNonempty : ¬sptDomainEmpty (adjustSets names).1 := by
            intro empty
            have absent := empty 0
            exact absent ((sptMem_iff_lookup 0 _).mpr ⟨(), rfl⟩)
          have callRun : WordSemStateFiniteExact.evaluate
              (.call (some ([1], adjustSets names, .skip, n, l + 1)) (some longDivLocation)
                [1, adjustVar a1, adjustVar a2] none) initial =
              (none, WordSemStateFiniteExact.setVars [1] [.word q] restored) := by
            refine divLongDivDirectCall conf initial returned restored (adjustSets names) cutFirst cutSecond
              n (l + 1) _ _ x y q argsAt ?_ cutAt namesNonempty neClock ?_ popRun domain
            · change sptLookup longDivLocation target.code = _
              exact code0
            · change WordSemStateFiniteExact.evaluate (longDivCode conf) entry =
                (some (.result (.loc n (l + 1)) [.word q]), returned) at stubEval
              exact stubEval
          let T := {WordSemStateFiniteExact.setVars [1] [.word q] restored with clock := s0.clock, termdep := s0.termdep}
          have termNe : ¬ s0.termdep = 0 := by
            change ¬ target.termdep = 0
            omega
          have wrapped := divMustTerminateRun s0 _ _ termNe callRun
          have assign0 : WordSemStateFiniteExact.evaluate (.assign 1 (.const 0)) t2 = (none, s0) := by
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, s0]
          refine ⟨T, ?_, ?_⟩
          · simp only [assignDivFast, hd, hl, if_false, Bool.false_eq_true, Option.getD_some, wordListSeq]
            rw [divEvalSeq, assign0]
            simp only
            rw [divEvalSeq, wrapped]
            exact shiftStore _ (by
              simp [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
                sptLookup_sptInsert_same])
          · -- the source stack bound in the small-operand case
            have archEq : source.limits.arch64Bit = true ↔ width = 64 := by
              have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              rw [limits.2.2.1]
              simp
            have smallEq := divSmallNumEq width good source.limits.arch64Bit archEq
            have cutFields := cutStateOpt_some_eq names source cut cutEq
            have cutLimits : cut.limits = source.limits := by rw [cutFields]
            have nextFields : next.stackFrameSizes = cut.stackFrameSizes ∧ next.stack = cut.stack ∧
                next.localsSize = cut.localsSize ∧ next.stackMax = cut.stackMax ∧ next.limits = cut.limits := by
              simp only [DataSem.doSpace, DataLang.opSpaceReset, if_true, Option.some.injEq] at spaceEq
              subst next
              exact ⟨rfl, rfl, rfl, rfl, rfl⟩
            have cond : DataSem.smallNum next.limits.arch64Bit (n1 : Int) ∧ 0 ≤ (n1 : Int) ∧
                DataSem.smallNum next.limits.arch64Bit (n2 : Int) ∧ 0 ≤ (n2 : Int) ∧
                DataSem.smallNum next.limits.arch64Bit (holIntDiv (n1 : Int) (n2 : Int)) := by
              rw [nextFields.2.2.2.2, cutLimits, smallEq, holIntDiv_ofNat_ofNat _ _ n2pos]
              refine ⟨sa, by omega, sb, by omega, ?_⟩
              generalize n1 / n2 = k at qBound ⊢
              rcases good with h | h <;> subst h <;> simp only [smallInt] <;> constructor <;>
                simp at qBound ⊢ <;> omega
            have stackSizeEq := stackRel_sizeOfStack relCut.2.2.2.2.2.2.2.2.2.2.2.2.1
            have frameSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            have localSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            have oldMax : optionLe target.stackMax cut.stackMax := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            let used := Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize
            have oldUsage : optionLe used target.stackMax := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            have srcMaxEq : src.stackMax = Option.map₂ max cut.stackMax
                (Option.map₂ (· + ·) (Option.map₂ max (sptLookup longDivLocation target.stackSize)
                  (sptLookup longDiv1Location target.stackSize)) used) := by
              simp only [src, DataSem.doStack, DataSem.doLimSafe, DataSem.stackConsumed, if_pos cond,
                nextFields.1, nextFields.2.1, nextFields.2.2.1, nextFields.2.2.2.1]
              rw [← frameSizeEq, ← localSizeEq, ← stackSizeEq]
            have optMax (a b : Option Nat) : wordSemOptionMax a b = Option.map₂ max a b := by
              cases a <;> cases b <;> rfl
            have optAdd (a b : Option Nat) : wordSemOptionAdd a b = Option.map₂ (· + ·) a b := by
              cases a <;> cases b <;> rfl
            have swapUsed : wordSemOptionAdd target.localsSize (wordSemStackSize target.stack) = used := by
              cases hlocal : target.localsSize <;> cases hstack : wordSemStackSize target.stack <;>
                simp [used, wordSemOptionAdd, hlocal, hstack, Nat.add_comm]
            have entryStack : wordSemStackSize entry.stack = used := by
              simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                WordSemStateFiniteExact.decClock, initial, s0, t2, WordSemStateFiniteExact.setVar, envEq,
                wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame]
              exact swapUsed
            have entryMaxEq : entry.stackMax = Option.map₂ max (Option.map₂ max target.stackMax used)
                (Option.map₂ (· + ·) used (sptLookup longDivLocation target.stackSize)) := by
              simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                WordSemStateFiniteExact.decClock, initial, s0, t2, WordSemStateFiniteExact.setVar, envEq,
                wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame]
              change wordSemOptionMax
                (wordSemOptionMax target.stackMax (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack)))
                (wordSemOptionAdd (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack))
                  (sptLookup longDivLocation target.stackSize)) = _
              rw [swapUsed]
              simp only [optMax, optAdd]
            have entrySize : entry.stackSize = target.stackSize := by
              simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                WordSemStateFiniteExact.decClock, initial, s0, t2, WordSemStateFiniteExact.setVar]
            obtain ⟨bound, usedBelow⟩ := divCallStackAlgebra target.stackMax cut.stackMax used
              (sptLookup longDivLocation target.stackSize) (sptLookup longDiv1Location target.stackSize) mx
              oldMax oldUsage (by
                rcases mxCases with h | h
                · exact Or.inl (h.trans entryMaxEq)
                · refine Or.inr ?_
                  rw [h, entryMaxEq, entryStack, entrySize])
            rw [← srcMaxEq] at bound
            -- relation for the cut target, then the stub's stack bound, store and result register
            have cutNextRel : stateRel conf l1 l2 next {target with locals := wordCut} none locs := by
              simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
              subst next
              rcases relCutWord with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
                htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
              refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
                hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
              exact memoryRel_zeroSpace conf target.be (holThe cut.tstamps) cut.refs
                cut.space target.store target.memory target.mdomain _ hmem
            have preRel : stateRel conf l1 l2 src {target with locals := wordCut} none locs :=
              stateRel_doStack conf l1 l2 _ _ locs _ _
                (stateRel_doLimSafe conf l1 l2 next _ locs _ _ cutNextRel)
            have returnedRel : stateRel conf l1 l2 src
                {target with locals := wordCut, stackMax := mx} none locs := by
              rcases preRel with ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, _, _, p, q, r, s⟩
              exact ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, usedBelow, bound, p, q, r, s⟩
            have tempRel := (Bignum.stateRel_setStore_temp conf l1 l2 src 28 (.word rem)
              {target with locals := wordCut, stackMax := mx} none locs).mpr returnedRel
            have finalRel := (stateRel_insertOdd conf l1 l2 src
              (WordSemStateFiniteExact.setStore (.temp 28) (.word rem) {target with locals := wordCut, stackMax := mx})
              none locs 1 (.word q) rfl).symm ▸ tempRel
            let X := WordSemStateFiniteExact.setStore (.temp 28) (.word rem)
              {target with locals := wordCut, stackMax := mx}
            have normalized : {T with permute := target.permute} =
                {X with locals := sptInsert 1 (.word q) X.locals} := by
              simp only [T, X, restored, returned, entry, WordSemStateFiniteExact.callEnv,
                WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, initial, s0, t2,
                WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setStore,
                LoopSemStateFiniteExact.sptAlistInsert, envEq, secondRestored, firstRestored, ← cutUnion]
            have normRel : stateRel conf l1 l2 src {T with permute := target.permute} none locs :=
              normalized ▸ finalRel
            exact normRel
    · have testFalse : wordSemWordCmp .test (.word tag) (.word (1 : BitVec width)) = some false := by
        simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
        change (tag &&& (1 : BitVec width) == 0) = false
        exact beq_eq_false_iff_ne.mpr fastTag
      have iteEval : WordSemStateFiniteExact.evaluate
          (.ite .test 1 (.imm 1) (assignDivFast conf n l dest (some names) a1 a2)
            (assignDivSlow n l dest (some names) a1 a2)) t2 =
          WordSemStateFiniteExact.evaluate (assignDivSlow n l dest (some names) a1 a2) t2 := by
        rw [WordSemStateFiniteExact.evaluate, get1]
        simp only [WordSemStateFiniteExact.getVarImm, testFalse]
      have loc5 : Bignum.arithLocation 5 = divLocation := by simp [Bignum.arithLocation]
      have intOp5 : Bignum.intOp 5 a b = some (a.fdiv b) := by simp [Bignum.intOp, bne]
      obtain ⟨q, r', runEq, rest⟩ := evalCallArith conf l1 l2 source t2 locs (some names) a1 a2 a b cut
        dest n l 5 (a.fdiv b) ⟨rel2, by simp, by simpa [t2, WordSemStateFiniteExact.setVar] using depth,
          argsEq, cutEq, intOp5⟩
      rw [loc5] at runEq rest
      have progEval : WordSemStateFiniteExact.evaluate
          (compileAssign conf n l dest (.intOp .div) [a1, a2] (some names)).1 target = (q, r') := by
        rw [compiled, assignDiv_split, prefixEval, iteEval, assignDivSlow]
        simp only [wordListSeq, Option.getD_some] at runEq ⊢
        rw [divEvalSeq]
        exact (divSeqIfMatch _ _).trans runEq
      have good : goodDimindex width := related.2.2.2.2.2.2.1
      have archEq : source.limits.arch64Bit = true ↔ width = 64 := by
        have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        rw [limits.2.2.1]
        simp
      have smallEq := divSmallNumEq width good source.limits.arch64Bit archEq
      let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
        flatStack source.stack target.stack
      have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
        target.store target.memory target.mdomain target envs [a1, a2] [.number a, .number b]
        [.word x, .word y] (by
          refine ⟨?_, argsEq, getWord⟩
          simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      have notCond : ¬ (DataSem.smallNum source.limits.arch64Bit a ∧ 0 ≤ a ∧
          DataSem.smallNum source.limits.arch64Bit b ∧ 0 ≤ b ∧
          DataSem.smallNum source.limits.arch64Bit (holIntDiv a b)) := by
        rw [smallEq]
        rintro ⟨sa, na, sb, nb, -⟩
        apply fastTag
        have mx := memoryRel_numberWordMsb conf target.be (holThe source.tstamps) source.refs
          source.space target.store target.memory target.mdomain a x _ ⟨by simpa using roots, good, sa⟩
        have my := memoryRel_numberWordMsb conf target.be (holThe source.tstamps) source.refs
          source.space target.store target.memory target.mdomain b y _
          ⟨memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ (by simpa using roots), good, sb⟩
        exact divTagZero x y (xSmall.mpr sa) (ySmall.mpr sb) (by rw [mx]; omega) (by rw [my]; omega)
      have cutFields := cutStateOpt_some_eq names source cut cutEq
      have cutSame : cut.stackMax = source.stackMax ∧ cut.limits = source.limits ∧
          cut.refs = source.refs ∧ cut.stack = source.stack ∧ cut.localsSize = source.localsSize ∧
          cut.stackFrameSizes = source.stackFrameSizes ∧ cut.ffi = source.ffi := by
        rw [cutFields]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have nextFields : next.stackFrameSizes = cut.stackFrameSizes ∧ next.stack = cut.stack ∧
          next.localsSize = cut.localsSize ∧ next.stackMax = cut.stackMax ∧ next.limits = cut.limits ∧
          next.refs = cut.refs ∧ next.locals = cut.locals ∧ next.ffi = cut.ffi ∧
          next.safeForSpace = (cut.safeForSpace && decide (DataSem.noThunksInRefs cut.refs ∧
            DataSem.sizeOfHeapArgs [.number a, .number b] cut +
              DataSem.spaceConsumed cut (.intOp .div) [.number a, .number b] ≤ cut.limits.heapLimit)) := by
        simp only [DataSem.doSpace, DataLang.opSpaceReset, if_true, Option.some.injEq] at spaceEq
        subst next
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have stackSizeEq := stackRel_sizeOfStack relCut.2.2.2.2.2.2.2.2.2.2.2.2.1
      have frameSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have localSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have notCondCut : ¬ (DataSem.smallNum cut.limits.arch64Bit a ∧ 0 ≤ a ∧
          DataSem.smallNum cut.limits.arch64Bit b ∧ 0 ≤ b ∧
          DataSem.smallNum cut.limits.arch64Bit (holIntDiv a b)) := by
        rw [cutSame.2.1]; exact notCond
      dsimp only at rest
      obtain ⟨maxLe, nesCase, okCase⟩ := rest
      have maxEq : (DataSem.doStack (.intOp .div) [.number a, .number b]
          (DataSem.doLimSafe next
            (.intOp .div) [.number a, .number b])).stackMax =
          wordSemOptionMax source.stackMax (wordSemOptionAdd (wordSemStackSize t2.stack)
            (wordSemOptionAdd t2.localsSize (wordSemOptionMax (sptLookup divLocation t2.stackSize)
              (WordDepth.maxDepth t2.stackSize anyArithCallTree)))) := by
        simp only [DataSem.doStack, DataSem.doLimSafe, nextFields.1, nextFields.2.1, nextFields.2.2.1,
          nextFields.2.2.2.1, nextFields.2.2.2.2.1, DataSem.stackConsumed, if_neg notCondCut]
        simp only [t2, WordSemStateFiniteExact.setVar]
        rw [stackSizeEq, localSizeEq, frameSizeEq, cutSame.1]
        generalize sptLookup divLocation cut.stackFrameSizes = A
        generalize WordDepth.maxDepth cut.stackFrameSizes anyArithCallTree = B
        generalize DataSem.sizeOfStack cut.stack = S
        generalize cut.localsSize = L
        generalize source.stackMax = M
        cases A <;> cases B <;> cases S <;> cases L <;> cases M
        all_goals simp [wordSemOptionMax, wordSemOptionAdd]
        all_goals omega
      refine ⟨q, r', progEval, ?_, ?_⟩
      · intro hq
        obtain ⟨ffiEq, heapBound⟩ := nesCase hq
        refine ⟨ffiEq.trans related.1.symm, ?_, ?_⟩
        · rw [maxEq]; exact maxLe
        · intro gc
          have lenEq : source.limits.lengthLimit = conf.lenSize :=
            (related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2.1
          have spaceEq' : DataSem.spaceConsumed cut (.intOp .div) [.number a, .number b] =
              2 * DataSem.bignumSize cut.limits.arch64Bit a + 2 * DataSem.bignumSize cut.limits.arch64Bit b := by
            simp only [DataSem.spaceConsumed, if_neg notCondCut]
            rfl
          cases hsafe : (DataSem.doStack (.intOp .div) [.number a, .number b]
              (DataSem.doLimSafe next (.intOp .div) [.number a, .number b])).safeForSpace with
          | false => rfl
          | true =>
            exfalso
            simp only [DataSem.doStack, DataSem.doLimSafe, nextFields.2.2.2.2.2.2.2.2, nextFields.2.2.2.2.1,
              DataSem.limSafe, if_neg notCondCut, Bool.and_eq_true, decide_eq_true_eq] at hsafe
            obtain ⟨⟨lim, -, thunks, heap⟩, -⟩ := hsafe
            rw [cutSame.2.1, lenEq] at lim
            have bound := heapBound ⟨gc, cutSame.2.2.1 ▸ thunks⟩
            rw [spaceEq', cutSame.2.1] at heap
            have := bound lim
            omega
      · intro hq
        obtain ⟨relOk, qNone⟩ := okCase hq
        refine ⟨?_, qNone⟩
        obtain ⟨sf, pk, rfl⟩ : ∃ sf pk, next = { cut with space := 0, safeForSpace := sf, peakHeapLength := pk } := by
          simp only [DataSem.doSpace, DataLang.opSpaceReset, if_true, Option.some.injEq] at spaceEq
          exact ⟨_, _, spaceEq.symm⟩
        rw [← maxEq] at relOk
        exact relOk

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
