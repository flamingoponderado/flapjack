module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Div

@[expose] public section

/-! The data-to-word remainder assignment proof, drafted against `EvalCallArithStmt`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The small-operand branch of `assignMod`, copied from its `let fast`.
Proof infrastructure with no separate HOL declaration. -/
def assignModFast {width : Nat} [NeZero width] (conf : Config) (secn l dest : Nat)
    (names : Option NumSet) (first second : Nat) : WordLangProgHOL (BitVec width) :=
  if conf.hasDiv then wordListSeq [
      .inst (.arith (.div 1 (adjustVar first) (adjustVar second))),
      .inst (.arith (.longMul 3 1 1 (adjustVar second))),
      .assign (adjustVar dest) (.op .sub [.var (adjustVar first), .var 1])]
    else if conf.hasLongdiv then wordListSeq [
      .assign 1 (.const 0), .inst (.arith (.longDiv 1 3 1 (adjustVar first) (adjustVar second))),
      .move 2 [(adjustVar dest, 3)]]
    else wordListSeq [
      .assign 1 (.const 0),
      .mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, secn, l + 1))
        (some longDivLocation) [1, adjustVar first, adjustVar second] none),
      .get (adjustVar dest) (.temp 28)]

/-- The bignum branch of `assignMod`: the `Mod_location` stub call and result move.
Proof infrastructure with no separate HOL declaration. -/
def assignModSlow {width : Nat} [NeZero width] (secn l dest : Nat)
    (names : Option NumSet) (first second : Nat) : WordLangProgHOL (BitVec width) :=
  wordListSeq [
      .mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, secn, l))
        (some modLocation) [adjustVar first, adjustVar second] none),
      .move 2 [(adjustVar dest, 1)]]

/-- `assignMod` is the tag prefix followed by the two branches above. -/
theorem assignMod_split {width : Nat} [NeZero width] (conf : Config) (secn l dest : Nat)
    (names : Option NumSet) (first second : Nat) :
    (assignMod (width := width) conf secn l dest names first second).1 = wordListSeq [
      .assign 1 (.op .or [.var (adjustVar first), .var (adjustVar second)]),
      .assign 1 (.op .or [.var 1, shiftVar .lsr 1 (width - 1)]),
      .ite .test 1 (.imm 1) (assignModFast conf secn l dest names first second)
        (assignModSlow secn l dest names first second)] := rfl

/-- Four times a word-sized number is that number shifted left by two. Private infrastructure. -/
theorem modTimesFour {width : Nat} [NeZero width] (m : Nat) (h : 4 * m < 2 ^ width) :
    BitVec.ofNat width (4 * m) = BitVec.ofNat width m <<< (2 : Nat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : m < 2 ^ width), Nat.mod_eq_of_lt h]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- The long-division remainder of two tagged naturals is the tagged remainder.
Private infrastructure. -/
theorem modRemWord {width : Nat} [NeZero width] (n1 n2 : Nat) (b1 : 4 * n1 < 2 ^ width) (_n2pos : 0 < n2) :
    BitVec.ofNat width (4 * n1 % (4 * n2)) = BitVec.ofNat width (n1 % n2) <<< (2 : Nat) := by
  rw [Nat.mul_mod_mul_left]
  exact modTimesFour _ (lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mod_le _ _)) b1)

/-- Subtracting the tagged quotient-times-divisor leaves the tagged remainder.
Private infrastructure. -/
theorem modSubWord {width : Nat} [NeZero width] (n1 n2 : Nat) (b1 : 4 * n1 < 2 ^ width) (n2pos : 0 < n2) :
    BitVec.ofNat width (4 * n1) - BitVec.ofNat width (n1 / n2 * (4 * n2)) =
      BitVec.ofNat width (n1 % n2) <<< (2 : Nat) := by
  have dm := Nat.mod_add_div n1 n2
  have le : n1 / n2 * (4 * n2) ≤ 4 * n1 := by
    rw [Nat.mul_comm (n1 / n2) (4 * n2)]
    have := Nat.mul_div_le n1 n2
    nlinarith
  rw [← modRemWord n1 n2 b1 n2pos, Nat.mul_mod_mul_left]
  have r : 4 * (n1 % n2) = 4 * n1 - n1 / n2 * (4 * n2) := by
    rw [Nat.mul_comm (n1 / n2) (4 * n2), Nat.mul_assoc]
    have dm' := Nat.mod_add_div n1 n2
    generalize n2 * (n1 / n2) = P at dm' ⊢
    omega
  rw [r]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt (lt_of_le_of_lt le b1),
    Nat.mod_eq_of_lt (by omega : 4 * n1 - n1 / n2 * (4 * n2) < 2 ^ width)]
  have pos : n1 / n2 * (4 * n2) < 2 ^ width := lt_of_le_of_lt le b1
  rw [show 2 ^ width - n1 / n2 * (4 * n2) + 4 * n1 = 2 ^ width + (4 * n1 - n1 / n2 * (4 * n2)) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- HOL `int_mod` of two naturals is their natural remainder. Private infrastructure. -/
theorem modHolIntMod (n1 n2 : Nat) (n2pos : 0 < n2) :
    holIntMod (n1 : Int) (n2 : Int) = ((n1 % n2 : Nat) : Int) := by
  rw [holIntMod_spec _ _ (by omega), holIntDiv_ofNat_ofNat _ _ n2pos]
  push_cast
  rw [Int.emod_def]
  ring

open Classical in
/-- Draft of HOL `assign_Mod` under `EvalCallArithStmt`. -/
theorem assignMod_correct {width : Nat} [NeZero width] {C F : Type}
    (evalCallArith : EvalCallArithStmt width C F)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .intOp .mod)
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
    obtain ⟨a, b, next, valuesEq, bne, spaceEq, resultEq, stateEq⟩ := modSource values cut resultState result run
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
      (assignModFast conf n l dest (some names) a1 a2)
      (assignModSlow n l dest (some names) a1 a2) hx hy
    have compiled : (compileAssign conf n l dest (.intOp .mod) [a1, a2] (some names)).1 =
        (assignMod (width := width) conf n l dest (some names) a1 a2).1 := by
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
      have qEq : (n1 : Int).fmod (n2 : Int) = ((n1 % n2 : Nat) : Int) := by
        simp [Int.fmod_eq_emod_of_nonneg]
      have qBound : n1 % n2 < 2 ^ (width - 3) := lt_of_le_of_lt (Nat.mod_le _ _) bound1
      have nextRel : stateRel conf l1 l2 next target none locs := by
        simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
        subst next
        rcases relCut with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
          htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
        refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
          hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
        exact memoryRel_zeroSpace conf target.be (holThe cut.tstamps) cut.refs
          cut.space target.store target.memory target.mdomain _ hmem
      let src := DataSem.doStack (.intOp .mod) [.number (n1 : Int), .number (n2 : Int)]
        (DataSem.doLimSafe next (.intOp .mod) [.number (n1 : Int), .number (n2 : Int)])
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
          (.ite .test 1 (.imm 1) (assignModFast conf n l dest (some names) a1 a2)
            (assignModSlow n l dest (some names) a1 a2)) t2 =
          WordSemStateFiniteExact.evaluate (assignModFast conf n l dest (some names) a1 a2) t2 := by
        rw [WordSemStateFiniteExact.evaluate, get1]
        simp only [WordSemStateFiniteExact.getVarImm, testTrue]
      suffices key : ∃ T : WordSemStateFiniteExact width C F,
          WordSemStateFiniteExact.evaluate (assignModFast conf n l dest (some names) a1 a2) t2 =
            (none, T.setVar (adjustVar dest) (.word (BitVec.ofNat width (n1 % n2) <<< (2 : Nat)))) ∧
          stateRel conf l1 l2 src T none locs by
        obtain ⟨T, evalT, relT⟩ := key
        refine ⟨none, T.setVar (adjustVar dest) (.word (BitVec.ofNat width (n1 % n2) <<< (2 : Nat))),
          ?_, by simp, fun _ => ⟨?_, rfl⟩⟩
        · rw [compiled, assignMod_split, prefixEval, iteEval, evalT]
        · rw [qEq]
          exact divSetSmallNat conf l1 l2 src T locs dest (n1 % n2) relT qBound
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
      have resWord : BitVec.ofNat width (4 * n1 % (4 * n2)) = BitVec.ofNat width (n1 % n2) <<< (2 : Nat) :=
        modRemWord n1 n2 b1 n2pos
      by_cases hd : conf.hasDiv
      · let prod := n1 / n2 * (4 * n2)
        let lo : BitVec width := BitVec.ofNat width prod
        let hi : BitVec width := BitVec.ofNat width (prod / 2 ^ width)
        let s1 := t2.setVar 1 (.word q)
        refine ⟨(s1.setVar 3 (.word hi)).setVar 1 (.word lo), ?_, ?_⟩
        · have instRun : WordSemStateFiniteExact.inst
              (.arith (.div 1 (adjustVar a1) (adjustVar a2))) t2 = some s1 := by
            simp [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
              WordSemStateFiniteExact.getVar, t2read _ adj1, t2read _ adj2, tread.1, tread.2, xEq, yEq,
              quot, q, s1]
            exact yNe
          have instEval : WordSemStateFiniteExact.evaluate
              (.inst (.arith (.div 1 (adjustVar a1) (adjustVar a2)))) t2 = (none, s1) := by
            rw [WordSemStateFiniteExact.evaluate, instRun]
          have qLt : n1 / n2 < 2 ^ width := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
          have s1read : ∀ k, k ≠ 1 → sptLookup k s1.locals = sptLookup k target.locals := by
            intro k hk
            simp [s1, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ hk, ← t2read _ hk]
          have mulRun : WordSemStateFiniteExact.inst
              (.arith (.longMul 3 1 1 (adjustVar a2))) s1 =
              some ((s1.setVar 3 (.word hi)).setVar 1 (.word lo)) := by
            have s11 : sptLookup 1 s1.locals = some (.word q) := by
              simp [s1, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
            simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
              WordSemStateFiniteExact.getVar, s11, s1read _ adj2, tread.2]
            simp [yEq, q, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt qLt, lo, hi, prod]
          have mulEval : WordSemStateFiniteExact.evaluate
              (.inst (.arith (.longMul 3 1 1 (adjustVar a2)))) s1 =
              (none, (s1.setVar 3 (.word hi)).setVar 1 (.word lo)) := by
            rw [WordSemStateFiniteExact.evaluate, mulRun]
          have subWord : BitVec.ofNat width (4 * n1) - lo = BitVec.ofNat width (n1 % n2) <<< (2 : Nat) :=
            modSubWord n1 n2 b1 n2pos
          have subEval : WordSemStateFiniteExact.evaluate
              (.assign (adjustVar dest) (.op .sub [.var (adjustVar a1), .var 1]))
              ((s1.setVar 3 (.word hi)).setVar 1 (.word lo)) =
              (none, ((s1.setVar 3 (.word hi)).setVar 1 (.word lo)).setVar (adjustVar dest)
                (.word (BitVec.ofNat width (n1 % n2) <<< (2 : Nat)))) := by
            have adj3 : adjustVar a1 ≠ 3 := by simp [adjustVar]
            have ra : sptLookup (adjustVar a1) (sptInsert 1 (.word lo) (sptInsert 3 (.word hi) s1.locals)) =
                some (.word x) := by
              rw [sptLookup_sptInsert_ne _ _ _ _ adj1, sptLookup_sptInsert_ne _ _ _ _ adj3, s1read _ adj1]
              exact tread.1
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getVar, ra, theWords, wordOpHOL, wordOp, sptLookup_sptInsert_same,
              WordSemStateFiniteExact.setVar, ← subWord, xEq]
          simp only [assignModFast, hd, if_true, wordListSeq]
          rw [divEvalSeq, instEval]
          simp only
          rw [divEvalSeq, mulEval]
          exact subEval
        · have r1 := (stateRel_insertOdd conf l1 l2 src t2 none locs 1 (.word q) rfl).symm ▸ srcRel2
          have r3 := (stateRel_insertOdd conf l1 l2 src s1 none locs 3 (.word hi) rfl).symm ▸ r1
          exact (stateRel_insertOdd conf l1 l2 src (s1.setVar 3 (.word hi)) none locs 1 (.word lo) rfl).symm ▸ r3
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
          simp only [assignModFast, hd, hl, if_true, if_false, Bool.false_eq_true, wordListSeq]
          rw [divEvalSeq, assign0]
          simp only
          rw [divEvalSeq, instEval]
          have moveRun : WordSemStateFiniteExact.evaluate (.move 2 [(adjustVar dest, 3)])
              ((s0.setVar 3 (.word rem)).setVar 1 (.word q)) =
              (none, ((s0.setVar 3 (.word rem)).setVar 1 (.word q)).setVar (adjustVar dest) (.word rem)) := by
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
              WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setVars,
              LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
          exact moveRun.trans (by rw [show rem = BitVec.ofNat width (n1 % n2) <<< (2 : Nat) from resWord])
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
          · simp only [assignModFast, hd, hl, if_false, Bool.false_eq_true, Option.getD_some, wordListSeq]
            rw [divEvalSeq, assign0]
            simp only
            rw [divEvalSeq, wrapped]
            have getRun : WordSemStateFiniteExact.evaluate (.get (adjustVar dest) (.temp 28)) T =
                (none, T.setVar (adjustVar dest) (.word rem)) := by
              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getStore, T, restored, returned,
                HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, WordSemStateFiniteExact.setVars]
            exact getRun.trans (by rw [show rem = BitVec.ofNat width (n1 % n2) <<< (2 : Nat) from resWord])
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
                DataSem.smallNum next.limits.arch64Bit (holIntMod (n1 : Int) (n2 : Int)) := by
              rw [nextFields.2.2.2.2, cutLimits, smallEq, modHolIntMod n1 n2 n2pos]
              refine ⟨sa, by omega, sb, by omega, ?_⟩
              generalize n1 % n2 = k at qBound ⊢
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
          (.ite .test 1 (.imm 1) (assignModFast conf n l dest (some names) a1 a2)
            (assignModSlow n l dest (some names) a1 a2)) t2 =
          WordSemStateFiniteExact.evaluate (assignModSlow n l dest (some names) a1 a2) t2 := by
        rw [WordSemStateFiniteExact.evaluate, get1]
        simp only [WordSemStateFiniteExact.getVarImm, testFalse]
      have loc6 : Bignum.arithLocation 6 = modLocation := by simp [Bignum.arithLocation]
      have intOp6 : Bignum.intOp 6 a b = some (a.fmod b) := by simp [Bignum.intOp, bne]
      obtain ⟨q, r', runEq, rest⟩ := evalCallArith conf l1 l2 source t2 locs (some names) a1 a2 a b cut
        dest n l 6 (a.fmod b) ⟨rel2, by simp, by simpa [t2, WordSemStateFiniteExact.setVar] using depth,
          argsEq, cutEq, intOp6⟩
      rw [loc6] at runEq rest
      have progEval : WordSemStateFiniteExact.evaluate
          (compileAssign conf n l dest (.intOp .mod) [a1, a2] (some names)).1 target = (q, r') := by
        rw [compiled, assignMod_split, prefixEval, iteEval, assignModSlow]
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
          DataSem.smallNum source.limits.arch64Bit (holIntMod a b)) := by
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
              DataSem.spaceConsumed cut (.intOp .mod) [.number a, .number b] ≤ cut.limits.heapLimit)) := by
        simp only [DataSem.doSpace, DataLang.opSpaceReset, if_true, Option.some.injEq] at spaceEq
        subst next
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have stackSizeEq := stackRel_sizeOfStack relCut.2.2.2.2.2.2.2.2.2.2.2.2.1
      have frameSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have localSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have notCondCut : ¬ (DataSem.smallNum cut.limits.arch64Bit a ∧ 0 ≤ a ∧
          DataSem.smallNum cut.limits.arch64Bit b ∧ 0 ≤ b ∧
          DataSem.smallNum cut.limits.arch64Bit (holIntMod a b)) := by
        rw [cutSame.2.1]; exact notCond
      dsimp only at rest
      obtain ⟨maxLe, nesCase, okCase⟩ := rest
      have maxEq : (DataSem.doStack (.intOp .mod) [.number a, .number b]
          (DataSem.doLimSafe next
            (.intOp .mod) [.number a, .number b])).stackMax =
          wordSemOptionMax source.stackMax (wordSemOptionAdd (wordSemStackSize t2.stack)
            (wordSemOptionAdd t2.localsSize (wordSemOptionMax (sptLookup modLocation t2.stackSize)
              (WordDepth.maxDepth t2.stackSize anyArithCallTree)))) := by
        simp only [DataSem.doStack, DataSem.doLimSafe, nextFields.1, nextFields.2.1, nextFields.2.2.1,
          nextFields.2.2.2.1, nextFields.2.2.2.2.1, DataSem.stackConsumed, if_neg notCondCut]
        simp only [t2, WordSemStateFiniteExact.setVar]
        rw [stackSizeEq, localSizeEq, frameSizeEq, cutSame.1]
        generalize sptLookup modLocation cut.stackFrameSizes = A
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
          have spaceEq' : DataSem.spaceConsumed cut (.intOp .mod) [.number a, .number b] =
              2 * DataSem.bignumSize cut.limits.arch64Bit a + 2 * DataSem.bignumSize cut.limits.arch64Bit b := by
            simp only [DataSem.spaceConsumed, if_neg notCondCut]
            rfl
          cases hsafe : (DataSem.doStack (.intOp .mod) [.number a, .number b]
              (DataSem.doLimSafe next (.intOp .mod) [.number a, .number b])).safeForSpace with
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
