module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordToInt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumImp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.ShiftVar
@[expose] public section

/-! Integer-to-Word64 conversion in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The tagged encoding of a small integer is its two's-complement word times four.
Flapjack arithmetic infrastructure for `assign_WordFromInt`. -/
theorem smallnum_eq_ofInt {k : Nat} [NeZero k] (i : Int) :
    (smallnum i : BitVec k) = BitVec.ofInt k (4 * i) := by
  unfold smallnum
  split
  · rename_i neg
    have : (4 * (0 - i)).toNat = ((-(4 * i)) : Int).toNat := by omega
    rw [this, show (4 * i) = -(((-(4 * i)).toNat : Nat) : Int) by omega, BitVec.ofInt_neg,
      BitVec.ofInt_natCast]
    simp [BitVec.sub_eq_add_neg]
    congr 1
    omega
  · rename_i nonneg
    rw [show (4 * i) = (((4 * i).toNat : Nat) : Int) by omega, BitVec.ofInt_natCast]
    congr 1

/-- Arithmetic right shift by two recovers a small tagged integer.
Flapjack arithmetic infrastructure for `assign_WordFromInt`. -/
theorem smallnum_sshiftRight {k : Nat} [NeZero k] (hk : 3 ≤ k) (i : Int) (small : smallInt k i) :
    (smallnum i : BitVec k).sshiftRight 2 = BitVec.ofInt k i := by
  rw [smallnum_eq_ofInt]
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ (k - 3) := ⟨_, rfl⟩
  have pk : 2 ^ k = 8 * N := by
    rw [hN, show k = (k - 3) + 3 from by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have Npos : 0 < N := by rw [hN]; exact Nat.two_pow_pos _
  have div8 : 2 ^ k / 8 = N := by rw [pk]; omega
  unfold smallInt at small
  simp only [Int.ofNat_eq_natCast, div8] at small
  obtain ⟨lo, hi⟩ := small
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, BitVec.toInt_ofInt, BitVec.toInt_ofInt, pk]
  have b1 : (4 * i).bmod (8 * N) = 4 * i := by
    apply Int.bmod_eq_of_le <;> push_cast <;> omega
  have b2 : i.bmod (8 * N) = i := by
    apply Int.bmod_eq_of_le <;> push_cast <;> omega
  rw [b1, b2, Int.shiftRight_eq_div_pow]
  omega

/-- Negating a magnitude word gives the two's-complement word of the negative
integer. Flapjack arithmetic infrastructure for `assign_WordFromInt`. -/
theorem zero_sub_ofNat_natAbs {k : Nat} (i : Int) (neg : i < 0) :
    (0 : BitVec k) - BitVec.ofNat k i.natAbs = BitVec.ofInt k i := by
  have h : BitVec.ofInt k i = - BitVec.ofNat k i.natAbs := by
    rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_neg]
    congr 1
    omega
  rw [h]
  simp [BitVec.sub_eq_add_neg]

/-- Truncating the 64-bit two's-complement word of an integer gives its 32-bit
word. Flapjack arithmetic infrastructure for `assign_WordFromInt`. -/
theorem ofInt64_setWidth32 (i : Int) : (BitVec.ofInt 64 i).setWidth 32 = BitVec.ofInt 32 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

/-- The high half of the 64-bit two's-complement word of an integer.
Flapjack arithmetic infrastructure for `assign_WordFromInt`. -/
theorem ofInt64_high32 (i : Int) : ((BitVec.ofInt 64 i) >>> (32 : Nat)).setWidth 32 =
    BitVec.ofNat 32 ((i % 2 ^ 64).toNat / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

/-- On 32-bit words, an arithmetic right shift of a small tagged integer by 31
gives the high half of its 64-bit word. Flapjack arithmetic infrastructure for
`assign_WordFromInt`. -/
theorem smallnum_high32 (i : Int) (lo : -(2 ^ 29) ≤ i) (hi : i < 2 ^ 29) :
    (BitVec.ofInt 32 (4 * i)).sshiftRight 31 = ((BitVec.ofInt 64 i) >>> (32 : Nat)).setWidth 32 := by
  rw [ofInt64_high32]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, BitVec.toInt_ofInt]
  have b1 : (4 * i).bmod (2 ^ 32) = 4 * i := by
    apply Int.bmod_eq_of_le <;> omega
  rw [b1, Int.shiftRight_eq_div_pow]
  by_cases h : 0 ≤ i
  · have : (i % 2 ^ 64).toNat / 2 ^ 32 = 0 := by omega
    rw [this, show (BitVec.ofNat 32 0).toInt = 0 by decide]; omega
  · have : (i % 2 ^ 64).toNat / 2 ^ 32 = 2 ^ 32 - 1 := by omega
    rw [this, show (BitVec.ofNat 32 (2 ^ 32 - 1)).toInt = -1 by decide]; omega

/-- Two's-complement negation of a two-digit 32-bit magnitude through two
add-with-carry steps gives the halves of the negative integer's 64-bit word.
Flapjack arithmetic infrastructure for `assign_WordFromInt`. -/
theorem negCarry_halves32 (i : Int) (neg : i < 0) :
    (wordAddCarryHOL (0 : BitVec 32) (~~~(0 : BitVec 32) ^^^ BitVec.ofNat 32 i.natAbs) 1).1 =
      (BitVec.ofInt 64 i).setWidth 32 ∧
    (wordAddCarryHOL (0 : BitVec 32) (~~~(0 : BitVec 32) ^^^ BitVec.ofNat 32 (i.natAbs / 2 ^ 32))
      (wordAddCarryHOL (0 : BitVec 32) (~~~(0 : BitVec 32) ^^^ BitVec.ofNat 32 i.natAbs) 1).2).1 =
      ((BitVec.ofInt 64 i) >>> (32 : Nat)).setWidth 32 := by
  have nx : ∀ d : BitVec 32, (~~~(0 : BitVec 32) ^^^ d).toNat = 2 ^ 32 - 1 - d.toNat := by
    intro d
    rw [show ~~~(0 : BitVec 32) ^^^ d = ~~~d by
      rw [show ~~~(0 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.allOnes_xor],
      BitVec.toNat_not]
  rw [ofInt64_high32]
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [wordAddCarryHOL, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, nx]
    simp
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [wordAddCarryHOL, BitVec.toNat_ofNat, nx]
    simp
    split_ifs <;> omega

/-- Assigning an evaluated expression in a sequence continues from the updated
local. Private infrastructure for the HOL assignment proof. -/
private theorem seqAssign' {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : s.wordExp expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (s.setVar key v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Executing a successful instruction in a sequence continues from its state.
Private infrastructure for the HOL assignment proof. -/
private theorem seqInst' {width : Nat} [NeZero width] {C F : Type}
    (t s : WordSemStateFiniteExact width C F) (i : WordLangInst (BitVec width))
    (p : WordLangProgHOL (BitVec width)) (h : WordSemStateFiniteExact.inst i t = some s)
    (hc : s.clock = t.clock) (ht : s.termdep = t.termdep) :
    WordSemStateFiniteExact.evaluate (.seq (.inst i) p) t =
      WordSemStateFiniteExact.evaluate p s := by
  simp only [WordSemStateFiniteExact.evaluate, h, WordSemStateFiniteExact.fixClock]
  rw [← hc, if_neg (lt_irrefl _), ← ht]

/-- Setting an odd local preserves an established state-relation equivalence.
Private infrastructure for the HOL assignment proof. -/
private theorem relSetVar {width : Nat} [NeZero width] {C F : Type} (conf : Config) (l1 l2 : Nat)
    (locs : List (Nat × Nat)) (pre target : WordSemStateFiniteExact width C F) (k : Nat)
    (v : WordLocW width) (odd : k % 2 = 1)
    (h : ∀ s : DataSem.State C F, stateRel conf l1 l2 s pre none locs = stateRel conf l1 l2 s target none locs) :
    ∀ s : DataSem.State C F, stateRel conf l1 l2 s (pre.setVar k v) none locs =
      stateRel conf l1 l2 s target none locs :=
  fun s => (stateRel_insertOdd conf l1 l2 s pre none locs k v odd).trans (h s)

namespace WordFromIntAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordFromIntAssignmentWitness

private theorem wordFromIntSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp .wordFromInt) values source = .val (result, resultState)) :
    ∃ i next, values = [.number i] ∧ DataSem.consumeSpace 3 source = some next ∧
      result = .word64 (BitVec.ofInt 64 i) ∧
      resultState = DataSem.doStack (.wordOp .wordFromInt) values
        (DataSem.doLimSafe next (.wordOp .wordFromInt) values) := by
  cases h : DataSem.consumeSpace 3 source with
  | none =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h] at run
  | some next =>
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons value rest =>
      cases rest with
      | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | nil =>
        cases value <;> simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]

/-- Integer-to-Word64 conversion satisfies the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_WordFromInt"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWordFromInt_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .wordOp .wordFromInt)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  subst op
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
  have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  obtain ⟨i, next, valuesEq, spaceEq, resultEq, stateEq⟩ := wordFromIntSource values source resultState result run
  subst values
  subst result
  subst resultState
  have argLen := DataSpace.getVars_length args source.locals [.number i] argsEq
  match args, argLen with
  | [arg], _ =>
  have nextEq : next = { source with space := source.space - 3 } := by
    unfold DataSem.consumeSpace at spaceEq
    split at spaceEq <;> simp_all
  subst next
  have spaceEnough : 3 ≤ source.space := by
    unfold DataSem.consumeSpace at spaceEq
    split at spaceEq <;> simp_all
  let unspaced := DataSem.doStack (.wordOp .wordFromInt) [.number i]
    (DataSem.doLimSafe source (.wordOp .wordFromInt) [.number i])
  have unspacedRel : stateRel conf l1 l2 unspaced target none locs :=
    stateRel_doStack conf l1 l2 _ target locs _ _
      (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
  obtain ⟨words, getWords, lengthEq⟩ :=
    stateRel_getVars conf l1 l2 source target locs [arg] [.number i] related argsEq
  match words, lengthEq with
  | [loc], _ =>
  let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
    flatStack source.stack target.stack
  let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
  have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
    target.store target.memory target.mdomain target envs [arg] [.number i] [loc] (by
      refine ⟨?_, argsEq, getWords⟩
      simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have good := related.2.2.2.2.2.2.1
  have shiftBound := related.2.2.2.2.2.2.2.1
  have locRead : WordSemStateFiniteExact.getVar (adjustVar arg) target = some loc := by
    cases found : WordSemStateFiniteExact.getVar (adjustVar arg) target <;>
      simp_all [WordSemStateFiniteExact.getVars]
  have rootsRel : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.number i, loc) :: (locals ++ envs)) := by
    simpa [locals, envs, List.append_assoc] using roots
  rcases good with width32 | width64
  · subst width
    cases header : encodeHeader (width := 32) conf 3 2 with
    | none =>
      obtain ⟨_, headerOfSafe⟩ := wordToIntHeaders conf source target l1 l2 locs related
      let spaced : DataSem.State C F := { source with space := source.space - 3 }
      let nextSource := DataSem.doStack (.wordOp .wordFromInt) [.number i]
        (DataSem.doLimSafe spaced (.wordOp .wordFromInt) [.number i])
      have nextRel : stateRel conf l1 l2 nextSource target none locs :=
        stateRel_doStack conf l1 l2 _ target locs _ _
          (stateRel_doLimSafe conf l1 l2 spaced target locs _ _
            (stateRel_lessSpace conf l1 l2 source target locs 3 related))
      obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ :=
        evaluateGiveUp2 conf l1 l2 source target locs related
      have noSafe : ¬ DataSem.limSafe source.limits (.wordOp .wordFromInt) [.number i] := by
        intro safe
        obtain ⟨hd, encoded⟩ := headerOfSafe [.number i] (by simpa [DataSem.limSafe] using safe)
        simp only [show (32 = 64) = False by decide, if_false] at encoded
        rw [header] at encoded
        contradiction
      refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
      · simpa [compileAssign, arg1, assignWordFromInt, header] using outEval
      · intro _
        refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
        · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
          simpa [nextSource, spaced, DataSem.doStack, DataSem.doLimSafe] using targetBound
        · intro _
          simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
      · simp
    | some hd =>
    let value : BitVec 64 := BitVec.ofInt 64 i
    have finish : ∀ (pre : WordSemStateFiniteExact 32 C F) (s1 s2 : Nat), s1 ≠ 1 → s2 ≠ 1 →
        (∀ s : DataSem.State C F, stateRel conf l1 l2 s pre none locs = stateRel conf l1 l2 s target none locs) →
        pre.getVar s1 = some (.word (value.setWidth 32)) →
        pre.getVar s2 = some (.word ((value >>> (32 : Nat)).setWidth 32)) →
        ∃ r, WordSemStateFiniteExact.evaluate (writeWord64On32 conf hd dest s1 s2) pre = (none, r) ∧
          stateRel conf l1 l2 (DataSem.setVar dest (.word64 value)
            (DataSem.doStack (.wordOp .wordFromInt) [.number i]
              (DataSem.doLimSafe {source with space := source.space - 3} (.wordOp .wordFromInt)
                [.number i]))) r none locs := by
      intro pre s1 s2 s1Ne s2Ne relEq getLow getHigh
      have rel := (relEq source).mpr related
      have uRel := (relEq unspaced).mpr unspacedRel
      have presentPre : ∀ k, (sptLookup k source.locals).isSome →
          (sptLookup (adjustVar k) pre.locals).isSome := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := rel
        exact presentOld
      let envsP := [(theGlobal source.global, holFapply pre.store .globals)] ++
        flatStack source.stack pre.stack
      have preHeap : memoryRel conf pre.be (holThe source.tstamps) source.refs source.space
          pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envsP) := by
        simpa [envsP, joinEnvLocals] using rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved, destPresent, zeroEq⟩ :=
        evaluateWriteWord64On32 (β := PUnit) conf pre.be (holThe source.tstamps) source.space source.refs pre
          source.locals envsP s1 s2 dest value hd preHeap getLow getHigh shiftBound s1Ne s2Ne
          (by omega) rfl header presentPre
      have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
        unspaced pre locs (.word64 value) nf memory locals1 pre.fpRegs uRel
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
        destPresent zeroEq
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe, envsP] using writeHeap)
      exact ⟨_, writeEval, by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe] using finalRel⟩
    let bigProg : WordLangProgHOL (BitVec 32) := wordListSeq [
        .assign 1 (realAddr conf (adjustVar arg)), .assign 3 (.load (.var 1)),
        .assign 5 (.load (.op .add [.var 1, .const wordSemBytesInWord])),
        .assign 7 (shiftVar .lsr 3 (32 - conf.lenSize)),
        .ite .equal 7 (.imm 1)
          (.ite .test 3 (.imm 16)
            (.seq (.assign 9 (.const 0)) (writeWord64On32 conf hd dest 5 9))
            (.seq (.assign 9 (.const (~~~(0 : BitVec 32))))
              (.seq (.assign 5 (.op .sub [.const 0, .var 5]))
                (writeWord64On32 conf hd dest 5 9))))
          (.ite .test 3 (.imm 16)
            (.seq (.assign 9 (.load (.op .add [.var 1, .const (2 * wordSemBytesInWord)])))
              (writeWord64On32 conf hd dest 5 9))
            (wordListSeq [
              .assign 11 (.const 0), .assign 13 (.const 1),
              .assign 9 (.load (.op .add [.var 1, .const (2 * wordSemBytesInWord)])),
              .assign 5 (.op .xor [.const (~~~(0 : BitVec 32)), .var 5]),
              .assign 9 (.op .xor [.const (~~~(0 : BitVec 32)), .var 9]),
              .inst (.arith (.addCarry 15 11 5 13)), .inst (.arith (.addCarry 19 11 9 13)),
              writeWord64On32 conf hd dest 15 19]))]
    have compiled : (compileAssign (width := 32) conf n l dest (.wordOp .wordFromInt) [arg] none).1 =
        .ite .test (adjustVar arg) (.imm 1)
          (wordListSeq [
            .assign 3 (shiftN .asr (.var (adjustVar arg)) 2),
            .assign 5 (shiftN .asr (.var (adjustVar arg)) 31),
            writeWord64On32 conf hd dest 3 5]) bigProg := by
      simp [compileAssign, arg1, assignWordFromInt, header, bigProg]
    have reduce : ∃ (pre : WordSemStateFiniteExact 32 C F) (s1 s2 : Nat), s1 ≠ 1 ∧ s2 ≠ 1 ∧
        (∀ s : DataSem.State C F, stateRel conf l1 l2 s pre none locs = stateRel conf l1 l2 s target none locs) ∧
        pre.getVar s1 = some (.word (value.setWidth 32)) ∧
        pre.getVar s2 = some (.word ((value >>> (32 : Nat)).setWidth 32)) ∧
        WordSemStateFiniteExact.evaluate
          (compileAssign (width := 32) conf n l dest (.wordOp .wordFromInt) [arg] none).1 target =
        WordSemStateFiniteExact.evaluate (writeWord64On32 conf hd dest s1 s2) pre := by
      obtain ⟨w, wEq, lowIff⟩ := memoryRel_anyNumberImp conf target.be (holThe source.tstamps)
        source.refs source.space target.store target.memory target.mdomain i loc (locals ++ envs)
        ⟨Or.inl rfl, rootsRel⟩
      subst loc
      rw [compiled]
      by_cases small : smallInt 32 i
      · have locSmall := memoryRel_numberImp conf target.be (holThe source.tstamps)
          source.refs source.space target.store target.memory target.mdomain i (.word w) (locals ++ envs)
          ⟨Or.inl rfl, small, rootsRel⟩
        have wEq' : w = smallnum i := by simpa using locSmall
        have low : w.getLsbD 0 = false := by
          cases h : w.getLsbD 0
          · rfl
          · exact absurd small (lowIff.mp h)
        have mask : w &&& 1 = 0 := (StackAlloc.word_and_one_eq_0_iff w).mpr
          (by intro h; rw [low] at h; exact Bool.false_ne_true h)
        have test : wordSemWordCmp .test (.word w) (.word (1#32)) = some true := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (w &&& (1 : BitVec 32) == 0) = true
          exact beq_iff_eq.mpr mask
        have bounds : -(2 ^ 29) ≤ i ∧ i < 2 ^ 29 := by
          unfold smallInt at small
          simp only [Int.ofNat_eq_natCast] at small
          norm_num at small
          omega
        have sh2 : w.sshiftRight 2 = value.setWidth 32 := by
          rw [wEq', smallnum_sshiftRight (by decide) i small, ofInt64_setWidth32]
        have sh31 : w.sshiftRight 31 = (value >>> (32 : Nat)).setWidth 32 := by
          rw [wEq', smallnum_eq_ofInt]
          exact smallnum_high32 i bounds.1 bounds.2
        let mid := target.setVar 3 (.word (value.setWidth 32))
        refine ⟨mid.setVar 5 (.word ((value >>> (32 : Nat)).setWidth 32)), 3, 5, by decide, by decide,
          relSetVar conf l1 l2 locs _ _ 5 _ rfl (relSetVar conf l1 l2 locs _ _ 3 _ rfl (fun _ => rfl)),
          by simp [mid, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same, sptLookup_sptInsert_ne],
          by simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same], ?_⟩
        have midRead : (target.setVar 3 (.word (value.setWidth 32))).getVar (adjustVar arg) =
            some (.word w) := by
          have odd : adjustVar arg ≠ 3 := by simp only [adjustVar]; omega
          simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_ne _ _ _ _ odd] using locRead
        simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, locRead]
        rw [show wordSemWordCmp .test (.word w) (.word (1 : BitVec 32)) = some true from test]
        simp only [wordListSeq]
        rw [seqAssign' _ 3 _ (.word (value.setWidth 32)) _ (by
          simp [WordSemStateFiniteExact.wordExp, shiftN, wordShiftHOL, locRead, sh2]),
          seqAssign' _ 5 _ (.word ((value >>> (32 : Nat)).setWidth 32)) _ (by
          simp [WordSemStateFiniteExact.wordExp, shiftN, wordShiftHOL, midRead, sh31])]
      · obtain ⟨ff, w', x, a, vEq, wbit, real, domA, memA, _, _, _, _, sep, domB, memB, sign, _, lenLt,
          decode⟩ := memoryRel_number_bignumImp_alt conf target.be (holThe source.tstamps) source.refs
            source.space target.store target.memory target.mdomain i (.word w) (locals ++ envs)
            ⟨rootsRel, small, Or.inl rfl⟩
        cases vEq
        have test : wordSemWordCmp .test (.word w) (.word (1#32)) = some false := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (w &&& (1 : BitVec 32) == 0) = false
          exact beq_eq_false_iff_ne.mpr wbit
        have realEval := Bignum.getRealAddr_lemma conf (adjustVar arg) target w a
          ⟨shiftBound, Or.inl rfl, locRead, real⟩
        have notZero : i.natAbs ≠ 0 := by
          intro z
          apply small
          rw [Int.natAbs_eq_zero.mp z]
          simp [smallInt]
        have digits : (Misc.Multiword.n2mw i.natAbs : List (BitVec 32)) =
            BitVec.ofNat 32 (i.natAbs % 2 ^ 32) :: Misc.Multiword.n2mw (i.natAbs / 2 ^ 32) := by
          rw [Misc.Multiword.n2mw]
          simp [notZero]
        let len := (Misc.Multiword.n2mw i.natAbs : List (BitVec 32)).length
        let d0 : BitVec 32 := BitVec.ofNat 32 i.natAbs
        let s4 := (((target.setVar 1 (.word a)).setVar 3 (.word x)).setVar 5 (.word d0)).setVar 7
          (.word (BitVec.ofNat 32 len))
        have rel4 : ∀ s : DataSem.State C F, stateRel conf l1 l2 s s4 none locs =
            stateRel conf l1 l2 s target none locs :=
          relSetVar conf l1 l2 locs _ _ 7 _ rfl (relSetVar conf l1 l2 locs _ _ 5 _ rfl
            (relSetVar conf l1 l2 locs _ _ 3 _ rfl (relSetVar conf l1 l2 locs _ _ 1 _ rfl (fun _ => rfl))))
        have shifted : x >>> (32 - conf.lenSize) = BitVec.ofNat 32 len := by
          simpa [WordGcFunctions.decodeLength] using decode
        let pfx : List (WordLangProgHOL (BitVec 32)) := [
          .assign 1 (realAddr conf (adjustVar arg)), .assign 3 (.load (.var 1)),
          .assign 5 (.load (.op .add [.var 1, .const wordSemBytesInWord])),
          .assign 7 (shiftVar .lsr 3 (32 - conf.lenSize))]
        have loads : WordSemStateFiniteExact.evaluate (wordListSeq pfx) target = (none, s4) := by
          simp only [pfx, wordListSeq]
          rw [seqAssign' _ 1 _ (.word a) _ realEval,
            seqAssign' _ 3 _ (.word x) _ (by
              simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
                WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same, domA, memA]),
            seqAssign' _ 5 _ (.word d0) _ (by
              simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
                WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same, sptLookup_sptInsert_ne, theWords, wordOpHOL, wordOp,
                domB, memB, d0])]
          simp [WordSemStateFiniteExact.evaluate, Bignum.wordExpShiftVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same, sptLookup_sptInsert_ne, SemanticPrimitivesProps.shiftLookup, shifted, s4]
        let tailProg : WordLangProgHOL (BitVec 32) :=
          .ite .equal 7 (.imm 1)
            (.ite .test 3 (.imm 16)
              (.seq (.assign 9 (.const 0)) (writeWord64On32 conf hd dest 5 9))
              (.seq (.assign 9 (.const (~~~(0 : BitVec 32))))
                (.seq (.assign 5 (.op .sub [.const 0, .var 5]))
                  (writeWord64On32 conf hd dest 5 9))))
            (.ite .test 3 (.imm 16)
              (.seq (.assign 9 (.load (.op .add [.var 1, .const (2 * wordSemBytesInWord)])))
                (writeWord64On32 conf hd dest 5 9))
              (wordListSeq [
                .assign 11 (.const 0), .assign 13 (.const 1),
                .assign 9 (.load (.op .add [.var 1, .const (2 * wordSemBytesInWord)])),
                .assign 5 (.op .xor [.const (~~~(0 : BitVec 32)), .var 5]),
                .assign 9 (.op .xor [.const (~~~(0 : BitVec 32)), .var 9]),
                .inst (.arith (.addCarry 15 11 5 13)), .inst (.arith (.addCarry 19 11 9 13)),
                writeWord64On32 conf hd dest 15 19]))
        have joined : WordSemStateFiniteExact.evaluate bigProg target =
            WordSemStateFiniteExact.evaluate tailProg s4 :=
          evalListAppend pfx tailProg target s4 loads
        have top : WordSemStateFiniteExact.evaluate (.ite .test (adjustVar arg) (.imm 1)
            (wordListSeq [
              .assign 3 (shiftN .asr (.var (adjustVar arg)) 2),
              .assign 5 (shiftN .asr (.var (adjustVar arg)) 31),
              writeWord64On32 conf hd dest 3 5]) bigProg) target =
            WordSemStateFiniteExact.evaluate tailProg s4 := by
          rw [← joined]
          conv_lhs => rw [WordSemStateFiniteExact.evaluate]
          simp only [WordSemStateFiniteExact.getVarImm, locRead]
          rw [show wordSemWordCmp .test (.word w) (.word (1 : BitVec 32)) = some false from test]
        have get3 : s4.getVar 3 = some (.word x) := by
          simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
        have get7 : s4.getVar 7 = some (.word (BitVec.ofNat 32 len)) := by
          simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        have i64 : ∀ k : Nat, k < 2 ^ 64 → (i % 2 ^ 64).toNat = k → value = BitVec.ofNat 64 k := by
          intro k _ hk
          apply BitVec.eq_of_toNat_eq
          simp only [value, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
          omega
        have t16 : wordSemWordCmp .test (.word x) (.word (16#32)) = some (decide (0 ≤ i)) := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (x &&& (16 : BitVec 32) == 0) = decide (0 ≤ i)
          by_cases nonneg : 0 ≤ i
          · simp only [nonneg, decide_true]
            exact beq_iff_eq.mpr (sign.mpr nonneg)
          · simp only [nonneg, decide_false]
            exact beq_eq_false_iff_ne.mpr (fun h => nonneg (sign.mp h))
        by_cases big : i.natAbs / 2 ^ 32 = 0
        · have restNil : (Misc.Multiword.n2mw (i.natAbs / 2 ^ 32) : List (BitVec 32)) = [] := by
            rw [Misc.Multiword.n2mw, if_pos big]
          have len1 : len = 1 := by
            show (Misc.Multiword.n2mw i.natAbs : List (BitVec 32)).length = 1
            rw [digits, restNil]; rfl
          have cmp7 : wordSemWordCmp .equal (.word (BitVec.ofNat 32 len)) (.word (1#32)) = some true := by
            simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, len1]
          have step7 : WordSemStateFiniteExact.evaluate tailProg s4 =
              WordSemStateFiniteExact.evaluate (.ite .test 3 (.imm 16)
                (.seq (.assign 9 (.const 0)) (writeWord64On32 conf hd dest 5 9))
                (.seq (.assign 9 (.const (~~~(0 : BitVec 32))))
                  (.seq (.assign 5 (.op .sub [.const 0, .var 5]))
                    (writeWord64On32 conf hd dest 5 9)))) s4 := by
            conv_lhs => rw [WordSemStateFiniteExact.evaluate]
            simp only [WordSemStateFiniteExact.getVarImm, get7]
            rw [show wordSemWordCmp .equal (.word (BitVec.ofNat 32 len)) (.word (1 : BitVec 32)) =
              some true from cmp7]
          have absLt : i.natAbs < 2 ^ 32 := by
            rw [Nat.div_eq_zero_iff] at big; omega
          by_cases nonneg : 0 ≤ i
          · have hN : (i.natAbs : Int) = i := Int.natAbs_of_nonneg nonneg
            have lowEq : value.setWidth 32 = d0 := by
              rw [ofInt64_setWidth32]
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, d0]
              omega
            have highEq : (value >>> (32 : Nat)).setWidth 32 = 0 := by
              rw [ofInt64_high32]
              apply BitVec.eq_of_toNat_eq
              simp
              omega
            refine ⟨s4.setVar 9 (.word 0), 5, 9, by decide, by decide,
              relSetVar conf l1 l2 locs _ _ 9 _ rfl rel4, ?_, ?_, ?_⟩
            · rw [lowEq]
              simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
            · rw [highEq]
              simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same]
            · rw [top, step7]
              conv_lhs => rw [WordSemStateFiniteExact.evaluate]
              simp only [WordSemStateFiniteExact.getVarImm, get3]
              rw [show wordSemWordCmp .test (.word x) (.word (16 : BitVec 32)) = some true by
                simpa [nonneg] using t16]
              exact seqAssign' _ 9 _ (.word 0) _ (by simp [WordSemStateFiniteExact.wordExp])
          · have hN : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
            have lowEq : value.setWidth 32 = 0 - d0 := by
              rw [ofInt64_setWidth32, zero_sub_ofNat_natAbs i (lt_of_not_ge nonneg)]
            have highEq : (value >>> (32 : Nat)).setWidth 32 = ~~~0 := by
              rw [ofInt64_high32]
              apply BitVec.eq_of_toNat_eq
              simp
              omega
            let s9 := s4.setVar 9 (.word (~~~(0 : BitVec 32)))
            refine ⟨s9.setVar 5 (.word (0 - d0)), 5, 9, by decide, by decide,
              relSetVar conf l1 l2 locs _ _ 5 _ rfl (relSetVar conf l1 l2 locs _ _ 9 _ rfl rel4),
              ?_, ?_, ?_⟩
            · rw [lowEq]
              simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same]
            · rw [highEq]
              simp [s9, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
            · rw [top, step7]
              conv_lhs => rw [WordSemStateFiniteExact.evaluate]
              simp only [WordSemStateFiniteExact.getVarImm, get3]
              rw [show wordSemWordCmp .test (.word x) (.word (16 : BitVec 32)) = some false by
                simpa [nonneg] using t16]
              dsimp only
              rw [seqAssign' _ 9 _ (.word (~~~(0 : BitVec 32))) _ (by simp [WordSemStateFiniteExact.wordExp])]
              exact seqAssign' s9 5 (.op .sub [.const 0, .var 5]) (.word (0 - d0))
                (writeWord64On32 conf hd dest 5 9) (by
                simp [s9, s4, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
                  WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
                  theWords, wordOpHOL, wordOp])
        · have restDigits : (Misc.Multiword.n2mw (i.natAbs / 2 ^ 32) : List (BitVec 32)) =
              BitVec.ofNat 32 (i.natAbs / 2 ^ 32 % 2 ^ 32) ::
                Misc.Multiword.n2mw (i.natAbs / 2 ^ 32 / 2 ^ 32) := by
            rw [Misc.Multiword.n2mw, if_neg big]
          have lenLt' : len < 2 ^ 32 := lenLt
          have lenNe : len ≠ 1 := by
            show (Misc.Multiword.n2mw i.natAbs : List (BitVec 32)).length ≠ 1
            rw [digits, restDigits]; simp
          have cmp7 : wordSemWordCmp .equal (.word (BitVec.ofNat 32 len)) (.word (1#32)) = some false := by
            simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
            apply beq_eq_false_iff_ne.mpr
            intro h
            have := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat] at this
            omega
          let d1 : BitVec 32 := BitVec.ofNat 32 (i.natAbs / 2 ^ 32)
          have e1 : BitVec.ofNat 32 (i.natAbs / 2 ^ 32 % 2 ^ 32) = d1 := by
            apply BitVec.eq_of_toNat_eq; simp [d1]
          have sep2 := sep
          rw [digits, restDigits, List.map_cons, List.map_cons, Misc.wordList, Misc.wordList,
            ← SetSep.starAssoc, SetSep.starComm, ← SetSep.starAssoc, ← SetSep.starAssoc] at sep2
          obtain ⟨d1Val, d1Dom⟩ := SetSep.readFun2Set _ _ _ target.memory
            (fun p => target.mdomain p = true) sep2
          have addr : a + wordSemBytesInWord + StackRemove.bytesInWord 32 = a + 2 * wordSemBytesInWord := by
            rw [BitVec.add_assoc]
            congr 1
          rw [addr, e1] at d1Val
          rw [addr] at d1Dom
          have step7 : WordSemStateFiniteExact.evaluate tailProg s4 =
              WordSemStateFiniteExact.evaluate (.ite .test 3 (.imm 16)
                (.seq (.assign 9 (.load (.op .add [.var 1, .const (2 * wordSemBytesInWord)])))
                  (writeWord64On32 conf hd dest 5 9))
                (wordListSeq [
                  .assign 11 (.const 0), .assign 13 (.const 1),
                  .assign 9 (.load (.op .add [.var 1, .const (2 * wordSemBytesInWord)])),
                  .assign 5 (.op .xor [.const (~~~(0 : BitVec 32)), .var 5]),
                  .assign 9 (.op .xor [.const (~~~(0 : BitVec 32)), .var 9]),
                  .inst (.arith (.addCarry 15 11 5 13)), .inst (.arith (.addCarry 19 11 9 13)),
                  writeWord64On32 conf hd dest 15 19])) s4 := by
            conv_lhs => rw [WordSemStateFiniteExact.evaluate]
            simp only [WordSemStateFiniteExact.getVarImm, get7]
            rw [show wordSemWordCmp .equal (.word (BitVec.ofNat 32 len)) (.word (1 : BitVec 32)) =
              some false from cmp7]
          have load9 : ∀ s : WordSemStateFiniteExact 32 C F, s.memory = target.memory →
              s.mdomain = target.mdomain → s.getVar 1 = some (.word a) →
              s.wordExp (.load (.op .add [.var 1, .const (2 * wordSemBytesInWord)])) = some (.word d1) := by
            intro s hm hd h1
            simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad, hm, hd,
              theWords, wordOpHOL, wordOp, h1]
            exact ⟨d1Dom, d1Val⟩
          have get1 : s4.getVar 1 = some (.word a) := by
            simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
              sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
          by_cases nonneg : 0 ≤ i
          · have hN : (i.natAbs : Int) = i := Int.natAbs_of_nonneg nonneg
            have lowEq : value.setWidth 32 = d0 := by
              rw [ofInt64_setWidth32]
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, d0]
              omega
            have highEq : (value >>> (32 : Nat)).setWidth 32 = d1 := by
              rw [ofInt64_high32]
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_ofNat, d1]
              omega
            refine ⟨s4.setVar 9 (.word d1), 5, 9, by decide, by decide,
              relSetVar conf l1 l2 locs _ _ 9 _ rfl rel4, ?_, ?_, ?_⟩
            · rw [lowEq]
              simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
            · rw [highEq]
              simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same]
            · rw [top, step7]
              conv_lhs => rw [WordSemStateFiniteExact.evaluate]
              simp only [WordSemStateFiniteExact.getVarImm, get3]
              rw [show wordSemWordCmp .test (.word x) (.word (16 : BitVec 32)) = some true by
                simpa [nonneg] using t16]
              exact seqAssign' _ 9 _ (.word d1) _ (load9 s4 rfl rfl get1)
          · have neg : i < 0 := lt_of_not_ge nonneg
            obtain ⟨lowEq, highEq⟩ := negCarry_halves32 i neg
            let c1 := wordAddCarryHOL (0 : BitVec 32) (~~~(0 : BitVec 32) ^^^ d0) 1
            let c2 := wordAddCarryHOL (0 : BitVec 32) (~~~(0 : BitVec 32) ^^^ d1) c1.2
            let p2 := (s4.setVar 11 (.word 0)).setVar 13 (.word 1)
            let p3 := p2.setVar 9 (.word d1)
            let p4 := p3.setVar 5 (.word (~~~(0 : BitVec 32) ^^^ d0))
            let p5 := p4.setVar 9 (.word (~~~(0 : BitVec 32) ^^^ d1))
            let p6 := (p5.setVar 15 (.word c1.1)).setVar 13 (.word c1.2)
            let p7 := (p6.setVar 19 (.word c2.1)).setVar 13 (.word c2.2)
            refine ⟨p7, 15, 19, by decide, by decide,
              relSetVar conf l1 l2 locs _ _ 13 _ rfl (relSetVar conf l1 l2 locs _ _ 19 _ rfl
                (relSetVar conf l1 l2 locs _ _ 13 _ rfl (relSetVar conf l1 l2 locs _ _ 15 _ rfl
                  (relSetVar conf l1 l2 locs _ _ 9 _ rfl (relSetVar conf l1 l2 locs _ _ 5 _ rfl
                    (relSetVar conf l1 l2 locs _ _ 9 _ rfl (relSetVar conf l1 l2 locs _ _ 13 _ rfl
                      (relSetVar conf l1 l2 locs _ _ 11 _ rfl rel4)))))))),
              ?_, ?_, ?_⟩
            · rw [← lowEq]
              simp [p7, p6, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same, sptLookup_sptInsert_ne, c1, d0]
            · rw [← highEq]
              simp [p7, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_same, sptLookup_sptInsert_ne, c2, c1, d0, d1]
            · rw [top, step7]
              conv_lhs => rw [WordSemStateFiniteExact.evaluate]
              simp only [WordSemStateFiniteExact.getVarImm, get3]
              rw [show wordSemWordCmp .test (.word x) (.word (16 : BitVec 32)) = some false by
                simpa [nonneg] using t16]
              dsimp only
              simp only [wordListSeq]
              rw [seqAssign' s4 11 _ (.word 0) _ (by simp [WordSemStateFiniteExact.wordExp]),
                seqAssign' (s4.setVar 11 (.word 0)) 13 _ (.word 1) _ (by simp [WordSemStateFiniteExact.wordExp]),
                seqAssign' p2 9 _ (.word d1) _ (load9 p2 rfl rfl (by
                  simp [p2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne]; exact get1)),
                seqAssign' p3 5 _ (.word (~~~(0 : BitVec 32) ^^^ d0)) _ (by
                  simp [p3, p2, s4, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
                    WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
                    theWords, wordOpHOL, wordOp]),
                seqAssign' p4 9 _ (.word (~~~(0 : BitVec 32) ^^^ d1)) _ (by
                  simp [p4, p3, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
                    WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
                    theWords, wordOpHOL, wordOp])]
              rw [seqInst' p5 p6 _ _ (by
                  simp [p6, p5, p4, p3, p2, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne, sptLookup_sptInsert_same, c1]) rfl rfl,
                seqInst' p6 p7 _ _ (by
                  simp [p7, p6, p5, p4, p3, p2, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne, sptLookup_sptInsert_same, c2, c1]) rfl rfl]
    obtain ⟨pre, s1, s2, s1Ne, s2Ne, relEq, getLow, getHigh, evalEq⟩ := reduce
    obtain ⟨r, writeEval, finalRel⟩ := finish pre s1 s2 s1Ne s2Ne relEq getLow getHigh
    exact ⟨none, r, by rw [evalEq, writeEval], by simp, fun _ => ⟨finalRel, rfl⟩⟩
  · subst width
    obtain ⟨⟨hd1, header1⟩, _⟩ := wordToIntHeaders conf source target l1 l2 locs related
    let value : BitVec 64 := BitVec.ofInt 64 i
    have finish : ∀ pre : WordSemStateFiniteExact 64 C F,
        (∀ s : DataSem.State C F, stateRel conf l1 l2 s pre none locs = stateRel conf l1 l2 s target none locs) →
        pre.getVar 3 = some (.word value) →
        ∃ r, WordSemStateFiniteExact.evaluate (writeWord64 conf hd1 dest 3) pre = (none, r) ∧
          stateRel conf l1 l2 (DataSem.setVar dest (.word64 value)
            (DataSem.doStack (.wordOp .wordFromInt) [.number i]
              (DataSem.doLimSafe {source with space := source.space - 3} (.wordOp .wordFromInt)
                [.number i]))) r none locs := by
      intro pre relEq get3
      have rel := (relEq source).mpr related
      have uRel := (relEq unspaced).mpr unspacedRel
      have presentPre : ∀ k, (sptLookup k source.locals).isSome →
          (sptLookup (adjustVar k) pre.locals).isSome := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := rel
        exact presentOld
      let envsP := [(theGlobal source.global, holFapply pre.store .globals)] ++
        flatStack source.stack pre.stack
      have preHeap : memoryRel conf pre.be (holThe source.tstamps) source.refs source.space
          pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envsP) := by
        simpa [envsP, joinEnvLocals] using rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved, destPresent, zeroEq⟩ :=
        evaluateWriteWord64 (β := PUnit) conf pre.be (holThe source.tstamps) source.space source.refs pre
          source.locals envsP 3 dest value hd1 preHeap get3 shiftBound (by decide) (by omega) rfl
          header1 presentPre
      have smallerHeap : memoryRel conf pre.be (holThe source.tstamps) source.refs
          (source.space - 3) (pre.store.update (.nextFree, nf)) memory pre.mdomain
          (joinEnvLocals (sptInsert dest (.word64 value) source.locals) locals1 ++ envsP) := by
        apply memoryRel_lessSpace conf pre.be (holThe source.tstamps) source.refs
          (source.space - 2) (source.space - 3) _ _ _ _
        refine ⟨?_, by omega⟩
        simpa using writeHeap
      have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
        unspaced pre locs (.word64 value) nf memory locals1 pre.fpRegs uRel
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
        destPresent zeroEq
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe, envsP] using smallerHeap)
      exact ⟨_, writeEval, by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe] using finalRel⟩
    let prefixProg : WordLangProgHOL (BitVec 64) :=
      .ite .test (adjustVar arg) (.imm 1) (.assign 3 (shiftN .asr (.var (adjustVar arg)) 2))
        (.seq (loadBignum conf 1 3 (adjustVar arg))
          (.ite .test 1 (.imm 16) .skip (.assign 3 (.op .sub [.const 0, .var 3]))))
    have compiled : (compileAssign (width := 64) conf n l dest (.wordOp .wordFromInt) [arg] none).1 =
        wordListSeq [prefixProg, writeWord64 conf hd1 dest 3] := by
      simp [compileAssign, arg1, assignWordFromInt, header1, wordListSeq, prefixProg]
    have prefixRun : ∃ pre : WordSemStateFiniteExact 64 C F,
        WordSemStateFiniteExact.evaluate (wordListSeq [prefixProg]) target = (none, pre) ∧
        (∀ s : DataSem.State C F, stateRel conf l1 l2 s pre none locs =
          stateRel conf l1 l2 s target none locs) ∧
        pre.getVar 3 = some (.word value) := by
      obtain ⟨w, wEq, lowIff⟩ := memoryRel_anyNumberImp conf target.be (holThe source.tstamps)
        source.refs source.space target.store target.memory target.mdomain i loc (locals ++ envs)
        ⟨Or.inr rfl, rootsRel⟩
      subst loc
      by_cases small : smallInt 64 i
      · have locSmall := memoryRel_numberImp conf target.be (holThe source.tstamps)
          source.refs source.space target.store target.memory target.mdomain i (.word w) (locals ++ envs)
          ⟨Or.inr rfl, small, rootsRel⟩
        have wEq' : w = smallnum i := by simpa using locSmall
        have low : w.getLsbD 0 = false := by
          cases h : w.getLsbD 0
          · rfl
          · exact absurd small (lowIff.mp h)
        have mask : w &&& 1 = 0 := (StackAlloc.word_and_one_eq_0_iff w).mpr
          (by intro h; rw [low] at h; exact Bool.false_ne_true h)
        have test : wordSemWordCmp .test (.word w) (.word (1#64)) = some true := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (w &&& (1 : BitVec 64) == 0) = true
          exact beq_iff_eq.mpr mask
        refine ⟨target.setVar 3 (.word value), ?_,
          fun s => stateRel_insertOdd conf l1 l2 s target none locs 3 _ rfl, ?_⟩
        · have shifted : w.sshiftRight 2 = value := by
            rw [wEq']; exact smallnum_sshiftRight (by decide) i small
          simp [wordListSeq, prefixProg, WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.getVarImm, locRead, test, WordSemStateFiniteExact.wordExp, shiftN,
            wordShiftHOL, shifted]
        · simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      · obtain ⟨_, w', x, a, vEq, wbit, real, domA, memA, _, _, _, _, _, domB, memB, sign, _⟩ :=
          memoryRel_number_bignumImp_alt conf target.be (holThe source.tstamps) source.refs source.space
            target.store target.memory target.mdomain i (.word w) (locals ++ envs) ⟨rootsRel, small, Or.inr rfl⟩
        cases vEq
        have test : wordSemWordCmp .test (.word w) (.word (1#64)) = some false := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (w &&& (1 : BitVec 64) == 0) = false
          exact beq_eq_false_iff_ne.mpr wbit
        have realEval := Bignum.getRealAddr_lemma conf (adjustVar arg) target w a
          ⟨shiftBound, Or.inr rfl, locRead, real⟩
        let pre0 := ((target.setVar 3 (.word a)).setVar 1 (.word x)).setVar 3 (.word (BitVec.ofNat 64 i.natAbs))
        have rel0 : ∀ s : DataSem.State C F, stateRel conf l1 l2 s pre0 none locs =
            stateRel conf l1 l2 s target none locs := fun s =>
          (stateRel_insertOdd conf l1 l2 s _ none locs 3 _ rfl).trans
            ((stateRel_insertOdd conf l1 l2 s _ none locs 1 _ rfl).trans
              (stateRel_insertOdd conf l1 l2 s target none locs 3 _ rfl))
        have get1 : pre0.getVar 1 = some (.word x) := by
          simp [pre0, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
        have get3 : pre0.getVar 3 = some (.word (BitVec.ofNat 64 i.natAbs)) := by
          simp [pre0, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        have loadRun : WordSemStateFiniteExact.evaluate (loadBignum conf 1 3 (adjustVar arg)) target =
            (none, pre0) := by
          simp [loadBignum, wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
            wordOpHOL, wordOp, theWords, realEval, domA, memA, domB, memB,
            sptLookup_sptInsert_same, sptLookup_sptInsert_ne, pre0]
        have afterLoad : WordSemStateFiniteExact.evaluate prefixProg target =
            WordSemStateFiniteExact.evaluate
              (.ite .test 1 (.imm 16) .skip (.assign 3 (.op .sub [.const 0, .var 3]))) pre0 := by
          conv => lhs; simp only [prefixProg]; rw [WordSemStateFiniteExact.evaluate]
          simp only [WordSemStateFiniteExact.getVarImm, locRead]
          rw [show wordSemWordCmp .test (.word w) (.word (1 : BitVec 64)) = some false from test]
          simp only [WordSemStateFiniteExact.evaluate, loadRun]
          simp [WordSemStateFiniteExact.fixClock, pre0, WordSemStateFiniteExact.setVar]
        by_cases nonneg : 0 ≤ i
        · have zero : x &&& 16 = 0 := sign.mpr nonneg
          have t16 : wordSemWordCmp .test (.word x) (.word (16#64)) = some true := by
            simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
            change (x &&& (16 : BitVec 64) == 0) = true
            exact beq_iff_eq.mpr zero
          refine ⟨pre0, ?_, rel0, ?_⟩
          · simp only [wordListSeq, afterLoad]
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get1, t16]
          · rw [get3]
            congr 2
            simp only [value]
            have h : BitVec.ofInt 64 i = BitVec.ofNat 64 i.natAbs := by
              rw [← BitVec.ofInt_natCast]
              congr 1
              omega
            exact h.symm
        · have nz : x &&& 16 ≠ 0 := fun h => nonneg (sign.mp h)
          have t16 : wordSemWordCmp .test (.word x) (.word (16#64)) = some false := by
            simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
            change (x &&& (16 : BitVec 64) == 0) = false
            exact beq_eq_false_iff_ne.mpr nz
          refine ⟨pre0.setVar 3 (.word value), ?_,
            fun s => (stateRel_insertOdd conf l1 l2 s pre0 none locs 3 _ rfl).trans (rel0 s), ?_⟩
          · simp only [wordListSeq, afterLoad]
            have negEq : (0 : BitVec 64) - BitVec.ofNat 64 i.natAbs = value :=
              zero_sub_ofNat_natAbs i (by omega)
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get1, t16,
              WordSemStateFiniteExact.wordExp, get3, theWords, wordOpHOL, wordOp]
            rw [← negEq]
            simp [BitVec.sub_eq_add_neg]
          · simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    obtain ⟨pre, preRun, relEq, get3⟩ := prefixRun
    obtain ⟨r, writeEval, finalRel⟩ := finish pre relEq get3
    have joined := evalListAppend [prefixProg] (writeWord64 conf hd1 dest 3) target pre preRun
    simp only [List.cons_append, List.nil_append] at joined
    refine ⟨none, r, ?_, by simp, fun _ => ⟨finalRel, rfl⟩⟩
    rw [compiled, joined, writeEval]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
