module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Zero
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StateRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.PostBits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space
public import Flapjack.Compiler.Backend.WordBignum.Proofs.HeapLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange

@[expose] public section

/-! `AnyArith_thm`: storing the result after the bignum call (Flapjack-only
helpers following the HOL proof's "check point 3" onwards). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.WordSemStateFiniteExact.BignumClauses
open Flapjack.Misc.Multiword

/-- The part of `AnyArith_code` after the bignum call. -/
def postCode {width : Nat} [NeZero width] (c : Config) : WordLangProgHOL (BitVec width) :=
  .seq (.get 1 (.temp 10)) (.seq (.ite .test 1 (.reg 1) (.return 0 [1]) .skip)
  (.seq (.assign 3 (.load (.op .add [.lookup .nextFree, .const wordSemBytesInWord])))
  (.seq (.ite .equal 1 (.imm 2)
      (.seq (.assign 5 (shiftN .lsr (.var 3) (width - 3)))
        (.ite .test 5 (.reg 5) (.seq (.assign 1 (shiftN .lsl (.var 3) 2)) (.return 0 [1])) .skip))
      (.ite .equal 1 (.imm 3)
        (.seq (.assign 5 (shiftN .lsr (.op .sub [.var 3, .const 1]) (width - 3)))
          (.ite .test 5 (.reg 5)
            (.seq (.assign 1 (.op .sub [.const 0, shiftN .lsl (.var 3) 2])) (.return 0 [1])) .skip))
        (.assign 5 (.const 0))))
  (.seq (.assign 5 (.lookup .nextFree)) (.seq (.assign 6 (shiftVar .lsr 1 1))
  (.seq (.assign 8 (.op .and [.var 1, .const 1]))
  (.seq (.assign 7 (.op .or [.const 15, shiftVar .lsl 6 (width - c.lenSize), shiftVar .lsl 8 4]))
  (.seq (.store (.var 5) 7) (.seq (.assign 1 (.op .sub [.var 5, .lookup .currHeap]))
  (.seq (.assign 1 (.op .or [shiftVar .lsl 1 (shiftLength c - wordShiftAmount width), .const 1]))
  (.seq (.set .nextFree (.op .add [.var 5, .const wordSemBytesInWord,
      shiftVar .lsl 6 (wordShiftAmount width)]))
    (.return 0 [1]))))))))))))


/-- `AnyArith_code` in the segments used by the proof. -/
theorem anyArithCode_eq {width : Nat} [NeZero width] (c : Config) :
    (anyArithCode c : WordLangProgHOL (BitVec width)) =
      .seq (.assign 1 (.const 4)) (.seq (addNumSize c 0) (.seq (addNumSize c 1)
        (.seq (.set (.temp 29) (.var 1))
        (.seq (allocVar c (2 ^ c.lenSize) (sptListInsert [0, 1, 2] .ln))
        (.seq (anyHeader c 2 false 0 31 12) (.seq (anyHeader c 4 true 1 30 11)
        (setupCode (.seq (.call (some ([1], (.ls (), .ln), .skip, anyArithLocation, 3))
          (some bignumLocation) [] none) (postCode c))))))))) := rfl


/-- What the post-call phase needs to know about the state after the bignum call. -/
structure PostHyps {width : Nat} [NeZero width] {C F : Type} (c : Config) (l1 l2 : Nat)
    (s : DataSem.State C F) (L0 : Spt DataSem.Value) (s9 R0 : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (n : Nat) (heap ha hb : ValueHeap width) (limit a sp sp1 k : Nat)
    (gens : GcCombined.GenState) (curr other : BitVec width) (x0 ow : WordLocW width)
    (v : Int) (zs1 : List (BitVec width)) : Prop where
  rel9 : stateRel c l1 l2 { s with locals := L0, space := n + 1 } s9 none locs
  hims : heapInMemoryStore heap a sp sp1 gens c s9.store s9.memory s9.mdomain limit
  wml : wordMlInv (heap, s9.be, a, sp, sp1, gens) limit (holThe s.tstamps) c s.refs
      ([] ++ joinEnv L0 (sptToAList (sptInter s9.locals (adjustSet L0))) ++
        [(theGlobal s.global, holFapply s9.store .globals)] ++ flatStack s.stack s9.stack)
  lim : (limit + 3) * (width / 8) + 1 < 2 ^ width
  spLe : n + 1 ≤ sp
  hheap : heap = ha ++ .unused (n + k) :: hb
  ha_len : a = heapLength ha
  limNZ : limit ≠ 0
  hys : ((i2mw v : Bool × List (BitVec width)).2 ++ zs1).length = n
  hn : n < 2 ^ c.lenSize
  hstore : ∀ key, (∀ r, key ≠ .temp r) → R0.store.lookup key = s9.store.lookup key
  hmem : SetSep.star
      (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength ha) +
        StackRemove.bytesInWord width)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
      (SetSep.star (SetSep.one (curr + StackRemove.bytesInWord width *
          BitVec.ofNat width (heapLength ha), x0))
        (SetSep.star (SetSep.one (other, ow)) (splitFrame c curr other ha hb n k limit)))
      (SetSep.fun2Set (R0.memory, fun x => R0.mdomain x = true))
  hcurr : s9.store.lookup .currHeap = some (.word curr)
  hother : s9.store.lookup .otherHeap = some (.word other)
  hnext : s9.store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width *
      BitVec.ofNat width (heapLength ha)))
  hffi : R0.ffi = s9.ffi
  hhandler : R0.handler = s9.handler
  hgc : R0.gcFun = s9.gcFun
  hcode : R0.code = s9.code
  hcomp : R0.compile = s9.compile
  horacle : R0.compileOracle = s9.compileOracle
  hcb : R0.codeBuffer = s9.codeBuffer
  hdb : R0.dataBuffer = s9.dataBuffer
  hbe : R0.be = s9.be
  hss : R0.stackSize = s9.stackSize
  hsl : R0.stackLimit = s9.stackLimit
  hstack : R0.stack = s9.stack
  hmax : BackendProps.optionLe (Option.map₂ (· + ·) (wordSemStackSize R0.stack) (some 0)) R0.stackMax
  h10 : R0.store.lookup (.temp 10) = some (.word (mcHeader (i2mw v : Bool × List (BitVec width))))
  h0 : sptLookup 0 R0.locals = some (.loc l1 l2)

/-- The zero-result relation for any state that differs from the post-call
state only in its locals and clock. -/
theorem PostHyps.zero {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s : DataSem.State C F} {L0 : Spt DataSem.Value} {s9 R0 : WordSemStateFiniteExact width C F}
    {locs : List (Nat × Nat)} {n : Nat} {heap ha hb : ValueHeap width} {limit a sp sp1 k : Nat}
    {gens : GcCombined.GenState} {curr other : BitVec width} {x0 ow : WordLocW width}
    {v : Int} {zs1 : List (BitVec width)}
    (P : PostHyps c l1 l2 s L0 s9 R0 locs n heap ha hb limit a sp sp1 k gens curr other x0 ow v zs1)
    (r1 r2 : Nat) (clk : Nat) :
    stateRel c r1 r2
      { s with locals := .ln, localsSize := some 0, stackMax := none, clock := clk,
               space := n + 1 }
      { R0 with locals := .ln, localsSize := some 0, clock := clk }
      (some [(.number 0, .word 0)]) locs :=
  zero_stateRel P.rel9 P.hims P.wml P.lim P.spLe P.hheap P.limNZ (by simpa using P.hys)
    P.hstore P.hmem P.hcurr P.hother P.hffi P.hhandler P.hgc P.hcode P.hcomp P.horacle P.hcb P.hdb
    P.hbe P.hss P.hsl P.hstack rfl rfl P.hmax


/-- The post-call phase of `AnyArith_code`. -/
theorem post_step {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s : DataSem.State C F} {L0 : Spt DataSem.Value} {s9 R0 : WordSemStateFiniteExact width C F}
    {locs : List (Nat × Nat)} {n : Nat} {heap ha hb : ValueHeap width} {limit a sp sp1 k : Nat}
    {gens : GcCombined.GenState} {curr other : BitVec width} {x0 ow : WordLocW width}
    {v : Int} {zs1 : List (BitVec width)}
    (P : PostHyps c l1 l2 s L0 s9 R0 locs n heap ha hb limit a sp sp1 k gens curr other x0 ow v zs1)
    (r1 r2 : Nat) (good : goodDimindex width) (hnw : n < 2 ^ width / 2) :
    ∃ (q : Option (WordSemResult width)) (r : WordSemStateFiniteExact width C F) (new_c : Nat),
      WordSemStateFiniteExact.evaluate (postCode c) R0 = (q, r) ∧
      ∃ rv : WordLocW width, q = some (.result (.loc l1 l2) [rv]) ∧
        stateRel c r1 r2
          { s with locals := .ln, localsSize := some 0, clock := new_c, space := 0,
                   stackMax := none } r (some [(.number v, rv)]) locs := by
  set hv := mcHeader (i2mw v : Bool × List (BitVec width)) with hhv
  have lenV : (i2mw v : Bool × List (BitVec width)).2.length ≤ n := by
    have := P.hys; simp at this; omega
  have hv0 : hv = 0 ↔ v = 0 := mcHeader_i2mw_eq_0w (by omega)
  set R1 := R0.setVar 1 (.word hv)
  have e1 : WordSemStateFiniteExact.evaluate (.get 1 (.temp 10)) R0 = (none, R1) := by
    rw [evaluate_get, WordSemStateFiniteExact.getStore, P.h10]
  have g1 : WordSemStateFiniteExact.getVar 1 R1 = some (.word hv) := by
    simp [R1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  unfold postCode
  rw [evaluate_seq_of_none _ _ _ _ e1]
  rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .reg 1) g1 g1 rfl]
  by_cases v0 : v = 0
  · have hz : hv = 0 := hv0.2 v0
    have bt : (Compiler.Encoders.Asm.wordCmpHOL Cmp.test hv hv) = true := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, hz, beq_iff_eq]
      show (0 : BitVec width) &&& 0 = 0
      simp
    rw [bt, if_pos rfl, evaluate_seq, evaluate_return]
    have g0 : WordSemStateFiniteExact.getVar 0 R1 = some (.loc l1 l2) := by
      simp [R1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_ne _ _ _ _ (by decide : (0 : Nat) ≠ 1), P.h0]
    simp only [g0, WordSemStateFiniteExact.getVars, g1]
    refine ⟨_, _, R0.clock, rfl, .word hv, rfl, ?_⟩
    have Z := state_rel_with_clock_0 (P.zero r1 r2 R0.clock)
    subst v0
    rw [hz]
    exact Z
  have hz : hv ≠ 0 := fun h => v0 (hv0.1 h)
  have bf : (Compiler.Encoders.Asm.wordCmpHOL Cmp.test hv hv) = false := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_eq_false_iff_ne]
    show hv &&& hv ≠ 0
    simpa using hz
  rw [bf, if_neg (by decide), evaluate_seq, evaluate_skip]
  dsimp only
  have ne : (i2mw v : Bool × List (BitVec width)).2 ≠ [] := by
    intro e; exact v0 ((snd_i2mw_nil v).1 e)
  obtain ⟨x, xs, hx⟩ : ∃ x xs, (i2mw v : Bool × List (BitVec width)).2 = x :: xs := by
    cases h : (i2mw v : Bool × List (BitVec width)).2 with
    | nil => exact absurd h ne
    | cons x xs => exact ⟨x, xs, rfl⟩
  set b := StackRemove.bytesInWord width
  set u := curr + b * BitVec.ofNat width (heapLength ha)
  have rd : R0.memory (u + b) = .word x ∧ R0.mdomain (u + b) = true := by
    have H := P.hmem
    rw [hx, List.cons_append, List.map_cons, wordList_cons, ← SetSep.starAssoc] at H
    exact (SetSep.readFun2Set _ _ _ _ _ H)
  have rd1 : R0.memory (u + wordSemBytesInWord) = .word x := rd.1
  have rd2 : R0.mdomain (u + wordSemBytesInWord) = true := rd.2
  set R2 := R1.setVar 3 (.word x)
  have nf : R0.store.lookup .nextFree = some (.word u) := by
    rw [P.hstore _ (by intro r h; cases h), P.hnext]
  have e3 : WordSemStateFiniteExact.evaluate
      (.assign 3 (.load (.op .add [.lookup .nextFree, .const wordSemBytesInWord]))) R1 =
      (none, R2) := by
    rw [evaluate_assign]
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, nf, theWords,
      wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad, R1, WordSemStateFiniteExact.setVar, rd1, rd2]
    rfl
  rw [evaluate_seq_of_none _ _ _ _ e3]
  have g1' : WordSemStateFiniteExact.getVar 1 R2 = some (.word hv) := by
    simp [R2, R1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_ne _ _ _ _ (by decide : (1 : Nat) ≠ 3), sptLookup_sptInsert_same]
  have hlenB : 2 * (i2mw v : Bool × List (BitVec width)).2.length + 1 < 2 ^ width := by omega
  have w4 : 4 < 2 ^ width := by rcases good with h | h <;> subst h <;> norm_num
  have ww : 3 < width := by rcases good with h | h <;> subst h <;> norm_num
  obtain ⟨two, three⟩ := mcHeader_two_three (width := width) v hlenB w4
  have sh3 : (BitVec.ofNat width (width - 3)).toNat = width - 3 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le)
  have sh2 : (BitVec.ofNat width 2).toNat = 2 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have g0' : ∀ L : Spt (WordLocW width), sptLookup 0 L = sptLookup 0 R0.locals →
      WordSemStateFiniteExact.getVar 0 ({ R0 with locals := L } : WordSemStateFiniteExact width C F) =
        some (.loc l1 l2) := by
    intro L h; simp [WordSemStateFiniteExact.getVar, h, P.h0]
  by_cases sm : smallInt width v
  · have single : (i2mw v : Bool × List (BitVec width)).2.length = 1 := by
      by_contra hne
      refine v0 (i2mw_smallInt_imp_0 v ⟨fun v1 e => hne ?_, fun v1 e => hne ?_, sm, good⟩)
      · rw [e]; rfl
      · rw [e]; rfl
    obtain ⟨hx1, lt, _⟩ := i2mw_single v single
    have xe : x = BitVec.ofNat width v.natAbs := by
      rw [hx] at hx1; exact (List.cons.inj hx1).1
    subst xe
    by_cases neg : v < 0
    · obtain ⟨b1, b2⟩ := small_neg_bits good v neg single
      have h3 : hv = 3 := three.2 ⟨neg, single⟩
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 2) g1' rfl rfl]
      have n32 : (3 : BitVec width) ≠ 2 := by
        intro e
        have := congrArg BitVec.toNat e
        simp only [show (3 : BitVec width) = BitVec.ofNat width 3 from rfl,
          show (2 : BitVec width) = BitVec.ofNat width 2 from rfl, BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
      simp only [Compiler.Encoders.Asm.wordCmpHOL, h3, beq_iff_eq, n32,
        if_false]
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 3) g1' rfl rfl]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, h3, beq_self_eq_true, if_true]
      rw [evaluate_seq]
      have g3 : WordSemStateFiniteExact.getVar 3 R2 = some (.word (BitVec.ofNat width v.natAbs)) := by
        simp [R2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_same]
      set R3 := R2.setVar 5 (.word 0)
      set R4 := R3.setVar 1 (.word (smallnum v))
      have eA : WordSemStateFiniteExact.evaluate
          (.seq (.assign 5 (shiftN .lsr (.op .sub [.var 3, .const 1]) (width - 3)))
            (.ite .test 5 (.reg 5)
              (.seq (.assign 1 (.op .sub [.const 0, shiftN .lsl (.var 3) 2])) (.return 0 [1])) .skip))
          R2 = (some (.result (.loc l1 l2) [.word (smallnum v)]),
            WordSemStateFiniteExact.flushState false R4) := by
        have a5 : WordSemStateFiniteExact.evaluate
            (.assign 5 (shiftN .lsr (.op .sub [.var 3, .const 1]) (width - 3))) R2 = (none, R3) := by
          have ex : R2.wordExp (shiftN .lsr (.op .sub [.var 3, .const 1]) (width - 3)) =
              some (.word ((BitVec.ofNat width v.natAbs - 1) >>> (width - 3))) := by
            simp [shiftN, WordSemStateFiniteExact.wordExp, g3, sh3, wordShiftHOL, theWords,
              wordOpHOL, wordOp]
            omega
          rw [evaluate_assign, ex, b1.mp sm]
        rw [evaluate_seq_of_none _ _ _ _ a5, evaluate_ite]
        have g5 : WordSemStateFiniteExact.getVar 5 R3 = some (.word 0) := by
          simp [R3, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        have g3' : WordSemStateFiniteExact.getVar 3 R3 =
            some (.word (BitVec.ofNat width v.natAbs)) := by
          simpa [R3, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (3 : Nat) ≠ 5)] using g3
        simp only [g5, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
          Compiler.Encoders.Asm.wordCmpHOL]
        rw [show (AndOp.and (0 : BitVec width) 0 == 0) = true by
          show ((0 : BitVec width) &&& 0 == 0) = true; simp]
        dsimp only
        have a1 : WordSemStateFiniteExact.evaluate
            (.assign 1 (.op .sub [.const 0, shiftN .lsl (.var 3) 2])) R3 = (none, R4) := by
          have ex : R3.wordExp (.op .sub [.const 0, shiftN .lsl (.var 3) 2]) =
              some (.word (0 - (BitVec.ofNat width v.natAbs) <<< (2 : Nat))) := by
            simp [shiftN, WordSemStateFiniteExact.wordExp, g3', sh2, wordShiftHOL, theWords,
              wordOpHOL, wordOp]
            simp [show ¬ width ≤ 2 by omega]
          rw [evaluate_assign, ex, b2 sm]
        rw [evaluate_seq_of_none _ _ _ _ a1, evaluate_return]
        have g0 : WordSemStateFiniteExact.getVar 0 R4 = some (.loc l1 l2) := by
          simp [R4, R3, R2, R1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (0 : Nat) ≠ 1),
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (0 : Nat) ≠ 3),
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (0 : Nat) ≠ 5), P.h0]
        have g1'' : WordSemStateFiniteExact.getVar 1 R4 = some (.word (smallnum v)) := by
          simp [R4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        simp only [g0, WordSemStateFiniteExact.getVars, g1'']
      rw [eA]
      refine ⟨_, _, R0.clock, rfl, .word (smallnum v), rfl, ?_⟩
      have Z := P.zero r1 r2 R0.clock
      exact state_rel_with_clock_0 (stateRel_number_smallInt c r1 r2 _ _ _ locs v ⟨Z, sm⟩)
    · obtain ⟨b1, b2⟩ := small_pos_bits good v neg single
      have h2 : hv = 2 := two.2 ⟨neg, single⟩
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 2) g1' rfl rfl]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, h2, beq_self_eq_true, if_true]
      rw [evaluate_seq]
      have g3 : WordSemStateFiniteExact.getVar 3 R2 = some (.word (BitVec.ofNat width v.natAbs)) := by
        simp [R2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_same]
      set R3 := R2.setVar 5 (.word 0)
      set R4 := R3.setVar 1 (.word (smallnum v))
      have eA : WordSemStateFiniteExact.evaluate
          (.seq (.assign 5 (shiftN .lsr (.var 3) (width - 3)))
            (.ite .test 5 (.reg 5) (.seq (.assign 1 (shiftN .lsl (.var 3) 2)) (.return 0 [1])) .skip))
          R2 = (some (.result (.loc l1 l2) [.word (smallnum v)]),
            WordSemStateFiniteExact.flushState false R4) := by
        have a5 : WordSemStateFiniteExact.evaluate (.assign 5 (shiftN .lsr (.var 3) (width - 3))) R2 =
            (none, R3) := by
          rw [evaluate_assign, shiftN]
          simp only [WordSemStateFiniteExact.wordExp, g3, sh3, wordShiftHOL]
          rw [if_neg (by omega)]
          simp only [Option.map_some]
          rw [b1.mp sm]
        rw [evaluate_seq_of_none _ _ _ _ a5, evaluate_ite]
        have g5 : WordSemStateFiniteExact.getVar 5 R3 = some (.word 0) := by
          simp [R3, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        have g3' : WordSemStateFiniteExact.getVar 3 R3 =
            some (.word (BitVec.ofNat width v.natAbs)) := by
          simpa [R3, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (3 : Nat) ≠ 5)] using g3
        simp only [g5, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
          Compiler.Encoders.Asm.wordCmpHOL]
        rw [show (AndOp.and (0 : BitVec width) 0 == 0) = true by
          show ((0 : BitVec width) &&& 0 == 0) = true; simp]
        dsimp only
        have a1 : WordSemStateFiniteExact.evaluate (.assign 1 (shiftN .lsl (.var 3) 2)) R3 =
            (none, R4) := by
          rw [evaluate_assign, shiftN]
          simp only [WordSemStateFiniteExact.wordExp, g3', sh2, wordShiftHOL]
          rw [if_neg (by omega)]
          simp only [Option.map_some]
          rw [b2 sm]
        rw [evaluate_seq_of_none _ _ _ _ a1, evaluate_return]
        have g0 : WordSemStateFiniteExact.getVar 0 R4 = some (.loc l1 l2) := by
          simp [R4, R3, R2, R1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (0 : Nat) ≠ 1),
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (0 : Nat) ≠ 3),
            sptLookup_sptInsert_ne _ _ _ _ (by decide : (0 : Nat) ≠ 5), P.h0]
        have g1'' : WordSemStateFiniteExact.getVar 1 R4 = some (.word (smallnum v)) := by
          simp [R4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        simp only [g0, WordSemStateFiniteExact.getVars, g1'']
      rw [eA]
      refine ⟨_, _, R0.clock, rfl, .word (smallnum v), rfl, ?_⟩
      have Z := P.zero r1 r2 R0.clock
      exact state_rel_with_clock_0 (stateRel_number_smallInt c r1 r2 _ _ _ locs v ⟨Z, sm⟩)
  have g3 : WordSemStateFiniteExact.getVar 3 R2 = some (.word x) := by
    simp [R2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have n32 : (3 : BitVec width) ≠ 2 := by
    intro e
    have := congrArg BitVec.toNat e
    simp only [show (3 : BitVec width) = BitVec.ofNat width 3 from rfl,
      show (2 : BitVec width) = BitVec.ofNat width 2 from rfl, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have tst : ∀ y : BitVec width, y ≠ 0 →
      wordSemWordCmp Cmp.test (WordLocW.word y) (WordLocW.word y) = some false := by
    intro y hy
    simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL]
    congr 1
    show (y &&& y == 0) = false
    simpa using hy
  obtain ⟨w5, eIf⟩ : ∃ w5 : BitVec width, ∀ REST : WordLangProgHOL (BitVec width),
      WordSemStateFiniteExact.evaluate (.seq (.ite .equal 1 (.imm 2)
          (.seq (.assign 5 (shiftN .lsr (.var 3) (width - 3)))
            (.ite .test 5 (.reg 5) (.seq (.assign 1 (shiftN .lsl (.var 3) 2)) (.return 0 [1])) .skip))
          (.ite .equal 1 (.imm 3)
            (.seq (.assign 5 (shiftN .lsr (.op .sub [.var 3, .const 1]) (width - 3)))
              (.ite .test 5 (.reg 5)
                (.seq (.assign 1 (.op .sub [.const 0, shiftN .lsl (.var 3) 2])) (.return 0 [1])) .skip))
            (.assign 5 (.const 0)))) REST) R2 =
        WordSemStateFiniteExact.evaluate REST (R2.setVar 5 (.word w5)) := by
    by_cases hc2 : hv = 2
    · obtain ⟨neg, single⟩ := two.1 hc2
      obtain ⟨hx1, _, _⟩ := i2mw_single v single
      have xe : x = BitVec.ofNat width v.natAbs := by rw [hx] at hx1; exact (List.cons.inj hx1).1
      subst xe
      obtain ⟨b1, _⟩ := small_pos_bits good v neg single
      refine ⟨BitVec.ofNat width v.natAbs >>> (width - 3), fun REST => ?_⟩
      have nz : BitVec.ofNat width v.natAbs >>> (width - 3) ≠ 0 := fun h => sm (b1.mpr h)
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 2) g1' rfl rfl]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, hc2, beq_self_eq_true, if_true]
      apply evaluate_seq_of_none
      have ex : R2.wordExp (shiftN .lsr (.var 3) (width - 3)) =
          some (.word (BitVec.ofNat width v.natAbs >>> (width - 3))) := by
        simp [shiftN, WordSemStateFiniteExact.wordExp, g3, sh3, wordShiftHOL]; omega
      rw [evaluate_seq_of_none _ _ _ _ (by rw [evaluate_assign, ex]), evaluate_ite]
      simp only [WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, tst _ nz, evaluate_skip]
    by_cases hc3 : hv = 3
    · obtain ⟨neg, single⟩ := three.1 hc3
      obtain ⟨hx1, _, _⟩ := i2mw_single v single
      have xe : x = BitVec.ofNat width v.natAbs := by rw [hx] at hx1; exact (List.cons.inj hx1).1
      subst xe
      obtain ⟨b1, _⟩ := small_neg_bits good v neg single
      refine ⟨(BitVec.ofNat width v.natAbs - 1) >>> (width - 3), fun REST => ?_⟩
      have nz : (BitVec.ofNat width v.natAbs - 1) >>> (width - 3) ≠ 0 := fun h => sm (b1.mpr h)
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 2) g1' rfl rfl]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq]
      rw [if_neg (show ¬ hv = 2 by rw [hc3]; exact n32)]
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 3) g1' rfl rfl]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq]
      rw [if_pos hc3]
      apply evaluate_seq_of_none
      have ex : R2.wordExp (shiftN .lsr (.op .sub [.var 3, .const 1]) (width - 3)) =
          some (.word ((BitVec.ofNat width v.natAbs - 1) >>> (width - 3))) := by
        simp [shiftN, WordSemStateFiniteExact.wordExp, g3, sh3, wordShiftHOL, theWords,
          wordOpHOL, wordOp]
        omega
      rw [evaluate_seq_of_none _ _ _ _ (by rw [evaluate_assign, ex]), evaluate_ite]
      simp only [WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, tst _ nz, evaluate_skip]
    · refine ⟨0, fun REST => ?_⟩
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 2) g1' rfl rfl]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq, hc2, if_false]
      rw [WordBignum.CompileThmSupport.evaluate_seq_ite (ri := .imm 3) g1' rfl rfl]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq, hc3, if_false]
      apply evaluate_seq_of_none
      rw [evaluate_assign]
      simp [WordSemStateFiniteExact.wordExp]
  rw [eIf]
  have sa : ∀ (S : WordSemStateFiniteExact width C F) (kv : Nat) (e : WordLangExpHOL (BitVec width))
      (w : WordLocW width) (p : WordLangProgHOL (BitVec width)), S.wordExp e = some w →
      WordSemStateFiniteExact.evaluate (.seq (.assign kv e) p) S =
        WordSemStateFiniteExact.evaluate p (S.setVar kv w) := by
    intro S kv e w p h
    exact evaluate_seq_of_none _ _ _ _ (by rw [evaluate_assign, h])
  have lsz := P.hims.2.2.2.1
  have lsz7 := P.hims.2.2.2.2.1
  have shA := P.hims.2.2.1
  have shL := P.hims.2.2.2.2.2.1
  set R5 := R2.setVar 5 (.word w5)
  set ksh := shiftLength c - wordShiftAmount width
  set v6 := hv >>> (1 : Nat)
  set v8 := hv &&& 1
  have nf5 : R5.store.lookup .nextFree = some (.word u) := nf
  have cf : R5.store.lookup .currHeap = some (.word curr) := by
    rw [show R5.store = R0.store from rfl, P.hstore _ (by intro r h; cases h), P.hcurr]
  have one1 : (BitVec.ofNat width 1).toNat = 1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [sa _ 5 _ (.word u) _ (by simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, nf5])]
  rw [sa (R5.setVar 5 (.word u)) 6 (shiftVar .lsr 1 1) (.word v6) _ (by
    simp [shiftVar, shiftN, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, R5, R2, R1, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      wordShiftHOL, one1, v6, show ¬ width ≤ 1 by omega])]
  set S5 := R5.setVar 5 (.word u)
  set S6 := S5.setVar 6 (.word v6)
  rw [sa S6 8 (.op .and [.var 1, .const 1]) (.word v8) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar, S6, S5, R5, R2, R1,
      WordSemStateFiniteExact.getVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne, theWords, wordOpHOL, wordOp, v8]
    show hv &&& ((1 : BitVec width) &&& BitVec.allOnes width) = hv &&& 1
    simp)]
  set S8 := S6.setVar 8 (.word v8)
  set hdr : BitVec width := 15 ||| (v6 <<< (width - c.lenSize) ||| v8 <<< (4 : Nat))
  have m1 : (width - c.lenSize) % 2 ^ width = width - c.lenSize :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le)
  have m4 : 4 % 2 ^ width = 4 := Nat.mod_eq_of_lt (by omega)
  have orE : ∀ a b : BitVec width, OrOp.or a b = a ||| b := fun _ _ => rfl
  rw [sa S8 7 (.op .or [.const 15, shiftVar .lsl 6 (width - c.lenSize), shiftVar .lsl 8 4])
    (.word hdr) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar, S8, S6, S5, R5, R2, R1,
      WordSemStateFiniteExact.getVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne, theWords, wordOpHOL, wordOp, shiftVar,
      shiftN, wordShiftHOL, hdr, show ¬ width - c.lenSize = 0 by omega,
      show ¬ width ≤ width - c.lenSize by omega, show ¬ width ≤ 4 by omega, m1, m4, orE])]
  set S7 := S8.setVar 7 (.word hdr)
  have dU : R0.mdomain u = true := by
    have H : SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow))
        (splitFrame c curr other ha hb n k limit)))
      (SetSep.fun2Set (R0.memory, fun x => R0.mdomain x = true)) := P.hmem
    rw [show SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow))
        (splitFrame c curr other ha hb n k limit))) =
      SetSep.star (SetSep.one (u, x0)) (SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
        (SetSep.star (SetSep.one (other, ow)) (splitFrame c curr other ha hb n k limit))) by
        ac_rfl] at H
    exact (SetSep.readFun2Set _ _ _ _ _ H).2
  set SM : WordSemStateFiniteExact width C F :=
    { S7 with memory := fun a => if a = u then .word hdr else S7.memory a }
  have eSt : WordSemStateFiniteExact.evaluate (.store (.var 5) 7) S7 = (none, SM) := by
    rw [evaluate_store]
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, S7, S8, S6, S5, sptLookup_sptInsert_same,
      sptLookup_sptInsert_ne, WordSemStateFiniteExact.memStore, R5, R2, R1, dU]
    rfl
  rw [evaluate_seq_of_none _ _ _ _ eSt]
  have cf0 : R0.store.lookup .currHeap = some (.word curr) := cf
  rw [sa SM 1 (.op .sub [.var 5, .lookup .currHeap]) (.word (u - curr)) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, SM, S7, S8, S6, S5, sptLookup_sptInsert_same,
      sptLookup_sptInsert_ne, WordSemStateFiniteExact.getStore, cf0, theWords, wordOpHOL, wordOp,
      R5, R2, R1])]
  set S11 := SM.setVar 1 (.word (u - curr))
  set ptr : BitVec width := ((u - curr) <<< ksh) ||| 1
  have mk : ksh % 2 ^ width = ksh := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le)
  rw [sa S11 1 (.op .or [shiftVar .lsl 1 ksh, .const 1]) (.word ptr) _ (by
    by_cases k0 : ksh = 0
    · simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, S11, sptLookup_sptInsert_same, theWords, wordOpHOL, wordOp,
        shiftVar, k0, ptr, orE]
    · simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, S11, sptLookup_sptInsert_same, theWords, wordOpHOL, wordOp,
        shiftVar, shiftN, wordShiftHOL, k0, ptr, orE, mk, show ¬ width ≤ ksh by omega])]
  set S12 := S11.setVar 1 (.word ptr)
  have sa3' : wordShiftAmount width ≤ 3 := by
    unfold wordShiftAmount; split <;> omega
  have sam : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le)
  have sa0 : wordShiftAmount width ≠ 0 := by
    unfold wordShiftAmount; split <;> omega
  have sa3 : wordShiftAmount width ≤ 3 := by
    unfold wordShiftAmount; split <;> omega
  set nfv : BitVec width := u + (wordSemBytesInWord + v6 <<< wordShiftAmount width)
  set S13 := S12.setStore .nextFree (.word nfv)
  have eSet : WordSemStateFiniteExact.evaluate (.set .nextFree (.op .add [.var 5,
      .const wordSemBytesInWord, shiftVar .lsl 6 (wordShiftAmount width)])) S12 = (none, S13) := by
    rw [evaluate_set, if_neg (by simp)]
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, S12, S11, SM, S7, S8, S6, S5, sptLookup_sptInsert_same,
      sptLookup_sptInsert_ne, theWords, wordOpHOL, wordOp, shiftVar, shiftN, wordShiftHOL, sam, sa0,
      show ¬ width ≤ wordShiftAmount width by omega, nfv, S13]
  rw [evaluate_seq_of_none _ _ _ _ eSet, evaluate_return]
  have g0 : WordSemStateFiniteExact.getVar 0 S13 = some (.loc l1 l2) := by
    simp [S13, S12, S11, SM, S7, S8, S6, S5, R5, R2, R1, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne, P.h0]
  have g1f : WordSemStateFiniteExact.getVar 1 S13 = some (.word ptr) := by
    simp [S13, S12, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore, sptLookup_sptInsert_same]
  simp only [g0, WordSemStateFiniteExact.getVars, g1f]
  refine ⟨_, _, R0.clock, rfl, .word ptr, rfl, ?_⟩
  -- the memory after the header store
  set mM : BitVec width → WordLocW width := fun a => if a = u then .word hdr else R0.memory a
  have hmemM : SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
      (SetSep.star (SetSep.one (u, .word hdr)) (SetSep.star (SetSep.one (other, ow))
        (splitFrame c curr other ha hb n k limit)))
      (SetSep.fun2Set (mM, fun x => R0.mdomain x = true)) := by
    have H : SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow))
        (splitFrame c curr other ha hb n k limit)))
      (SetSep.fun2Set (R0.memory, fun x => R0.mdomain x = true)) := P.hmem
    rw [show SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow))
        (splitFrame c curr other ha hb n k limit))) =
      SetSep.star (SetSep.one (u, x0)) (SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
        (SetSep.star (SetSep.one (other, ow)) (splitFrame c curr other ha hb n k limit))) by
        ac_rfl] at H
    have H2 := SetSep.writeFun2Set (WordLocW.word hdr) u x0 _ _ _ H
    have upd : (fun x => @ite _ (x = u) (Classical.propDecidable _) (WordLocW.word hdr) (R0.memory x)) =
        mM := by funext x; by_cases h : x = u <;> simp [h, mM]
    rw [upd] at H2
    rw [show SetSep.star (SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
        (SetSep.star (SetSep.one (other, ow)) (splitFrame c curr other ha hb n k limit)))
        (SetSep.one (u, WordLocW.word hdr)) =
      SetSep.star (Misc.wordList (u + b)
        (((i2mw v : Bool × List (BitVec width)).2 ++ zs1).map WordLocW.word))
      (SetSep.star (SetSep.one (u, .word hdr)) (SetSep.star (SetSep.one (other, ow))
        (splitFrame c curr other ha hb n k limit))) by ac_rfl] at H2
    exact H2
  set X : WordSemStateFiniteExact width C F :=
    { R0 with locals := .ln, localsSize := some 0, memory := mM }
  have Z := zero_stateRel (R := X) (r1 := r1) (r2 := r2) P.rel9 P.hims P.wml P.lim P.spLe P.hheap
    P.limNZ (by simpa using P.hys) P.hstore hmemM P.hcurr P.hother P.hffi P.hhandler P.hgc P.hcode
    P.hcomp P.horacle P.hcb P.hdb P.hbe P.hss P.hsl P.hstack rfl rfl P.hmax
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, M0⟩ := Z
  have nfX : X.store.lookup .nextFree = some (.word u) := nf
  have large : ¬ smallInt width v := sm
  have encoded : encodeHeader c (((if decide (v < 0) then 1 else 0 : BitVec width) <<< 2) ||| 3).toNat
      (i2mw v : Bool × List (BitVec width)).2.length = some hdr := by
    have tl := tag_lt good (decide (v < 0))
    have p6 : 64 ≤ 2 ^ (width - c.lenSize - 2) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 6 ≤ width - c.lenSize - 2 by omega))
    have p16 : 64 ≤ 2 ^ width / 16 := by rcases good with h | h <;> rw [h] <;> norm_num
    have pl : 2 ^ c.lenSize ≤ 2 ^ (width - 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hn := P.hn
    unfold encodeHeader
    rw [if_pos ⟨by omega, by omega, by omega, by omega⟩]
    congr 1
    have e6 : v6 = BitVec.ofNat width (i2mw v : Bool × List (BitVec width)).2.length :=
      header_shift1 v hlenB
    have e8 : v8 = (if decide (v < 0) then 1 else 0 : BitVec width) := by
      show mcHeader (decide (v < 0), (n2mw v.natAbs : List (BitVec width))) &&& 1 = _
      rw [mcHeader_AND_1]
      cases decide (v < 0) <;> rfl
    simp only [hdr, e6, e8, makeHeader, BitVec.or_assoc, header_bits good]
    ac_rfl
  obtain ⟨ne, curr', m1, hne, hcu, hsl', M1⟩ := memoryRel_bignumAlt c X.be _ s.refs (n + 1) X.store
    X.memory X.mdomain _ v (decide (v < 0)) (i2mw v : Bool × List (BitVec width)).2 hdr M0 good large
    (by simp [bignumRep, i2mw]) (by omega) encoded
  rw [nfX] at hne
  cases hne
  rw [show X.store.lookup .currHeap = R0.store.lookup .currHeap from rfl, cf0] at hcu
  cases hcu
  -- the stored header and payload were already in place
  have m1e : m1 = mM := by
    have H := hmemM
    rw [List.map_append, WordBignum.wordListAppendWordBignum] at H
    have shape : ∀ (A B C D : ((BitVec width × WordLocW width) → Prop) → Prop),
        SetSep.star (SetSep.star A B) (SetSep.star C D) =
          SetSep.star (SetSep.star C A) (SetSep.star B D) := by
      intro A B C D; ac_rfl
    rw [shape, ← wordList_cons] at H
    have := wordList_imp_storeList _ _ _ _ _ H
    rw [show X.memory = mM from rfl] at hsl'
    rw [this] at hsl'
    exact (Option.some.inj hsl').symm
  subst m1e
  set L := (i2mw v : Bool × List (BitVec width)).2.length
  have e6 : v6 = BitVec.ofNat width L := header_shift1 v hlenB
  have nfvE : nfv = u + wordSemBytesInWord * BitVec.ofNat width (L + 1) := by
    simp only [nfv, e6, shiftAmount_bytes good, BitVec.ofNat_add]
    rw [show (1#width : BitVec width) = 1 from rfl]
    show u + (StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width L) =
      u + StackRemove.bytesInWord width * (BitVec.ofNat width L + 1)
    ring
  set F := WordSemStateFiniteExact.flushState false S13
  have stEq : F.store = X.store.update (.nextFree,
      .word (u + wordSemBytesInWord * BitVec.ofNat width (L + 1))) := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [F, S13, WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.setStore,
      HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE, nfvE]
    by_cases h : key = .nextFree
    · subst h; simp
    · have h2 : ¬ WordStore.nextFree = key := fun e => h e.symm
      simp [h, h2, X, S12, S11, SM, S7, S8, S6, S5, R5, R2, R1, WordSemStateFiniteExact.setVar]
  have nt : ∀ key, key ≠ .nextFree → F.store.lookup key = X.store.lookup key := by
    intro key h
    rw [stEq]
    have h2 : ¬ WordStore.nextFree = key := fun e => h e.symm
    simp [HolFiniteMapExact.update, FUPDATE, h2]
  refine ⟨z1, z2, z3, z4, z5, ?_, z7, z8, z9, ?_, (fun h => by cases h), z12, z13, z14, z15, z16,
    z17, z18, ?_, ?_⟩
  · unfold codeOracleRel at z6 ⊢
    rw [nt _ (by simp), nt _ (by simp), nt _ (by simp), nt _ (by simp)]
    exact z6
  · intro key hk
    simp only [List.mem_singleton] at hk
    subst hk
    rw [nt _ (by simp)]
    exact z10 _ (by simp)
  · rw [nt _ (by simp)]
    exact z19
  · have M2 := memoryRel_zeroSpace _ _ _ _ _ _ _ _ _ M1
    rw [← stEq] at M2
    apply memoryRel_rearrange _ _ _ _ _ _ _ _ _ _ _ M2
    intro pair hp
    have hg : holFapply F.store .globals = holFapply X.store .globals := by
      unfold holFapply; rw [nt _ (by simp)]
    simp only [Option.getD, List.mem_append, List.mem_cons, hg] at hp ⊢
    have mp : Build.makePtr c (u - curr) (0 : BitVec width) L = (WordLocW.word ptr : WordLocW width) :=
      rfl
    rcases hp with (((h | h) | h) | (h | h)) | h
    · left; rw [mp]; exact h
    · simp at h
    · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
    · simp at h
    · exact Or.inr (Or.inr h)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
