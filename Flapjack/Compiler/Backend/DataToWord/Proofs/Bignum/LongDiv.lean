module

public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.ShiftVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StackMax
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Misc.Multiword.SingleDivFull
public import Flapjack.Misc.Multiword.SingleWord
public import Flapjack.Misc.GoodDimindex

@[expose] public section

/-! Correctness of the generated software long-division loop `LongDiv1_code`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Misc.Multiword
open Flapjack.SemanticPrimitivesProps

namespace LongDivWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end LongDivWitness

private theorem mwCmp_two {width : Nat} [NeZero width] (a1 a2 b1 b2 : BitVec width) :
    mwCmp [a1, a2] [b1, b2] =
      if a2 = b2 then (if a1 = b1 then none else some (decide (a1 < b1)))
      else some (decide (a2 < b2)) := by
  rw [mwCmp]
  simp only [reduceCtorEq, if_false, holLast, List.dropLast]
  split
  · rw [mwCmp]
    simp only [reduceCtorEq, if_false, holLast, List.dropLast]
    split
    · rw [mwCmp]; simp
    · rfl
  · rfl

private theorem andOp_eq {width : Nat} (x y : BitVec width) : AndOp.and x y = x &&& y := rfl

private theorem orOp_eq {width : Nat} (x y : BitVec width) : OrOp.or x y = x ||| y := rfl

private theorem singleDivLoop_succ {width : Nat} [NeZero width] (k : Nat)
    (hk : k + 1 < 2 ^ width) (ns : List (BitVec width)) (m : BitVec width)
    (is : List (BitVec width)) :
    singleDivLoop (BitVec.ofNat width (k + 1), ns, m, is) =
      if mwCmp is (mwShift ns) = some true then
        singleDivLoop (BitVec.ofNat width k, mwShift ns, m <<< (1 : Nat), is)
      else
        singleDivLoop (BitVec.ofNat width k, mwShift ns, m <<< (1 : Nat) + 1,
          (mwSub is (mwShift ns) true).1) := by
  have ne : ¬ BitVec.ofNat width (k + 1) = 0 := by
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
    simp at this
  have km1 : BitVec.ofNat width (k + 1) - 1 = BitVec.ofNat width k := by
    rw [← BitVec.ofNat_add_ofNat]; exact BitVec.add_sub_cancel _ _
  rw [singleDivLoop]
  simp only [ne, if_false, km1]

private theorem seqAssign {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign k e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setVar k v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

private theorem wordExp_shiftVar_of {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (sh : Shift) (v n : Nat) (w : BitVec width)
    (h : sptLookup v t.locals = some (.word w)) :
    t.wordExp (shiftVar sh v n) = some (.word (shiftLookup sh w n)) := by
  rw [wordExpShiftVar, h]

private theorem seqSkipIte {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (q : WordLangProgHOL (BitVec width))
    (p : WordLangProgHOL (BitVec width))
    (h : WordSemStateFiniteExact.evaluate q t = (none, t)) :
    WordSemStateFiniteExact.evaluate (.seq q p) t = WordSemStateFiniteExact.evaluate p t := by
  simp only [WordSemStateFiniteExact.evaluate, h, WordSemStateFiniteExact.fixClock]
  simp

/-- The generated recursive call enters the loop body with the seven loop registers. -/
private theorem evalRecur {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (c : Config) (args : List Nat)
    (vals : List (WordLocW width))
    (hcode : sptLookup longDiv1Location t.code = some (7, longDiv1Code c))
    (hclock : t.clock ≠ 0)
    (hvals : WordSemStateFiniteExact.getVars args t = some vals)
    (hlen : vals.length = 7) (l1 l2 : Nat) (ys : List (WordLocW width))
    (s : WordSemStateFiniteExact width C F)
    (hrun : WordSemStateFiniteExact.evaluate (longDiv1Code c)
      (WordSemStateFiniteExact.callEnv vals (sptLookup longDiv1Location t.stackSize)
        (WordSemStateFiniteExact.decClock t)) = (some (.result (.loc l1 l2) ys), s)) :
    WordSemStateFiniteExact.evaluate (.call none (some longDiv1Location) args none) t =
      (some (.result (.loc l1 l2) ys), s) := by
  simp [WordSemStateFiniteExact.evaluate, hvals, wordSemBadDestArgs, wordSemAddRetLoc,
    wordSemFindCode, hcode, hlen, hclock, hrun, wordSemBadFunReturn]

private theorem seqSome {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (q p : WordLangProgHOL (BitVec width))
    (r : WordSemResult width) (s : WordSemStateFiniteExact width C F)
    (h : WordSemStateFiniteExact.evaluate q t = (some r, s))
    (hc : s.clock ≤ t.clock) (ht : s.termdep = t.termdep) :
    WordSemStateFiniteExact.evaluate (.seq q p) t = (some r, s) := by
  simp only [WordSemStateFiniteExact.evaluate, h, WordSemStateFiniteExact.fixClock]
  simp only [Prod.mk.injEq, true_and]
  rw [if_neg (Nat.not_lt.mpr hc), ← ht]

private theorem iteTrue {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec width))
    (c1 c2 : WordLangProgHOL (BitVec width)) (x y : WordLocW width)
    (h1 : WordSemStateFiniteExact.getVar r1 t = some x)
    (h2 : WordSemStateFiniteExact.getVarImm ri t = some y)
    (hc : wordSemWordCmp cmp x y = some true) :
    WordSemStateFiniteExact.evaluate (.ite cmp r1 ri c1 c2) t =
      WordSemStateFiniteExact.evaluate c1 t := by
  rw [WordSemStateFiniteExact.evaluate]; simp [h1, h2, hc]

private theorem iteFalse {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec width))
    (c1 c2 : WordLangProgHOL (BitVec width)) (x y : WordLocW width)
    (h1 : WordSemStateFiniteExact.getVar r1 t = some x)
    (h2 : WordSemStateFiniteExact.getVarImm ri t = some y)
    (hc : wordSemWordCmp cmp x y = some false) :
    WordSemStateFiniteExact.evaluate (.ite cmp r1 ri c1 c2) t =
      WordSemStateFiniteExact.evaluate c2 t := by
  rw [WordSemStateFiniteExact.evaluate]; simp [h1, h2, hc]

private theorem evalSkip {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate .skip t = (none, t) := by
  rw [WordSemStateFiniteExact.evaluate]

private theorem seqInst {width : Nat} [NeZero width] {C F : Type}
    (t s : WordSemStateFiniteExact width C F) (i : WordLangInst (BitVec width))
    (p : WordLangProgHOL (BitVec width)) (h : WordSemStateFiniteExact.inst i t = some s)
    (hc : s.clock = t.clock) (ht : s.termdep = t.termdep) :
    WordSemStateFiniteExact.evaluate (.seq (.inst i) p) t =
      WordSemStateFiniteExact.evaluate p s := by
  simp only [WordSemStateFiniteExact.evaluate, h, WordSemStateFiniteExact.fixClock]
  rw [← hc, if_neg (lt_irrefl _), ← ht]

private theorem ofNat_add3 {width : Nat} [NeZero width] (a b : BitVec width) (c : Nat) :
    BitVec.ofNat width (a.toNat + b.toNat + c) = a + b + BitVec.ofNat width c := by
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.ofNat_add_ofNat]; simp

private theorem xor_negOne {width : Nat} (x : BitVec width) : x ^^^ -1 = ~~~x := by
  show x ^^^ -1#width = ~~~x
  rw [BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]

/-- The two-digit subtraction of `single_div_loop` as two generated add-with-carry steps. -/
private theorem mwSub_two_eq {width : Nat} [NeZero width] (i1 i2 x1 x2 : BitVec width) :
    (mwSub [i1, i2] [x1, x2] true).1 =
      [(wordAddCarryHOL i1 (x1 ^^^ -1) 1).1,
        (wordAddCarryHOL i2 (x2 ^^^ -1) (wordAddCarryHOL i1 (x1 ^^^ -1) 1).2).1] := by
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  simp only [mwSub, singleSub, singleAdd, wordAddCarryHOL, xor_negOne, b2w, b2n, ofNat_add3]
  have hw0 : width ≠ 0 := NeZero.ne width
  simp [hw0]
  rcases Nat.lt_or_ge (i1.toNat + (2 ^ width - 1 - x1.toNat) + 1) (2 ^ width) with h | h
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.not_lt.mpr h]

/-- One run of the generated software long-division loop follows `single_div_loop`;
the stack maximum is either unchanged or grown by the loop's own frame. The
evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "LongDiv1_thm'"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem longDiv1_thm' {width : Nat} [NeZero width] {C F : Type} :
    ∀ (k : Nat) (n1 n2 m i1 i2 : BitVec width) (t2 : WordSemStateFiniteExact width C F)
      (r1 r2 : Nat) (m1 : BitVec width) (is1 : List (BitVec width)) (c : Config),
      singleDivLoop (BitVec.ofNat width k, [n1, n2], m, [i1, i2]) = (m1, is1) ∧
      sptLookup longDiv1Location t2.code = some (7, longDiv1Code c) ∧
      sptLookup 0 t2.locals = some (.loc r1 r2) ∧
      sptLookup 2 t2.locals = some (.word (BitVec.ofNat width k)) ∧
      sptLookup 4 t2.locals = some (.word n2) ∧
      sptLookup 6 t2.locals = some (.word n1) ∧
      sptLookup 8 t2.locals = some (.word m) ∧
      sptLookup 10 t2.locals = some (.word i1) ∧
      sptLookup 12 t2.locals = some (.word i2) ∧
      k < 2 ^ width ∧ k < t2.clock ∧ goodDimindex width ∧ ¬ c.hasLongdiv →
      ∃ (j1 j2 : BitVec width) (maxStack : Option Nat),
        is1 = [j1, j2] ∧
        WordSemStateFiniteExact.evaluate (longDiv1Code c) t2 =
          (some (.result (.loc r1 r2) [.word m1]),
            { t2 with clock := t2.clock - k, locals := .ln, localsSize := some 0,
                      stackMax := maxStack,
                      store := t2.store.updateEq (.temp 28, .word (holHd is1)) }) ∧
        (maxStack = t2.stackMax ∨
          maxStack = Option.map₂ max t2.stackMax
            (Option.map₂ (· + ·) (wordSemStackSize t2.stack)
              (sptLookup longDiv1Location t2.stackSize))) := by
  intro k
  induction k with
  | zero =>
    intro n1 n2 m i1 i2 t2 r1 r2 m1 is1 c
      ⟨hloop, hcode, h0, h2, h4, h6, h8, h10, h12, hk, hclock, good, hld⟩
    rw [singleDivLoop] at hloop
    simp only [BitVec.ofNat_eq_ofNat, if_true] at hloop
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloop
    refine ⟨i1, i2, t2.stackMax, rfl, ?_, Or.inl rfl⟩
    simp [longDiv1Code, hld, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
      WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.fixClock, wordSemWordCmp,
      Compiler.Encoders.Asm.wordCmpHOL, andOp_eq, h0, h2, h8, h10, holHd]
  | succ k ih =>
    intro n1 n2 m i1 i2 t2 r1 r2 m1 is1 c
      ⟨hloop, hcode, h0, h2, h4, h6, h8, h10, h12, hk, hclock, good, hld⟩
    have hk' : k < 2 ^ width := by omega
    have hw : 1 < width := by rcases good with h | h <;> omega
    have ne : ¬ BitVec.ofNat width (k + 1) = 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
      simp at this
    have km1 : BitVec.ofNat width (k + 1) - 1 = BitVec.ofNat width k := by
      rw [← BitVec.ofNat_add_ofNat]; exact BitVec.add_sub_cancel _ _
    -- The loop body up to the comparisons.
    let n1' : BitVec width := n1 >>> (1 : Nat) ||| n2 <<< (width - 1)
    let n2' : BitVec width := n2 >>> (1 : Nat)
    have one_mod : 1 % 2 ^ width = 1 := Nat.one_mod_two_pow_eq_one.2 (by omega)
    have hsh : mwShift [n1, n2] = [n1', n2'] := by simp [mwShift, n1', n2']
    rw [singleDivLoop_succ k hk, hsh, mwCmp_two] at hloop
    let t3 := (((t2.setVar 6 (.word n1')).setVar 4 (.word n2')).setVar 8
      (.word (m <<< (1 : Nat)))).setVar 2 (.word (BitVec.ofNat width k))
    have eA : t2.wordExp (.op .or [shiftVar .lsr 6 1, shiftVar .lsl 4 (width - 1)]) =
        some (.word n1') := by
      have a := wordExp_shiftVar_of t2 .lsr 6 1 n1 h6
      have b := wordExp_shiftVar_of t2 .lsl 4 (width - 1) n2 h4
      simp [WordSemStateFiniteExact.wordExp, a, b, theWords, wordOpHOL, wordOp, shiftLookup, n1',
        orOp_eq]
    have body : WordSemStateFiniteExact.evaluate (longDiv1Code c) t2 =
        WordSemStateFiniteExact.evaluate (wordListSeq
          [.ite .lower 12 (.reg 4)
              (.call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none) .skip,
            .ite .equal 12 (.reg 4)
              (.ite .lower 10 (.reg 6)
                (.call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none) .skip) .skip,
            .assign 8 (.op .add [.var 8, .const 1]),
            .assign 16 (.op .xor [.var 6, .const (-1)]),
            .assign 14 (.op .xor [.var 4, .const (-1)]), .assign 1 (.const 1),
            .inst (.arith (.addCarry 10 10 16 1)), .inst (.arith (.addCarry 12 12 14 1)),
            .call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none]) t3 := by
      have test : (BitVec.ofNat width (k + 1) == 0#width) = false := by simpa using ne
      have top : WordSemStateFiniteExact.evaluate (longDiv1Code c) t2 =
          WordSemStateFiniteExact.evaluate (wordListSeq
            [.assign 6 (.op .or [shiftVar .lsr 6 1, shiftVar .lsl 4 (width - 1)]),
            .assign 4 (shiftVar .lsr 4 1), .assign 8 (shiftVar .lsl 8 1),
            .assign 2 (.op .sub [.var 2, .const 1]),
            .ite .lower 12 (.reg 4)
              (.call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none) .skip,
            .ite .equal 12 (.reg 4)
              (.ite .lower 10 (.reg 6)
                (.call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none) .skip) .skip,
            .assign 8 (.op .add [.var 8, .const 1]),
            .assign 16 (.op .xor [.var 6, .const (-1)]),
            .assign 14 (.op .xor [.var 4, .const (-1)]), .assign 1 (.const 1),
            .inst (.arith (.addCarry 10 10 16 1)), .inst (.arith (.addCarry 12 12 14 1)),
            .call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none]) t2 := by
        conv_lhs => rw [longDiv1Code]
        simp [hld, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
          WordSemStateFiniteExact.getVar, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
          andOp_eq, h2, test]
      rw [top]
      simp only [wordListSeq.eq_3, wordListSeq.eq_2]
      rw [seqAssign _ _ _ _ _ eA]
      rw [seqAssign _ _ _ (.word n2') _ (wordExp_shiftVar_of _ .lsr 4 1 n2 (by
        simp [WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, h4]))]
      rw [seqAssign _ _ _ (.word (m <<< (1 : Nat))) _ (wordExp_shiftVar_of _ .lsl 8 1 m (by
        simp [WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, h8]))]
      rw [seqAssign _ _ _ (.word (BitVec.ofNat width k)) _ (by
        simp [WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, h2, theWords, wordOpHOL, wordOp]
        exact km1)]
    -- Entering the recursive call from any register file with the loop registers.
    have finish : ∀ (L : Spt (WordLocW width)) (a b mm : BitVec width),
        sptLookup 0 L = some (.loc r1 r2) →
        sptLookup 2 L = some (.word (BitVec.ofNat width k)) →
        sptLookup 4 L = some (.word n2') → sptLookup 6 L = some (.word n1') →
        sptLookup 8 L = some (.word mm) → sptLookup 10 L = some (.word a) →
        sptLookup 12 L = some (.word b) →
        singleDivLoop (BitVec.ofNat width k, [n1', n2'], mm, [a, b]) = (m1, is1) →
        ∃ (j1 j2 : BitVec width) (maxStack : Option Nat), is1 = [j1, j2] ∧
          WordSemStateFiniteExact.evaluate
            (.call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none)
            { t2 with locals := L } =
            (some (.result (.loc r1 r2) [.word m1]),
              { t2 with clock := t2.clock - (k + 1), locals := .ln, localsSize := some 0,
                        stackMax := maxStack,
                        store := t2.store.updateEq (.temp 28, .word (holHd is1)) }) ∧
          (maxStack = t2.stackMax ∨
            maxStack = Option.map₂ max t2.stackMax
              (Option.map₂ (· + ·) (wordSemStackSize t2.stack)
                (sptLookup longDiv1Location t2.stackSize))) := by
      intro L a b mm g0 g2 g4 g6 g8 g10 g12 run
      let vals : List (WordLocW width) := [.loc r1 r2, .word (BitVec.ofNat width k), .word n2',
        .word n1', .word mm, .word a, .word b]
      let next := WordSemStateFiniteExact.callEnv vals
        (sptLookup longDiv1Location t2.stackSize)
        (WordSemStateFiniteExact.decClock { t2 with locals := L })
      obtain ⟨j1, j2, mx, his, hrun, hmx⟩ := ih n1' n2' mm a b next r1 r2 m1 is1 c
        ⟨run, by simpa [next, WordSemStateFiniteExact.callEnv,
            WordSemStateFiniteExact.decClock] using hcode,
          by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
          by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
          by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
          by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
          by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
          by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
          by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
          hk', by simp [next, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]; omega,
          good, hld⟩
      have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
        cases x <;> cases y <;> rfl
      have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
        cases x <;> cases y <;> rfl
      have idem (x y : Option Nat) :
          Option.map₂ max (Option.map₂ max x y) y = Option.map₂ max x y := by
        cases x <;> cases y <;> simp [Option.map₂]
      refine ⟨j1, j2, mx, his, ?_, Or.inr ?_⟩
      · rw [evalRecur ({ t2 with locals := L } : WordSemStateFiniteExact width C F) c
          [0, 2, 4, 6, 8, 10, 12] vals hcode (by simp; omega)
          (by simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
            g0, g2, g4, g6, g8, g10, g12, vals]) rfl r1 r2 _ _ hrun]
        simp [next, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, Nat.sub_sub,
          Nat.add_comm]
      · rcases hmx with h | h <;>
          simp only [h, next, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
            optMax, optAdd, idem]
    rw [body]
    let L3 := sptInsert 2 (.word (BitVec.ofNat width k)) (sptInsert 8 (.word (m <<< (1 : Nat)))
      (sptInsert 4 (.word n2') (sptInsert 6 (.word n1') t2.locals)))
    have t3eq : t3 = { t2 with locals := L3 } := rfl
    have g0 : sptLookup 0 L3 = some (.loc r1 r2) := by simp [L3, sptLookup_sptInsert_ne, h0]
    have g2 : sptLookup 2 L3 = some (.word (BitVec.ofNat width k)) := by
      simp [L3, sptLookup_sptInsert_same]
    have g4 : sptLookup 4 L3 = some (.word n2') := by
      simp [L3, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have g6 : sptLookup 6 L3 = some (.word n1') := by
      simp [L3, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have g8 : sptLookup 8 L3 = some (.word (m <<< (1 : Nat))) := by
      simp [L3, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have g10 : sptLookup 10 L3 = some (.word i1) := by simp [L3, sptLookup_sptInsert_ne, h10]
    have g12 : sptLookup 12 L3 = some (.word i2) := by simp [L3, sptLookup_sptInsert_ne, h12]
    rw [t3eq]
    simp only [wordListSeq.eq_3, wordListSeq.eq_2]
    let T := ({ t2 with locals := L3 } : WordSemStateFiniteExact width C F)
    have q0 : WordSemStateFiniteExact.getVar 4 T = some (.word n2') := g4
    have q1 : WordSemStateFiniteExact.getVarImm (.reg 4) T = some (.word n2') := g4
    have q2 : WordSemStateFiniteExact.getVar 12 T = some (.word i2) := g12
    have q3 : WordSemStateFiniteExact.getVar 10 T = some (.word i1) := g10
    have q4 : WordSemStateFiniteExact.getVarImm (.reg 6) T = some (.word n1') := g6
    by_cases c1 : i2 < n2'
    · have hne : ¬ i2 = n2' := fun e => by rw [e] at c1; exact absurd c1 (BitVec.lt_irrefl _)
      have run : singleDivLoop (BitVec.ofNat width k, [n1', n2'], m <<< (1 : Nat), [i1, i2]) =
          (m1, is1) := by simpa [hne, c1] using hloop
      obtain ⟨j1, j2, mx, his, hrun, hmx⟩ := finish L3 i1 i2 _ g0 g2 g4 g6 g8 g10 g12 run
      refine ⟨j1, j2, mx, his, ?_, hmx⟩
      rw [seqSome _ _ _ _ _ ((iteTrue T _ _ _ _ _ _ _ q2 q1
        (by simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, c1])).trans hrun)
        (Nat.sub_le t2.clock (k + 1)) rfl]
    have skip1 : WordSemStateFiniteExact.evaluate
        (.ite .lower 12 (.reg 4) (.call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none) .skip)
        ({ t2 with locals := L3 } : WordSemStateFiniteExact width C F) =
        (none, { t2 with locals := L3 }) := by
      rw [iteFalse T _ _ _ _ _ _ _ q2 q1
        (by simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, c1]), evalSkip]
    rw [seqSkipIte _ _ _ skip1]
    by_cases c2 : i2 = n2' ∧ i1 < n1'
    · obtain ⟨e2, l1⟩ := c2
      have hne : ¬ i1 = n1' := fun e => by rw [e] at l1; exact absurd l1 (BitVec.lt_irrefl _)
      have run : singleDivLoop (BitVec.ofNat width k, [n1', n2'], m <<< (1 : Nat), [i1, i2]) =
          (m1, is1) := by simpa [hne, e2, l1] using hloop
      obtain ⟨j1, j2, mx, his, hrun, hmx⟩ := finish L3 i1 i2 _ g0 g2 g4 g6 g8 g10 g12 run
      refine ⟨j1, j2, mx, his, ?_, hmx⟩
      rw [seqSome _ _ _ _ _ ((iteTrue T _ _ _ _ _ _ _ q2 q1
        (by simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, e2])).trans
          ((iteTrue T _ _ _ _ _ _ _ q3 q4
            (by simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, l1])).trans hrun))
        (Nat.sub_le t2.clock (k + 1)) rfl]
    -- Neither comparison holds: subtract and set the low quotient bit.
    have notTrue : ¬ (if i2 = n2' then (if i1 = n1' then none else some (decide (i1 < n1')))
        else some (decide (i2 < n2'))) = some true := by
      by_cases e2 : i2 = n2'
      · have l1 : ¬ i1 < n1' := fun l => c2 ⟨e2, l⟩
        by_cases e1 : i1 = n1' <;> simp [e2, e1, l1]
      · simp [e2, c1]
    rw [if_neg notTrue, mwSub_two_eq] at hloop
    have skip2 : WordSemStateFiniteExact.evaluate
        (.ite .equal 12 (.reg 4) (.ite .lower 10 (.reg 6)
          (.call none (some longDiv1Location) [0, 2, 4, 6, 8, 10, 12] none) .skip) .skip)
        ({ t2 with locals := L3 } : WordSemStateFiniteExact width C F) =
        (none, { t2 with locals := L3 }) := by
      by_cases e2 : i2 = n2'
      · have l1 : ¬ i1 < n1' := fun l => c2 ⟨e2, l⟩
        rw [iteTrue T _ _ _ _ _ _ _ q2 q1
          (by simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, e2]),
          iteFalse T _ _ _ _ _ _ _ q3 q4
          (by simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, l1]), evalSkip]
      · rw [iteFalse T _ _ _ _ _ _ _ q2 q1
          (by simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, e2]), evalSkip]
    rw [seqSkipIte _ _ _ skip2]
    let a1 := wordAddCarryHOL i1 (n1' ^^^ -1) 1
    let a2 := wordAddCarryHOL i2 (n2' ^^^ -1) a1.2
    let TA := T.setVar 8 (.word (m <<< (1 : Nat) + 1))
    let TB := TA.setVar 16 (.word (n1' ^^^ -1))
    let TC := TB.setVar 14 (.word (n2' ^^^ -1))
    let T4 := TC.setVar 1 (.word 1)
    let T5 := (T4.setVar 10 (.word a1.1)).setVar 1 (.word a1.2)
    let T6 := (T5.setVar 12 (.word a2.1)).setVar 1 (.word a2.2)
    obtain ⟨j1, j2, mx, his, hrun, hmx⟩ := finish T6.locals a1.1 a2.1 (m <<< (1 : Nat) + 1)
      (by simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, g0])
      (by simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, g2])
      (by simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, g4])
      (by simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, g6])
      (by simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
        sptLookup_sptInsert_same])
      (by simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
        sptLookup_sptInsert_same])
      (by simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
        sptLookup_sptInsert_same])
      hloop
    refine ⟨j1, j2, mx, his, ?_, hmx⟩
    rw [seqAssign T _ _ (.word (m <<< (1 : Nat) + 1)) _ (by
      simp [T, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, g8, theWords,
        wordOpHOL, wordOp])]
    rw [seqAssign TA _ _ (.word (n1' ^^^ -1)) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, g6, theWords, wordOpHOL,
        wordOp])]
    rw [seqAssign TB _ _ (.word (n2' ^^^ -1)) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        TB, TA, T, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, g4, theWords,
        wordOpHOL, wordOp])]
    rw [seqAssign TC _ _ (.word 1) _ (by simp [WordSemStateFiniteExact.wordExp])]
    rw [seqInst T4 T5 _ _ (by
      simp [T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
        sptLookup_sptInsert_same, g10, a1]) rfl rfl]
    rw [seqInst T5 T6 _ _ (by
      simp [T6, T5, T4, TC, TB, TA, T, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
        sptLookup_sptInsert_same, g12, a1, a2]) rfl rfl]
    exact hrun

/-- `LongDiv1_thm'` with the stack bound phrased through `option_le`: when the
current frame is already accounted for, the stack maximum is unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "LongDiv1_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem longDiv1_thm {width : Nat} [NeZero width] {C F : Type} :
    ∀ (k : Nat) (n1 n2 m i1 i2 : BitVec width) (t2 : WordSemStateFiniteExact width C F)
      (r1 r2 : Nat) (m1 : BitVec width) (is1 : List (BitVec width)) (c : Config),
      singleDivLoop (BitVec.ofNat width k, [n1, n2], m, [i1, i2]) = (m1, is1) ∧
      sptLookup longDiv1Location t2.code = some (7, longDiv1Code c) ∧
      sptLookup 0 t2.locals = some (.loc r1 r2) ∧
      sptLookup 2 t2.locals = some (.word (BitVec.ofNat width k)) ∧
      sptLookup 4 t2.locals = some (.word n2) ∧
      sptLookup 6 t2.locals = some (.word n1) ∧
      sptLookup 8 t2.locals = some (.word m) ∧
      sptLookup 10 t2.locals = some (.word i1) ∧
      sptLookup 12 t2.locals = some (.word i2) ∧
      k < 2 ^ width ∧ k < t2.clock ∧ goodDimindex width ∧ ¬ c.hasLongdiv →
      ∃ (j1 j2 : BitVec width) (maxStack : Option Nat),
        is1 = [j1, j2] ∧
        WordSemStateFiniteExact.evaluate (longDiv1Code c) t2 =
          (some (.result (.loc r1 r2) [.word m1]),
            { t2 with clock := t2.clock - k, locals := .ln, localsSize := some 0,
                      stackMax := maxStack,
                      store := t2.store.updateEq (.temp 28, .word (holHd is1)) }) ∧
        (optionLe (Option.map₂ (· + ·) (wordSemStackSize t2.stack) t2.localsSize) t2.stackMax ∧
          t2.localsSize = sptLookup longDiv1Location t2.stackSize → maxStack = t2.stackMax) := by
  intro k n1 n2 m i1 i2 t2 r1 r2 m1 is1 c pre
  obtain ⟨j1, j2, mx, his, run, hmx⟩ := longDiv1_thm' k n1 n2 m i1 i2 t2 r1 r2 m1 is1 c pre
  refine ⟨j1, j2, mx, his, run, ?_⟩
  rintro ⟨le, size⟩
  rcases hmx with h | h
  · exact h
  · rw [h, ← size]
    have optMax (x y : Option Nat) : Option.map₂ max x y = wordSemOptionMax x y := by
      cases x <;> cases y <;> rfl
    rw [optMax, optionMap_maxComm]
    exact optionLe_maxDest _ _ le

/-- Without overflow, `single_div` agrees with its shift-and-subtract implementation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml"
  "single_div_pre_IMP_single_div_full" (words_as_type_indexed_bitvec)]
theorem singleDivPre_imp_singleDivFull {width : Nat} [NeZero width] {x1 x2 y : BitVec width} :
    singleDivPre x1 x2 y → singleDiv x1 x2 y = singleDivFull x1 x2 y := by
  rintro ⟨ne, lt⟩
  have hy : 0 < y.toNat := Nat.pos_of_ne_zero fun e => ne (BitVec.eq_of_toNat_eq (by simpa using e))
  refine (singleDivFull_thm ?_).symm
  have := (Nat.div_lt_iff_lt_mul hy).1 lt
  simp [mw2n]
  rw [Nat.mul_comm] at this
  linarith
/-- The generated long division computes `single_div`, with either the hardware
instruction or the software loop. HOL's unused universal `w : 'b` is kept. The
evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "evaluate_LongDiv_code'"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateLongDivCode' {width : Nat} [NeZero width] {C F β : Type} :
    ∀ (t : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (c : Config) (_w : β)
      (x1 x2 y d1 m1 : BitVec width),
      singleDivPre x1 x2 y ∧ singleDiv x1 x2 y = (d1, m1) ∧
      sptLookup longDiv1Location t.code = some (7, longDiv1Code c) ∧
      sptLookup 0 t.locals = some (.loc l1 l2) ∧
      sptLookup 2 t.locals = some (.word x1) ∧
      sptLookup 4 t.locals = some (.word x2) ∧
      sptLookup 6 t.locals = some (.word y) ∧
      2 ^ width < t.clock ∧ goodDimindex width →
      ∃ (ck : Nat) (maxStack : Option Nat),
        WordSemStateFiniteExact.evaluate (longDivCode c) t =
          (some (.result (.loc l1 l2) [.word d1]),
            { t with clock := ck, locals := .ln, localsSize := some 0,
                     store := t.store.updateEq (.temp 28, .word m1), stackMax := maxStack }) ∧
        (maxStack = t.stackMax ∨
          maxStack = Option.map₂ max t.stackMax
            (Option.map₂ (· + ·) (wordSemStackSize t.stack)
              (sptLookup longDiv1Location t.stackSize))) := by
  intro t l1 l2 c _ x1 x2 y d1 m1 ⟨pre, sd, hcode, h0, h2, h4, h6, hclock, good⟩
  by_cases hld : c.hasLongdiv
  · refine ⟨t.clock, t.stackMax, ?_, Or.inl rfl⟩
    obtain ⟨ne, lt⟩ := pre
    have hy0 : y.toNat ≠ 0 := fun e => ne (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [singleDiv, Prod.mk.injEq] at sd
    obtain ⟨rfl, rfl⟩ := sd
    simp [longDivCode, hld, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
      WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
      sptLookup_sptInsert_ne, sptLookup_sptInsert_same, h0, h2, h4, h6, hy0, lt]
  · have hsd := singleDivPre_imp_singleDivFull pre
    rw [sd] at hsd
    rcases hl : singleDivLoop (BitVec.ofNat width width, [0, y], 0, [x2, x1]) with ⟨q, is⟩
    simp only [singleDivFull, hl, Prod.mk.injEq] at hsd
    obtain ⟨rfl, rfl⟩ := hsd
    have wlt : width < 2 ^ width := Nat.lt_two_pow_self
    let t' := (t.setVar 10 (.word 0)).setVar 11 (.word (BitVec.ofNat width width))
    let vals : List (WordLocW width) := [.loc l1 l2, .word (BitVec.ofNat width width), .word y,
      .word 0, .word 0, .word x2, .word x1]
    let next := WordSemStateFiniteExact.callEnv vals (sptLookup longDiv1Location t.stackSize)
      (WordSemStateFiniteExact.decClock t')
    obtain ⟨j1, j2, mx, _, hrun, hmx⟩ := longDiv1_thm' width 0 y 0 x2 x1 next l1 l2 d1 is c
      ⟨hl, by simpa [next, t', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          WordSemStateFiniteExact.setVar] using hcode,
        by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [next, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        wlt, by simp [next, t', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          WordSemStateFiniteExact.setVar]; omega,
        good, hld⟩
    have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
      cases x <;> cases y <;> rfl
    have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
      cases x <;> cases y <;> rfl
    have idem (x y : Option Nat) :
        Option.map₂ max (Option.map₂ max x y) y = Option.map₂ max x y := by
      cases x <;> cases y <;> simp [Option.map₂]
    refine ⟨next.clock - width, mx, ?_, Or.inr ?_⟩
    · simp only [longDivCode, hld, if_false, Bool.false_eq_true]
      rw [seqAssign t 10 _ (.word 0) _ (by simp [WordSemStateFiniteExact.wordExp]),
        seqAssign (t.setVar 10 (.word 0)) 11 _ (.word (BitVec.ofNat width width)) _
          (by simp [WordSemStateFiniteExact.wordExp]),
        evalRecur t' c [0, 11, 6, 10, 10, 4, 2] vals
          (by simpa [t', WordSemStateFiniteExact.setVar] using hcode)
          (by simp [t', WordSemStateFiniteExact.setVar]; omega)
          (by simp [t', vals, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
            h0, h2, h4, h6])
          rfl l1 l2 _ _ hrun]
      simp [next, t', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
        WordSemStateFiniteExact.setVar, holHd]
    · rcases hmx with h | h <;>
        simp only [h, next, t', WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          WordSemStateFiniteExact.setVar, optMax, optAdd, idem]
/-- `evaluate_LongDiv_code'` with the stack bound phrased through `option_le`.
HOL's unused universal `w : 'b` is kept. The evaluator inherits the real-model
assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "evaluate_LongDiv_code"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateLongDivCode {width : Nat} [NeZero width] {C F β : Type} :
    ∀ (t : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (c : Config) (_w : β)
      (x1 x2 y d1 m1 : BitVec width),
      singleDivPre x1 x2 y ∧ singleDiv x1 x2 y = (d1, m1) ∧
      sptLookup longDiv1Location t.code = some (7, longDiv1Code c) ∧
      sptLookup 0 t.locals = some (.loc l1 l2) ∧
      sptLookup 2 t.locals = some (.word x1) ∧
      sptLookup 4 t.locals = some (.word x2) ∧
      sptLookup 6 t.locals = some (.word y) ∧
      2 ^ width < t.clock ∧ goodDimindex width →
      ∃ (ck : Nat) (maxStack : Option Nat),
        WordSemStateFiniteExact.evaluate (longDivCode c) t =
          (some (.result (.loc l1 l2) [.word d1]),
            { t with clock := ck, locals := .ln, localsSize := some 0,
                     store := t.store.updateEq (.temp 28, .word m1), stackMax := maxStack }) ∧
        (optionLe (Option.map₂ (· + ·) (wordSemStackSize t.stack) t.localsSize) t.stackMax ∧
          t.localsSize = sptLookup longDiv1Location t.stackSize → maxStack = t.stackMax) := by
  intro t l1 l2 c w x1 x2 y d1 m1 pre
  obtain ⟨ck, mx, run, hmx⟩ := evaluateLongDivCode' t l1 l2 c w x1 x2 y d1 m1 pre
  refine ⟨ck, mx, run, ?_⟩
  rintro ⟨le, size⟩
  rcases hmx with h | h
  · exact h
  · rw [h, ← size]
    have optMax (x y : Option Nat) : Option.map₂ max x y = wordSemOptionMax x y := by
      cases x <;> cases y <;> rfl
    rw [optMax, optionMap_maxComm]
    exact optionLe_maxDest _ _ le
end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
