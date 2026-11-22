module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.IopPre
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Multiword

@[expose] public section

/-! `AnyArith_thm`: running the generated bignum code through `evaluate_mc_iop`
(Flapjack-only helper following the HOL proof). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.WordSemStateFiniteExact.BignumClauses
open Flapjack.Misc.Multiword

/-- The mini-language state reported by `evaluate_mc_iop` after the call. -/
noncomputable def iopFinal {width : Nat} [NeZero width] (i j : Int) (iop : MwOp) (zs zs1 : List (BitVec width))
    (l l2 : Nat) : WordBignum.MiniState width :=
  WordBignum.deleteVars [21, 17, 15, 14, 16, 19, 18, 20, 6, 13, 4, 11, 8, 12, 9, 7, 2, 3, 1, 0]
    (WordBignum.clockWrite l2
      (WordBignum.regWrite 10 (some (mcHeader (i2mw (mwIntOp iop i j) : Bool × List (BitVec width))))
        (WordBignum.arrayWrite .in1 (i2mw i : Bool × List (BitVec width)).2
          (WordBignum.arrayWrite .in2 (i2mw j : Bool × List (BitVec width)).2
            (WordBignum.arrayWrite .out ((i2mw (mwIntOp iop i j) : Bool × List (BitVec width)).2 ++ zs1)
              (iopMini i j iop zs l))))))

/-- The bignum call of `AnyArith_code`, via `evaluate_mc_iop`. -/
theorem iop_call_step {width : Nat} [NeZero width] {C F : Type}
    {t9 : WordSemStateFiniteExact width C F} {l1 l2 : Nat} {i j : Int} {iop : MwOp} {n : Nat}
    {A1 A2 O : BitVec width} {R1 R2 frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    {xx1 : WordLangProgHOL (BitVec width)} {xx2 xx3 xx4 : Nat}
    {xx5 : List (WordBignum.Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width))}
    (hloc : t9.locals = sptInsert 0 (.loc l1 l2) .ln)
    (hcomp : WordBignum.compile bignumLocation 2 1 (bignumLocation + 1, [])
      (WordBignum.mcIopCode width) = (xx1, xx2, xx3, xx4, xx5))
    (hcode : sptLookup bignumLocation t9.code = some (1, .seq xx1 (.return 0 [0])))
    (crel : WordBignum.codeRel (xx4, xx5) t9.code)
    (dca : WordBignum.divCodeAssum (C := C) (F := F) t9.code) (td : t9.termdep ≠ 0)
    (st0 : t9.store.lookup (.temp 0) =
      some (.word (mcHeader (i2mw i : Bool × List (BitVec width)))))
    (st1 : t9.store.lookup (.temp 1) =
      some (.word (mcHeader (i2mw j : Bool × List (BitVec width)))))
    (st3 : t9.store.lookup (.temp 3) = some (.word (intOpRep iop)))
    (sIn1 : t9.store.lookup WordBignum.tempIn1 = some (.word A1))
    (sIn2 : t9.store.lookup WordBignum.tempIn2 = some (.word A2))
    (sOut : t9.store.lookup WordBignum.tempOut = some (.word O))
    (arr1 : SetSep.star (SetSep.star
        (Misc.wordList A1 ((i2mw i : Bool × List (BitVec width)).2.map .word))
        (Misc.wordList O (List.replicate n (.word 0)))) R1
      (SetSep.fun2Set (t9.memory, fun a => t9.mdomain a = true)))
    (arr2 : SetSep.star (SetSep.star
        (Misc.wordList A2 ((i2mw j : Bool × List (BitVec width)).2.map .word))
        (Misc.wordList O (List.replicate n (.word 0)))) R2
      (SetSep.fun2Set (t9.memory, fun a => t9.mdomain a = true)))
    (arr3 : SetSep.star (Misc.wordList O (List.replicate n (.word 0))) frame
      (SetSep.fun2Set (t9.memory, fun a => t9.mdomain a = true)))
    (hdiv : iop = .div ∨ iop = .mod → j ≠ 0)
    (hmax : mcDivMax (i2mw i : Bool × List (BitVec width)).2 (i2mw j : Bool × List (BitVec width)).2
      (List.replicate n 0) + 2 * n + 2 ≤ t9.clock - 1)
    (hlen : (i2mw i : Bool × List (BitVec width)).2.length +
      (i2mw j : Bool × List (BitVec width)).2.length < n)
    (hzs : n < 2 ^ width / 2) (hlt : iop ≠ .lt) (heq : iop ≠ .eq) (hdec : iop ≠ .dec)
    (good : goodDimindex width) (rest : WordLangProgHOL (BitVec width)) :
    ∃ (t2 : WordSemStateFiniteExact width C F) (zs1 : List (BitVec width)) (l2' : Nat),
      WordSemStateFiniteExact.evaluate
          (.seq (.call (some ([1], (.ls (), .ln), .skip, anyArithLocation, 3)) (some bignumLocation)
            [] none) rest) t9 =
        WordSemStateFiniteExact.evaluate rest
          (afterCallState t9 (WordSemStateFiniteExact.flushState false t2) (.loc l1 l2)) ∧
      ((i2mw (mwIntOp iop i j) : Bool × List (BitVec width)).2 ++ zs1).length = n ∧
      t2.stack = (bignumCallState t9 (.loc l1 l2)).stack ∧
      WordBignum.stateRel (iopFinal i j iop (List.replicate n 0) zs1 (t9.clock - 1) l2') t2
        (xx4, xx5) (bignumCallState t9 (.loc l1 l2)) frame ∧
      t2.code = t9.code ∧
      WordSemStateFiniteExact.evaluate (.seq xx1 (.return 0 [0])) (bignumCallState t9 (.loc l1 l2)) =
        (some (.result (.loc anyArithLocation 3) [.loc anyArithLocation 3]),
          WordSemStateFiniteExact.flushState false t2) := by
  set t3 := bignumCallState t9 (.loc l1 l2) with ht3
  have c3 : t3.clock = t9.clock - 1 := rfl
  have hc0 : t9.clock ≠ 0 := by omega
  have hw : 3 < width := by rcases good with h | h <;> omega
  have rel3 : WordBignum.stateRel (iopMini i j iop (List.replicate n 0) t3.clock) t3 (xx4, xx5) t3
      frame := by
    have rz : (List.replicate n (0 : BitVec width)).map WordLocW.word = List.replicate n (.word 0) := by
      simp [List.map_replicate]
    exact mini_stateRel (t3 := t3) st0 st1 st3 sIn1 sIn2 sOut (by rw [rz]; exact arr1)
      (by rw [rz]; exact arr2) (by rw [rz]; exact arr3) crel dca td
  have g0 : WordSemStateFiniteExact.getVar 0 t3 = some (.loc anyArithLocation 3) := by
    simp [t3, bignumCallState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.callEnv,
      sptFromList2, sptLookup]
  have bound := mcHeader_i2mw_eq_0w (width := width) (i := i)
  have boundj := mcHeader_i2mw_eq_0w (width := width) (i := j)
  have hh1 : mcHeader (i2mw i : Bool × List (BitVec width)) = 0 ↔
      (i2mw i : Bool × List (BitVec width)).2 = [] := by
    rw [bound (by omega), snd_i2mw_nil]
  have hh2 : mcHeader (i2mw j : Bool × List (BitVec width)) = 0 ↔
      (i2mw j : Bool × List (BitVec width)).2 = [] := by
    rw [boundj (by omega), snd_i2mw_nil]
  obtain ⟨zs1, l2', t2, _, hlen2, _, hrun, _, hstack, hg0, hrel2, hcode2⟩ :=
    WordBignum.evaluate_mc_iop i j 2 frame (List.replicate n 0) t3 (.loc anyArithLocation 3)
      bignumLocation t3.clock iop xx1 xx2 xx3 (xx4, xx5) rel3 hdiv hcomp g0 hh2 hh1
      (by simpa [c3] using hmax) (by simpa using hlen) hw (by simpa using hzs) hlt heq hdec good
  have hret : WordSemStateFiniteExact.evaluate (.seq xx1 (.return 0 [0])) t3 =
      (some (.result (.loc anyArithLocation 3) [.loc anyArithLocation 3]),
        WordSemStateFiniteExact.flushState false t2) := by
    rw [hrun, evaluate_return]
    simp [hg0, WordSemStateFiniteExact.getVars]
  refine ⟨t2, zs1, l2', ?_, by simpa using hlen2, hstack, hrel2, hcode2, hret⟩
  exact call_bignum hloc hcode hc0 hret (by simpa [WordSemStateFiniteExact.flushState] using hstack)
    rest

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
