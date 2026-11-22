module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Operand
public import Flapjack.Compiler.Backend.WordBignum.Proofs.EvaluateMcIop

@[expose] public section

/-! `AnyArith_thm`: establishing the bignum-code state relation before the call
(Flapjack-only helpers following the HOL proof's `impl_tac` for `evaluate_mc_iop`). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The mini-language state that `AnyArith_code` hands to the bignum code. -/
def iopMini {width : Nat} [NeZero width] (i j : Int) (iop : Misc.Multiword.MwOp)
    (zs : List (BitVec width)) (l : Nat) : WordBignum.MiniState width :=
  { regs := ((HolFiniteMapExact.empty.updateEq
        (0, Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width)))).updateEq
        (1, Misc.Multiword.mcHeader (Misc.Multiword.i2mw j : Bool × List (BitVec width)))).updateEq
        (3, (Misc.Multiword.intOpRep iop : BitVec width))
    arrays := Function.update
        (Function.update (fun _ => zs) .in2 (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2)
        .in1 (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2
    clock := l }

/-- The bignum-code state relation from its concrete ingredients. -/
theorem mini_stateRel {width : Nat} [NeZero width] {C F : Type}
    {t3 : WordSemStateFiniteExact width C F} {i j : Int} {iop : Misc.Multiword.MwOp}
    {zs : List (BitVec width)} {A1 A2 O : BitVec width}
    {cs : Nat × List (WordBignum.Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width))}
    {R1 R2 frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    (st0 : t3.store.lookup (.temp 0) =
      some (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width)))))
    (st1 : t3.store.lookup (.temp 1) =
      some (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw j : Bool × List (BitVec width)))))
    (st3 : t3.store.lookup (.temp 3) = some (.word (Misc.Multiword.intOpRep iop)))
    (sIn1 : t3.store.lookup WordBignum.tempIn1 = some (.word A1))
    (sIn2 : t3.store.lookup WordBignum.tempIn2 = some (.word A2))
    (sOut : t3.store.lookup WordBignum.tempOut = some (.word O))
    (arr1 : SetSep.star (SetSep.star
        (Misc.wordList A1 ((Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.map .word))
        (Misc.wordList O (zs.map .word))) R1
      (SetSep.fun2Set (t3.memory, fun a => t3.mdomain a = true)))
    (arr2 : SetSep.star (SetSep.star
        (Misc.wordList A2 ((Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.map .word))
        (Misc.wordList O (zs.map .word))) R2
      (SetSep.fun2Set (t3.memory, fun a => t3.mdomain a = true)))
    (arr3 : SetSep.star (Misc.wordList O (zs.map .word)) frame
      (SetSep.fun2Set (t3.memory, fun a => t3.mdomain a = true)))
    (code : WordBignum.codeRel cs t3.code)
    (div : WordBignum.divCodeAssum (C := C) (F := F) t3.code) (td : t3.termdep ≠ 0) :
    WordBignum.stateRel (iopMini i j iop zs t3.clock) t3 cs t3 frame := by
  refine ⟨rfl, ⟨A1, A2, O, R1, R2, sIn1, sIn2, sOut, ?_, ?_, ?_⟩, ?_, code, div, td,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  · simpa [iopMini] using arr1
  · simpa [iopMini] using arr2
  · simpa [iopMini] using arr3
  · intro a v h
    simp only [iopMini, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at h
    by_cases h3 : a = 3
    · subst h3; simp at h; subst h; exact ⟨by decide, st3⟩
    by_cases h1 : a = 1
    · subst h1; simp at h; subst h; exact ⟨by decide, st1⟩
    by_cases h0 : a = 0
    · subst h0; simp at h; subst h; exact ⟨by decide, st0⟩
    simp [h0, h1, h3, HolFiniteMapExact.empty] at h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
