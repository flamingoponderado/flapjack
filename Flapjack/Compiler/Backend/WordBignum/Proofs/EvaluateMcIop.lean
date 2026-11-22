module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.Corr.Iop
public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileThm
public import Flapjack.Misc.Multiword.Mc.Correct.Iop

@[expose] public section

/-! HOL `evaluate_mc_iop` of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`: the compiled
`mc_iop_code`, run from a `wordSem` state related to the mini-language state
holding the two operand headers, the operation code and the operand arrays,
computes the multiword integer operation. HOL derives it by combining
`mc_iop_corr_thm`, `compile_thm` and `mc_multiword`'s `mc_iop_thm`. -/

set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Misc.Multiword

namespace EvaluateMcIopWitness

/-- Same-module canonical roundtrip witness for the mini-language state
carrier, required by the relation qualifier on `evaluate_mc_iop`. -/
theorem holFmapAsFiniteSupportRelationWitness_MiniState {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

/-- Same-module canonical roundtrip witness for the `wordSem` state carrier,
required by the relation qualifier on `evaluate_mc_iop`. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact {width : Nat}
    [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateMcIopWitness

/-- `mc_iop_code` is well formed (HOL evaluates `syntax_ok mc_iop_code` by
`EVAL`). Flapjack-only step of `evaluate_mc_iop`. -/
theorem syntaxOk_mcIopCode {width : Nat} [NeZero width] : syntaxOk (mcIopCode width) := by
  simp (config := { decide := true }) [syntaxOk, syntaxOkAux, expOk, mcIopCode, mcIsubFlipCode,
    mcIaddCode, mcImulCode, mcIdivCode, mcIadd1Code, mcIadd2Code, mcIadd3Code, mcAddCode,
    mcSubCode, mcAddLoopCode, mcAddLoop1Code, mcAddLoop2Code, mcSubLoopCode, mcSubLoop1Code,
    mcSubLoop2Code, mcFixCode, mcImul1Code, mcMulCode, mcMulPassCode, mcMulZeroCode,
    mcIdiv0Code, mcIdivModHeaderCode, mcAdd1CallCode, mcAdd1Code, mcDivSubCallCode,
    mcDivSub1Code, mcDivSubAuxCode, mcDivSubAux1Code, mcDivCode, mcDiv0Code, mcDiv1Code,
    mcDiv2Code, mcDiv3Code, mcCopyOverCode, mcCopyDownCode, mcSimpleDivCode,
    mcSimpleDiv1Code, mcSingleDivCode, mcCalcDCode, mcMulBySingleCode, mcMulBySingle2Code,
    mcSingleMulCode, mcSingleMulAddCode, mcDivLoopCode, mcDivAdjustCode, mcAdjustAuxCode,
    mcAdjCmpCode, mcDivR1Code, mcDivGuessCode, mcDivTestCode, mcCmp2Code,
    mcCmp3Code, mcCmpMul2Code, mcTopTwoCode, mcDivSubCode, mcDivSubLoopCode, mcSub1Code,
    mcCmpCode, mcCompareCode]

/-- HOL `evaluate_mc_iop` (`word_bignumProofScript.sml:2289`, derived from
`mc_iop_corr_thm`, `compile_thm` and `mc_iop_thm`). The quantified variables
are HOL's, in the captured order (`evaluate_mc_iop_typed`); the mini-language
state literal `<|regs := FEMPTY |+ (0,..) |+ (1,..) |+ (3,..); arrays := (In1 =+
..) ((In2 =+ ..) (K zs)); clock := l|>` is written with the reviewed
finite-map `updateEq` rendering of `|+` and `Function.update` for `=+`, and
`dimword (:α) DIV 2` is `2 ^ width / 2`. The premises are HOL's curried chain
in order. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_mc_iop"
  (fmap_as_finite_support_relation :=
    [MiniState.regs, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluate_mc_iop {width : Nat} [NeZero width] {C F : Type} :
    ∀ (i1 i2 : Int) (l' : Nat) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
      (zs : List (BitVec width)) (t : WordSemStateFiniteExact width C F)
      (retVal : WordLocW width) (n l : Nat) (iop : MwOp) (p1 : WordLangProgHOL (BitVec width))
      (l1 i' : Nat)
      (cs : Nat × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width))),
      stateRel
          ({ regs := ((HolFiniteMapExact.empty.updateEq
                  (0, mcHeader (i2mw i1 : Bool × List (BitVec width)))).updateEq
                  (1, mcHeader (i2mw i2 : Bool × List (BitVec width)))).updateEq
                  (3, (intOpRep iop : BitVec width))
             arrays := Function.update
                 (Function.update (fun _ => zs) .in2 (i2mw i2 : Bool × List (BitVec width)).2)
                 .in1 (i2mw i1 : Bool × List (BitVec width)).2
             clock := l } : MiniState width) t cs t frame →
        (iop = .div ∨ iop = .mod → i2 ≠ 0) →
        compile n l' 1 (n + 1, []) (mcIopCode width) = (p1, l1, i', cs) →
        WordSemStateFiniteExact.getVar 0 t = some retVal →
        (mcHeader (i2mw i2 : Bool × List (BitVec width)) = 0 ↔
          (i2mw i2 : Bool × List (BitVec width)).2 = []) →
        (mcHeader (i2mw i1 : Bool × List (BitVec width)) = 0 ↔
          (i2mw i1 : Bool × List (BitVec width)).2 = []) →
        mcDivMax (i2mw i1 : Bool × List (BitVec width)).2
            (i2mw i2 : Bool × List (BitVec width)).2 zs + 2 * zs.length + 2 ≤ l →
        (i2mw i1 : Bool × List (BitVec width)).2.length +
            (i2mw i2 : Bool × List (BitVec width)).2.length < zs.length →
        3 < width →
        zs.length < 2 ^ width / 2 →
        iop ≠ .lt → iop ≠ .eq → iop ≠ .dec →
        goodDimindex width →
        ∃ (zs1 : List (BitVec width)) (l2 : Nat) (t2 : WordSemStateFiniteExact width C F),
          mcIop (l, mcHeader (i2mw i1 : Bool × List (BitVec width)),
              mcHeader (i2mw i2 : Bool × List (BitVec width)), (intOpRep iop : BitVec width),
              (i2mw i1 : Bool × List (BitVec width)).2, (i2mw i2 : Bool × List (BitVec width)).2,
              zs) =
            (l2, mcHeader (i2mw (mwIntOp iop i1 i2) : Bool × List (BitVec width)),
              (i2mw i1 : Bool × List (BitVec width)).2, (i2mw i2 : Bool × List (BitVec width)).2,
              (i2mw (mwIntOp iop i1 i2) : Bool × List (BitVec width)).2 ++ zs1) ∧
          ((i2mw (mwIntOp iop i1 i2) : Bool × List (BitVec width)).2 ++ zs1).length =
            zs.length ∧
          l ≤ l2 + mcDivMax (i2mw i1 : Bool × List (BitVec width)).2
              (i2mw i2 : Bool × List (BitVec width)).2 zs + 2 * zs.length + 2 ∧
          WordSemStateFiniteExact.evaluate (.seq p1 (.return 0 [0])) t =
            WordSemStateFiniteExact.evaluate (.return 0 [0]) t2 ∧
          0 < i' ∧ t2.stack = t.stack ∧
          WordSemStateFiniteExact.getVar 0 t2 = some retVal ∧
          stateRel
              (deleteVars [21, 17, 15, 14, 16, 19, 18, 20, 6, 13, 4, 11, 8, 12, 9, 7, 2, 3, 1, 0]
                (clockWrite l2
                  (regWrite 10
                    (some (mcHeader (i2mw (mwIntOp iop i1 i2) : Bool × List (BitVec width))))
                    (arrayWrite .in1 (i2mw i1 : Bool × List (BitVec width)).2
                      (arrayWrite .in2 (i2mw i2 : Bool × List (BitVec width)).2
                        (arrayWrite .out
                          ((i2mw (mwIntOp iop i1 i2) : Bool × List (BitVec width)).2 ++ zs1)
                          ({ regs := ((HolFiniteMapExact.empty.updateEq
                                  (0, mcHeader (i2mw i1 : Bool × List (BitVec width)))).updateEq
                                  (1, mcHeader (i2mw i2 : Bool × List (BitVec width)))).updateEq
                                  (3, (intOpRep iop : BitVec width))
                             arrays := Function.update
                                 (Function.update (fun _ => zs) .in2
                                   (i2mw i2 : Bool × List (BitVec width)).2)
                                 .in1 (i2mw i1 : Bool × List (BitVec width)).2
                             clock := l } : MiniState width)))))))
              t2 cs t frame ∧
          t2.code = t.code := by
  intro i1 i2 l' frame zs t retVal n l iop p1 l1 i' cs hrel hdiv hcomp hvar hh2 hh1 hmax hlen
    hw hzs hlt heq hdec hgood
  obtain ⟨zs1, l2, hpre, hiop, hlen2, hbound⟩ :=
    mcIop_thm (s := (i2mw i1 : Bool × List (BitVec width)).1)
      (xs := (i2mw i1 : Bool × List (BitVec width)).2)
      (t := (i2mw i2 : Bool × List (BitVec width)).1)
      (ys := (i2mw i2 : Bool × List (BitVec width)).2) (zs := zs) (iop := iop) (l := l) hw
      ⟨by simpa only [Prod.mk.eta] using hh1, mw_ok_SND_i2mw i1,
        by simpa only [Prod.mk.eta] using hh2, mw_ok_SND_i2mw i2, hlen, hzs, hlt, heq, hdec,
        fun h => (i2mw_snd_ne_nil i2).2 (hdiv h), hmax⟩
  simp only [Prod.mk.eta, mwiOp_thm iop i1 i2 hdiv] at hpre hiop hlen2 hbound
  set S : MiniState width :=
    ({ regs := ((HolFiniteMapExact.empty.updateEq
            (0, mcHeader (i2mw i1 : Bool × List (BitVec width)))).updateEq
            (1, mcHeader (i2mw i2 : Bool × List (BitVec width)))).updateEq
            (3, (intOpRep iop : BitVec width))
       arrays := Function.update
           (Function.update (fun _ => zs) .in2 (i2mw i2 : Bool × List (BitVec width)).2)
           .in1 (i2mw i1 : Bool × List (BitVec width)).2
       clock := l } : MiniState width) with hS
  have hl0 : S.regs.lookup 0 = some (mcHeader (i2mw i1 : Bool × List (BitVec width))) := by
    simp [hS, HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have hl1 : S.regs.lookup 1 = some (mcHeader (i2mw i2 : Bool × List (BitVec width))) := by
    simp [hS, HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have hl3 : S.regs.lookup 3 = some (intOpRep iop : BitVec width) := by
    simp [hS, HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have hf0 := holFapply_of_lookup hl0
  have hf1 := holFapply_of_lookup hl1
  have hf3 := holFapply_of_lookup hl3
  have ha1 : S.arrays .in1 = (i2mw i1 : Bool × List (BitVec width)).2 := by simp [hS]
  have ha2 : S.arrays .in2 = (i2mw i2 : Bool × List (BitVec width)).2 := by
    simp [hS, Function.update]
  have hao : S.arrays .out = zs := by simp [hS, Function.update]
  have hcl : S.clock = l := rfl
  have hG : 0 ∈ S.regs.dom ∧ 1 ∈ S.regs.dom ∧ 3 ∈ S.regs.dom ∧
      mcIopPre (S.clock, holFapply S.regs 0, holFapply S.regs 1, holFapply S.regs 3,
        S.arrays .in1, S.arrays .in2, S.arrays .out) := by
    refine ⟨by simp [HolFiniteMapExact.dom, hl0], by simp [HolFiniteMapExact.dom, hl1],
      by simp [HolFiniteMapExact.dom, hl3], ?_⟩
    rw [hf0, hf1, hf3, ha1, ha2, hao, hcl]
    exact hpre
  have hev := mc_iop_corr_thm S hG
  obtain ⟨t2, res, hres, hrest⟩ :=
    compile_thm (β := Nat) t frame none S (mcIopCode width) _ hev n l' 1 (n + 1, []) p1 l1 i'
      cs cs t retVal (.return 0 [0])
      ⟨hcomp, hrel, Nat.one_pos, syntaxOk_mcIopCode, codeSubset_refl _,
        (fun b hb => nomatch hb), (fun b hb => by simp [mcIopCode] at hb), hvar, hgood⟩
  obtain ⟨hres2, hi, hstack, hvar2, hrel2, hcode⟩ := hrest
  rw [hf0, hf1, hf3, ha1, ha2, hao, hcl, hiop] at hrel2
  exact ⟨zs1, l2, t2, hiop, hlen2, hbound, hres ▸ hres2, hi, hstack, hvar2, hrel2, hcode⟩

end Flapjack.Compiler.Backend.WordBignum
