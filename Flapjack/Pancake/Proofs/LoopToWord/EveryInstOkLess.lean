import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.Semantics.LoopProps.EveryProg
import Flapjack.Pancake.Semantics.LoopProps.AccVars
import Flapjack.Pancake.Proofs.LoopToWord.FindVar
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.Proofs.LoopToWord.ContextSupport
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelIntro
import Flapjack.Misc.Sptree.ToAList
-- Shares the generated `compHOL` match-congruence auxiliaries (avoids a duplicate declaration).
import Flapjack.Pancake.LoopToWord.Proofs.NoFP

/-!
# `loop_to_wordProof`: instruction well-formedness (`every_inst_ok_less`)

Counterparts of `cakeml/pancake/proofs/loop_to_wordProofScript.sml` 2285-2390:
`loop_inst_ok_def` and the preservation of `wordConvs$inst_ok_less` through
`comp`, `comp_func`, `compile_prog` and `compile`. HOL `every_inst (inst_ok_less c) p`
is `everyInst (fun i => instOkLessExact c (HolInst.ofWordLangInst i)) p = true`, as in
the reviewed `compile_to_word_conventions2`; `addr_offset_ok c 0w` and
`byte_offset_ok c 0w` are the reviewed `asm*OffsetOkExact` overload renderings;
`domain s ⊆ domain t` is pointwise `sptDomain` inclusion; `INJ (find_var ctxt)
(domain ctxt) 𝕌(:num)` is injectivity of `findVarHOL ctxt` on `sptDomain ctxt`
(as in the reviewed `locals_rel_def`); `EVEN m` is `m % 2 = 0`; `EVERY (λ(…). P) l`
is membership quantification.
-/

namespace Flapjack.LoopToWord

open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `loop_inst_ok_def` (`loop_to_wordProofScript.sml:2285-2292`):
`LDiv` needs ARMv8/MIPS/RISC-V, `LLongMul` the ARMv7 and ARMv8/RISC-V/Ag32 register
side conditions, `LLongDiv` x86-64, and every other program is accepted. HOL's set
membership `c.ISA ∈ {ARMv8; MIPS; RISC_V}` is the three-way disjunction. As in HOL
(`c : 'a asm_config`, program `: 'b prog`), the configuration and program word
dimensions are independent. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def loopInstOk {width : Nat} [NeZero width] {progWidth : Nat} [NeZero progWidth]
    (c : AsmConfigExact width) : HolLoopProg progWidth → Prop
  | .arith (.div _ _ _) => c.isa = .armv8 ∨ c.isa = .mips ∨ c.isa = .riscv
  | .arith (.longMul r1 r2 r3 r4) =>
      (c.isa = .armv7 → r1 ≠ r2) ∧
      (c.isa = .armv8 ∨ c.isa = .riscv ∨ c.isa = .ag32 → r1 ≠ r3 ∧ r1 ≠ r4)
  | .arith (.longDiv _ _ _ _ _) => c.isa = .x86_64
  | _ => True

/-- An assigned context variable and any other variable have distinct registers
(Flapjack infrastructure for the HOL `INJ_DEF`/`lookup_NONE_domain` case split). -/
theorem findVarHOL_ne_of_mem {ctxt : Spt Nat} {a b : Nat}
    (hinj : ∀ x y, sptDomain ctxt x → sptDomain ctxt y →
      findVarHOL ctxt x = findVarHOL ctxt y → x = y)
    (heven : ∀ n m, sptLookup n ctxt = some m → m ≠ 0 ∧ m % 2 = 0)
    (ha : sptDomain ctxt a) (hab : a ≠ b) : findVarHOL ctxt a ≠ findVarHOL ctxt b := by
  intro heq
  by_cases hb : sptDomain ctxt b
  · exact hab (hinj a b ha hb heq)
  · obtain ⟨m, hm⟩ := (sptMem_iff_lookup a ctxt).mp ha
    have hbn : sptLookup b ctxt = none := by
      cases h : sptLookup b ctxt with
      | none => rfl
      | some r => exact absurd ((sptMem_iff_lookup b ctxt).mpr ⟨r, h⟩) hb
    simp only [findVarHOL, hm, hbn, Option.getD_some, Option.getD_none] at heq
    exact (heven a m hm).1 heq

/-- Accumulated `acc_vars` contain the fresh-accumulator variables
(Flapjack infrastructure, from `acc_vars_acc`). -/
theorem accVarsHOL_dom_left {width : Nat} [NeZero width] (p : HolLoopProg width)
    (l : NumSet) (k : Nat) (h : sptDomain (accVarsHOL p .ln) k) :
    sptDomain (accVarsHOL p l) k := by
  rw [congrFun (accVarsAccHOL p l) k]; exact Or.inl h

/-- Accumulated `acc_vars` contain the accumulator (Flapjack infrastructure). -/
theorem accVarsHOL_dom_right {width : Nat} [NeZero width] (p : HolLoopProg width)
    (l : NumSet) (k : Nat) (h : sptDomain l k) : sptDomain (accVarsHOL p l) k := by
  rw [congrFun (accVarsAccHOL p l) k]; exact Or.inr h

/-- Full original loop_to_word_comp_every_inst_ok_less
(`loop_to_wordProofScript.sml:2294-2335`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordCompEveryInstOkLess {width : Nat} [NeZero width]
    (c : AsmConfigExact width) :
    ∀ (ctxt : Spt Nat) (prog : HolLoopProg width) (l : Nat × Nat),
      asmByteOffsetOkExact c 0 = true ∧ asmAddrOffsetOkExact c 0 = true ∧
      everyProgHOL (loopInstOk c) prog ∧
      (∀ k, sptDomain (accVarsHOL prog .ln) k → sptDomain ctxt k) ∧
      (∀ x y, sptDomain ctxt x → sptDomain ctxt y →
        findVarHOL ctxt x = findVarHOL ctxt y → x = y) ∧
      (∀ n m, sptLookup n ctxt = some m → m ≠ 0 ∧ m % 2 = 0) →
      everyInst (fun i => instOkLessExact c (HolInst.ofWordLangInst i))
        (compHOL ctxt prog l).1 = true := by
  intro ctxt prog l
  fun_induction compHOL ctxt prog l
  all_goals
    rintro ⟨hb, ha, hev, hdom, hinj, heven⟩
    try simp only [everyInst, Bool.and_eq_true]
  case case3 right _ =>
    have h2 := findVarHOL_ne_odd ctxt right 3 ⟨heven, by decide⟩
    simp only [HolInst.ofWordLangInst, HolArith.ofWordLangArith, instOkLessExact]
    simp [Ne.symm h2]
  case case5 r1 r2 r3 r4 _ =>
    simp only [everyProgHOL, loopInstOk] at hev
    have hd1 : sptDomain ctxt r1 := hdom r1 (by
      simp [accVarsHOL, sptDomain_sptInsert])
    simp only [HolInst.ofWordLangInst, HolArith.ofWordLangArith, instOkLessExact,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    have ne := fun b hb => findVarHOL_ne_of_mem (b := b) hinj heven hd1 hb
    refine ⟨?_, ?_⟩
    · by_cases h7 : c.isa = .armv7
      · exact Or.inr (ne r2 (hev.1 h7))
      · exact Or.inl h7
    · by_cases h8 : c.isa = .armv8 ∨ c.isa = .riscv ∨ c.isa = .ag32
      · exact Or.inr ⟨ne r3 (hev.2 h8).1, ne r4 (hev.2 h8).2⟩
      · left
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact ⟨⟨fun h => h8 (Or.inl h), fun h => h8 (Or.inr (Or.inl h))⟩,
          fun h => h8 (Or.inr (Or.inr h))⟩
  case case6 =>
    simp only [everyProgHOL, loopInstOk] at hev
    simp [HolInst.ofWordLangInst, HolArith.ofWordLangArith, instOkLessExact, hev]
  case case7 =>
    simp only [everyProgHOL, loopInstOk] at hev
    simp only [HolInst.ofWordLangInst, HolArith.ofWordLangArith, instOkLessExact]
    rcases hev with h | h | h <;> simp [h]
  case case10 =>
    simp [HolInst.ofWordLangInst, HolAddr.ofWordLangAddr, instOkLessExact]; exact ha
  case case11 =>
    simp [HolInst.ofWordLangInst, HolAddr.ofWordLangAddr, instOkLessExact]; exact hb
  case case12 =>
    simp [HolInst.ofWordLangInst, HolAddr.ofWordLangAddr, instOkLessExact]; exact ha
  case case13 =>
    simp [HolInst.ofWordLangInst, HolAddr.ofWordLangAddr, instOkLessExact]; exact hb
  case case14 f sc _ w1 _ hc1 w2 _ hc2 ih2 ih1 =>
    simp only [everyProgHOL] at hev
    simp only [accVarsHOL] at hdom
    have e1 := ih2 ⟨hb, ha, hev.2.1,
      fun k hk => hdom k (accVarsHOL_dom_left f _ k hk), hinj, heven⟩
    have e2 := ih1 ⟨hb, ha, hev.2.2,
      fun k hk => hdom k (accVarsHOL_dom_right f _ k (accVarsHOL_dom_left sc _ k hk)), hinj, heven⟩
    rw [hc1] at e1; rw [hc2] at e2
    exact ⟨e1, e2⟩
  case case15 f sc _ _ w1 _ hc1 w2 _ hc2 ih2 ih1 =>
    simp only [everyProgHOL] at hev
    simp only [accVarsHOL] at hdom
    have e1 := ih2 ⟨hb, ha, hev.2.1,
      fun k hk => hdom k (accVarsHOL_dom_left f _ k hk), hinj, heven⟩
    have e2 := ih1 ⟨hb, ha, hev.2.2,
      fun k hk => hdom k (accVarsHOL_dom_right f _ k (accVarsHOL_dom_left sc _ k hk)), hinj, heven⟩
    rw [hc1] at e1; rw [hc2] at e2
    exact ⟨⟨e1, e2⟩, trivial⟩
  case case16 body _ w _ hc ih =>
    simp only [everyProgHOL] at hev
    simp only [accVarsHOL] at hdom
    have e := ih ⟨hb, ha, hev.2, hdom, hinj, heven⟩
    rw [hc] at e
    exact ⟨trivial, e, trivial⟩
  case case22 body _ ih =>
    simp only [everyProgHOL] at hev
    simp only [accVarsHOL] at hdom
    exact ih ⟨hb, ha, hev.2, hdom, hinj, heven⟩
  case case26 => exact ⟨trivial, trivial⟩
  case case27 p1 p2 _ w1 _ hc1 w2 _ hc2 ih2 ih1 =>
    simp only [everyProgHOL] at hev
    simp only [accVarsHOL] at hdom
    have e1 := ih2 ⟨hb, ha, hev.2.1,
      fun k hk => hdom k (accVarsHOL_dom_left p1 _ k hk), hinj, heven⟩
    have e2 := ih1 ⟨hb, ha, hev.2.2,
      fun k hk => hdom k (accVarsHOL_dom_right p1 _ k (accVarsHOL_dom_left p2 _ k hk)), hinj, heven⟩
    refine ⟨⟨?_, e1⟩, trivial⟩
    have hs : (compHOL ctxt p1 (_, _ + 1)).2 = _ := congrArg Prod.snd hc1
    rw [hs]
    exact e2

/-- Full original loop_to_word_comp_func_every_inst_ok_less
(`loop_to_wordProofScript.sml:2337-2353`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordCompFuncEveryInstOkLess {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (n : Nat) (params : List Nat) (body : HolLoopProg width)
    (p : WordLangProgHOL (BitVec width)) :
    loopToWordCompFuncHOL n params body = p ∧ everyProgHOL (loopInstOk c) body ∧
      asmAddrOffsetOkExact c 0 = true ∧ asmByteOffsetOkExact c 0 = true →
    everyInst (fun i => instOkLessExact c (HolInst.ofWordLangInst i)) p = true := by
  rintro ⟨rfl, hev, ha, hb⟩
  unfold loopToWordCompFuncHOL
  have hrel := localsRelHOLMkCtxtLn (width := width) 2
    (params ++ fromNumSetHOL (sptDifference (accVarsHOL body (.ln : Spt Unit))
      (toNumSetHOL params))) .ln ⟨by decide, by decide⟩
  obtain ⟨hinj, heven, -⟩ := localsRelHOLIntro _ _ _ hrel
  refine loopToWordCompEveryInstOkLess c _ body _ ⟨hb, ha, hev, ?_, hinj, heven⟩
  intro k hk
  rw [sptDomain_makeCtxtHOL]
  right
  by_cases hp : k ∈ params
  · exact List.mem_append_left _ hp
  · refine List.mem_append_right _ ?_
    have hset := congrFun (fromNumSetHOL_set (sptDifference (accVarsHOL body (.ln : Spt Unit))
      (toNumSetHOL params))) k
    rw [hset, sptDomainDifference, sptDomain_toNumSetHOL]
    exact ⟨hk, hp⟩

/-- Full original loop_to_word_compile_prog_every_inst_ok_less
(`loop_to_wordProofScript.sml:2355-2370`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordCompileProgEveryInstOkLess {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (lprog : List (Nat × List Nat × HolLoopProg width))
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    loopToWordCompileProgHOL lprog = wprog0 ∧
      asmByteOffsetOkExact c 0 = true ∧ asmAddrOffsetOkExact c 0 = true ∧
      (∀ f ∈ lprog, everyProgHOL (loopInstOk c) f.2.2) →
    ∀ f ∈ wprog0, everyInst (fun i => instOkLessExact c (HolInst.ofWordLangInst i)) f.2.2 = true := by
  rintro ⟨rfl, hb, ha, hall⟩ f hf
  simp only [loopToWordCompileProgHOL, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact loopToWordCompFuncEveryInstOkLess c g.1 g.2.1 g.2.2 _ ⟨rfl, hall g hg, ha, hb⟩

/-- Full original loop_to_word_every_inst_ok_less
(`loop_to_wordProofScript.sml:2372-2380`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordEveryInstOkLess {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (lprog : List (Nat × List Nat × HolLoopProg width))
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    loopToWordCompileHOL lprog = wprog0 ∧
      asmByteOffsetOkExact c 0 = true ∧ asmAddrOffsetOkExact c 0 = true ∧
      (∀ f ∈ lprog, everyProgHOL (loopInstOk c) f.2.2) →
    ∀ f ∈ wprog0, everyInst (fun i => instOkLessExact c (HolInst.ofWordLangInst i)) f.2.2 = true :=
  loopToWordCompileProgEveryInstOkLess c lprog wprog0

end Flapjack.LoopToWord
