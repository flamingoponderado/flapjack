import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace InstAssignWitnesses

/-- Canonical imported carrier roundtrip for this instruction-case group. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end InstAssignWitnesses

/-- Flapjack proof infrastructure: an assignment-shaped instruction has the
same exact evaluator result as its expression assignment. The equations and
domain equality are discharged from the literal instruction clauses below;
they are not additional hypotheses of the tagged cases. -/
private theorem assignmentInstructionCase
    {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (r : Nat) (e : WordLangExpHOL (BitVec width))
    (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat)
    (live : NumSet) (lt : List (NumSet × NumSet))
    (hi : ∀ s : WordSemStateFiniteExact width C F, inst i s = assign r e s)
    (hc : ∀ s : WordSemStateFiniteExact width C F,
      inst (applyColourInst f i) s = assign (f r) (applyColourExp f e) s)
    (hl : ∀ k, sptDomain (getLive (.inst i) live lt) k ↔
      sptDomain (getLive (.assign r e) live lt) k)
    (hw : getWrites (.inst i) = getWrites (.assign r e))
    (h : colouringOk f (.inst i) live lt ∧ wordStateEqRel st cst ∧
      strongLocalsRel f (sptDomain (getLive (.inst i) live lt)) st.locals cst.locals) :
    applyColourPost f (.inst i) live lt st cst := by
  have hassign : colouringOk f (.assign r e) live lt ∧ wordStateEqRel st cst ∧
      strongLocalsRel f (sptDomain (getLive (.assign r e) live lt)) st.locals cst.locals := by
    refine ⟨?_, h.2.1, ?_⟩
    · have hok := h.1
      simp only [colouringOk] at hok ⊢
      rw [← hw]
      exact ⟨fun a b ha hb hab => hok.1 a b ((hl a).mpr ha) ((hl b).mpr hb) hab,
        hok.2⟩
    · exact slrMono h.2.2 (fun k hk => (hl k).mpr hk)
  have hp := evaluateApplyColour_Assign r e st cst f live lt hassign
  have hs : ∀ s : WordSemStateFiniteExact width C F,
      evaluate (.inst i) s = evaluate (.assign r e) s := by
    intro s
    rw [evaluate, evaluate, hi]
    unfold assign
    cases wordExp s e <;> rfl
  have ht : evaluate (applyColour f (.inst i)) cst =
      evaluate (applyColour f (.assign r e)) cst := by
    simp only [applyColour]
    rw [evaluate, evaluate, hc]
    unfold assign
    cases wordExp cst (applyColourExp f e) <;> rfl
  obtain ⟨perm, hp⟩ := hp
  refine ⟨perm, ?_⟩
  dsimp only at hp ⊢
  rw [hs, ht]
  exact hp

/-- HOL `evaluate_apply_colour[Inst]`, Const subcase (1228-1233).
Only the original three premises; the full existential postcondition. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstConst {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (w : BitVec width) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.const r w)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.const r w)) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.const r w)) live lt st cst := by
  intro st cst f live lt h
  apply assignmentInstructionCase (.const r w) r (.const w) st cst f live lt
    (fun _ => rfl) (fun _ => by simp [inst, applyColourInst, applyColourInstCore,
      applyColourExp, applyColourExpCore]) _ rfl h
  intro k
  simp [getLive, getLiveInst, getLiveInstCore, getLiveExp,
    sptDomain_uni, sptDomain_ln]

/-- HOL `evaluate_apply_colour[Inst]`, Binop subcase (1234-1248),
including both register and immediate operands, with no success premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstBinop {width : Nat} [NeZero width] {C F : Type}
    (op : BinOp) (dst src : Nat) (ri : WordRegImm (BitVec width)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.binop op dst src ri))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.binop op dst src ri))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.arith (.binop op dst src ri))) live lt st cst := by
  intro st cst f live lt h
  let e : WordLangExpHOL (BitVec width) :=
    .op op [.var src, match ri with | .reg r => .var r | .imm w => .const w]
  apply assignmentInstructionCase (.arith (.binop op dst src ri)) dst e st cst f live lt
    (fun _ => by cases ri <;> simp [inst, e]) _ _ rfl h
  · intro s
    cases ri <;> simp [inst, applyColourInst, applyColourInstCore, applyColourImmCore,
      applyColourExp, applyColourExpCore, e]
  · intro k
    cases ri <;> simp [getLive, getLiveInst, getLiveInstCore, getLiveExp, bigUnion,
      e, sptDomain_uni, sptDomain_ins, sptDomain_ln, or_assoc, or_comm]

/-- HOL `evaluate_apply_colour[Inst]`, Shift subcase (1249-1263),
retaining the expression-valued register/immediate shift operand. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstShift {width : Nat} [NeZero width] {C F : Type}
    (sh : Shift) (dst src : Nat) (ri : WordRegImm (BitVec width)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.shift sh dst src ri))) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.shift sh dst src ri))) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.arith (.shift sh dst src ri))) live lt st cst := by
  intro st cst f live lt h
  let e : WordLangExpHOL (BitVec width) :=
    .shift sh (.var src) (match ri with | .reg r => .var r | .imm w => .const w)
  apply assignmentInstructionCase (.arith (.shift sh dst src ri)) dst e st cst f live lt
    (fun _ => by cases ri <;> simp [inst, e]) _ _ rfl h
  · intro s
    cases ri <;> simp [inst, applyColourInst, applyColourInstCore, applyColourImmCore,
      applyColourExp, applyColourExpCore, e]
  · intro k
    cases ri <;> simp [getLive, getLiveInst, getLiveInstCore, getLiveExp,
      e, sptDomain_uni, sptDomain_ins, sptDomain_ln, or_assoc, or_comm]

end Flapjack.WordAlloc
