import Flapjack.Compiler.Backend.WordCopy.Proofs.Store

/-!
# word_copyProof: `copy_prop_inst` semantics

Ports of `copy_prop_inst_eval` and `copy_prop_inst_correct` from
`cakeml/compiler/backend/proofs/word_copyProofScript.sml` (lines 919-954): the rewritten
instruction evaluates like the original under a modelled `copy_state`, and the updated
`copy_state` models the resulting state. Both reach the wordSem `inst`, hence the inherited
`reals_as_rational_cuts` assumption.
-/

namespace Flapjack.Compiler.Backend.WordCopy

open Flapjack

namespace WordCopyInstWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordCopyInstWitnesses

section
variable {width : Nat} [NeZero width] {C F : Type}

private theorem evInst (s : WordSemStateFiniteExact width C F) (i : WordLangInst (BitVec width)) :
    Flapjack.WordSemStateFiniteExact.evaluate (.inst i) s =
      match WordSemStateFiniteExact.inst i s with
      | some s1 => (none, s1)
      | none => (some .error, s) :=
  (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.1 s i

private theorem instCong {s : WordSemStateFiniteExact width C F} {i i' : WordLangInst (BitVec width)}
    (h : WordSemStateFiniteExact.inst i' s = WordSemStateFiniteExact.inst i s) :
    Flapjack.WordSemStateFiniteExact.evaluate (.inst i') s =
      Flapjack.WordSemStateFiniteExact.evaluate (.inst i) s := by
  rw [evInst, evInst, h]

end

/-- Exact HOL `copy_prop_inst_eval` (`word_copyProofScript.sml:919-929`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_inst_eval"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyPropInstEval {width : Nat} [NeZero width] {C F : Type} :
    ∀ (ins : WordLangInst (BitVec width)) (cs : CopyState) (st : WordSemStateFiniteExact width C F)
      (prog' : WordLangProgHOL (BitVec width)) (cs' : CopyState),
      cpStateInv cs → cpStateModels cs st → (prog', cs') = copyPropInst ins cs →
      Flapjack.WordSemStateFiniteExact.evaluate prog' st =
        Flapjack.WordSemStateFiniteExact.evaluate (.inst ins) st := by
  intro ins cs st prog' cs' hinv hm h
  have gv : ∀ x, WordSemStateFiniteExact.getVar (lookupEq cs x) st =
      WordSemStateFiniteExact.getVar x st := fun x => cpStateModelsDGetVar ⟨hinv, hm⟩
  have gvi : ∀ x, WordSemStateFiniteExact.wordExp st (.var (lookupEq cs x)) =
      WordSemStateFiniteExact.wordExp st (.var x) := fun x => cpStateModelsDVar ⟨hinv, hm⟩
  have gvs : ∀ (l l' : List Nat), l'.map (fun x => WordSemStateFiniteExact.getVar x st) =
      l.map (fun x => WordSemStateFiniteExact.getVar x st) →
      WordSemStateFiniteExact.getVars l' st = WordSemStateFiniteExact.getVars l st :=
    fun _ _ h => mapGetVarEqD h
  have gadr : ∀ (a : Nat) (w : BitVec width),
      WordSemStateFiniteExact.wordExp st (.op .add [.var (lookupEq cs a), .const w]) =
        WordSemStateFiniteExact.wordExp st (.op .add [.var a, .const w]) := by
    intro a w; apply wordExpCongOp; simp only [List.map_cons, List.map_nil, gvi]
  have hif : ∀ (a b r : Nat), WordSemStateFiniteExact.getVar (if lookupEq cs a = r then a else
      lookupEq cs a) st = WordSemStateFiniteExact.getVar a st := by
    intro a b r; split
    · rfl
    · exact gv a
  rcases ins with _ | ⟨r, w⟩ | ⟨a⟩ | ⟨m, r, ⟨a, w⟩⟩ | ⟨f⟩
  · simp only [copyPropInst, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rw [(WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C) (F := F)).1 st,
      evInst]
    rfl
  · simp only [copyPropInst, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  · cases a with
    | binop bop r1 r2 ri =>
        cases ri with
        | imm w =>
            simp only [copyPropInst, lookupEqImm, reduceCtorEq, if_false, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            apply instCong
            simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign]
            rw [wordExpCongOp (aa := [.var r2, .const w]) ?_]
            simp only [List.map_cons, List.map_nil, gvi]
        | reg r3 =>
            by_cases hc : lookupEq cs r3 = r1 <;>
              simp only [copyPropInst, lookupEqImm, WordRegImm.reg.injEq, hc, if_true, if_false,
                Prod.mk.injEq] at h <;>
              obtain ⟨rfl, -⟩ := h <;>
              apply instCong <;>
              simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign] <;>
              rw [wordExpCongOp (aa := [.var r2, .var r3]) ?_] <;>
              simp only [List.map_cons, List.map_nil, gvi]
    | shift sh r1 r2 ri =>
        cases ri with
        | imm w =>
            simp only [copyPropInst, lookupEqImm, reduceCtorEq, if_false, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            apply instCong
            simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign]
            rw [wordExpCongShift (gvi r2) rfl]
        | reg r3 =>
            by_cases hc : lookupEq cs r3 = r1 <;>
              simp only [copyPropInst, lookupEqImm, WordRegImm.reg.injEq, hc, if_true, if_false,
                Prod.mk.injEq] at h <;>
              obtain ⟨rfl, -⟩ := h <;>
              apply instCong <;>
              simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign]
            · rw [wordExpCongShift (gvi r2) rfl]
            · rw [wordExpCongShift (gvi r2) (gvi r3)]
    | div r1 r2 r3 =>
        simp only [copyPropInst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        apply instCong
        simp only [WordSemStateFiniteExact.inst]
        rw [gvs [r3, r2] _ (by simp only [List.map_cons, List.map_nil, gv])]
    | longMul r1 r2 r3 r4 =>
        simp only [copyPropInst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl
    | longDiv r1 r2 r3 r4 r5 =>
        simp only [copyPropInst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        apply instCong
        simp only [WordSemStateFiniteExact.inst]
        rw [gvs [r3, r4, r5] _ (by simp only [List.map_cons, List.map_nil, gv])]
    | addCarry r1 r2 r3 r4 =>
        simp only [copyPropInst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        apply instCong
        simp only [WordSemStateFiniteExact.inst]
        rw [gvs [r2, r3, r4] _ (by simp only [List.map_cons, List.map_nil, gv, hif r3 r3 r1])]
    | addOverflow r1 r2 r3 r4 =>
        simp only [copyPropInst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        apply instCong
        simp only [WordSemStateFiniteExact.inst]
        rw [gvs [r2, r3] _ (by simp only [List.map_cons, List.map_nil, gv, hif r3 r3 r1])]
    | subOverflow r1 r2 r3 r4 =>
        simp only [copyPropInst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        apply instCong
        simp only [WordSemStateFiniteExact.inst]
        rw [gvs [r2, r3] _ (by simp only [List.map_cons, List.map_nil, gv, hif r3 r3 r1])]
  · cases m <;> simp only [copyPropInst, Prod.mk.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      apply instCong <;> simp only [WordSemStateFiniteExact.inst, gadr, gv]
  · cases f with
    | fpMovFromReg d r1 r2 =>
        by_cases hq : lookupEq cs r1 = lookupEq cs r2
        · simp only [copyPropInst, hq, if_true, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rfl
        · simp only [copyPropInst, hq, if_false, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          apply instCong
          simp only [WordSemStateFiniteExact.inst, gv]
    | _ =>
        simp only [copyPropInst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl

/-- `mem_store` changes only the memory (Flapjack infrastructure). -/
theorem memStoreModel {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st s1 : WordSemStateFiniteExact width C F} {a : BitVec width} {w : WordLocW width}
    (hm : cpStateModels cs st) (h : WordSemStateFiniteExact.memStore a w st = some s1) :
    cpStateModels cs s1 := by
  unfold WordSemStateFiniteExact.memStore at h
  split at h
  · cases h; exact cpStateModelsSame ⟨hm, rfl, rfl⟩
  · cases h

/-- The updated `copy_state` of `copy_prop_inst` models the state `inst` produces (Flapjack
infrastructure, the models half of `copy_prop_inst_correct`). -/
theorem copyPropInst_model {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st s1 : WordSemStateFiniteExact width C F} (ins : WordLangInst (BitVec width))
    (hinv : cpStateInv cs) (hm : cpStateModels cs st)
    (hi : WordSemStateFiniteExact.inst ins st = some s1) :
    cpStateModels (copyPropInst ins cs).2 s1 := by
  rcases ins with _ | ⟨r, w⟩ | ⟨a⟩ | ⟨m, r, ⟨a, w⟩⟩ | ⟨f⟩
  all_goals try cases a
  all_goals try cases m
  all_goals try cases f
  all_goals simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign] at hi
  all_goals
    repeat'
      first
      | (cases hi; done)
      | (simp only [Option.some.injEq] at hi; subst hi)
      | split at hi
  all_goals try dsimp only [copyPropInst, removeEqs]
  all_goals
    first
    | exact hm
    | exact removeEqModelSetVar ⟨hinv, hm⟩
    | exact removeEqModelSetVar ⟨removeEqInv _ _ hinv, removeEqModelSetVar ⟨hinv, hm⟩⟩
    | exact removeEqModel (removeEqModelSetVar ⟨hinv, hm⟩)
    | exact setFpVarModel hm
    | exact cpStateModelsSame ⟨hm, rfl, rfl⟩
    | exact memStoreModel hm (by assumption)

/-- Exact HOL `copy_prop_inst_correct` (`word_copyProofScript.sml:937-954`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_inst_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyPropInstCorrect {width : Nat} [NeZero width] {C F : Type} {cs cs' : CopyState}
    {st st' : WordSemStateFiniteExact width C F} {ins : WordLangInst (BitVec width)}
    {prog' : WordLangProgHOL (BitVec width)} {err : Option (WordSemResult width)} :
    cpStateInv cs ∧ cpStateModels cs st ∧ copyPropInst ins cs = (prog', cs') ∧
      Flapjack.WordSemStateFiniteExact.evaluate (.inst ins) st = (err, st') →
    Flapjack.WordSemStateFiniteExact.evaluate prog' st = (err, st') ∧
      (err = none → cpStateModels cs' st') := by
  rintro ⟨hinv, hm, hc, he⟩
  refine ⟨(copyPropInstEval ins cs st prog' cs' hinv hm hc.symm).trans he, fun herr => ?_⟩
  subst herr
  rw [evInst] at he
  have hcs : cs' = (copyPropInst ins cs).2 := by rw [hc]
  subst hcs
  cases hi : WordSemStateFiniteExact.inst ins st with
  | none => rw [hi] at he; cases he
  | some s1 =>
      rw [hi] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact copyPropInst_model ins hinv hm hi

end Flapjack.Compiler.Backend.WordCopy
