import Flapjack.Compiler.Backend.WordCopy.Proofs.Invariant
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

/-!
# word_copyProof: `CPstate_models`

Ports of the `CPstate_models` group of `cakeml/compiler/backend/proofs/word_copyProofScript.sml`
(lines 270-434): the relation between a `copy_state` and the locals/store of a wordSem state,
its introduction/elimination forms, and its preservation by `remove_eq`, local updates,
`set_fp_var` and `merge_eqs`. HOL `FLOOKUP s.store` is `HolFiniteMapExact.lookup`.
-/

namespace Flapjack.Compiler.Backend.WordCopy

open Flapjack

/-- Exact HOL `CPstate_models_def` (`word_copyProofScript.sml:270-280`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_models_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def cpStateModels {width : Nat} [NeZero width] {C F : Type} (cs : CopyState)
    (S : WordSemStateFiniteExact width C F) : Prop :=
  (∀ v c vrep, sptLookup v cs.toEq = some c → sptLookup c cs.fromEq = some vrep →
      sptLookup v S.locals = sptLookup vrep S.locals) ∧
  (∀ s c vrep, cs.storeToEq.lookup s = some c → sptLookup c cs.fromEq = some vrep →
      S.store.lookup s = sptLookup vrep S.locals)

namespace WordCopyModelsWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordCopyModelsWitnesses

/-- Exact HOL `CPstate_models_with_const` (`word_copyProofScript.sml:282-306`): the relation
reads only `locals` and `store`, so all 21 other record updates leave it unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_models_with_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cpStateModelsWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {cs : CopyState}
    {s : WordSemStateFiniteExact width C F} {ls : Option Nat}
    {fp : HolFiniteMapExact Nat (BitVec 64)} {xs : List (WordSemStackFrame width)}
    {sl : Nat} {sm : Option Nat} {ssize : Spt Nat} {m : BitVec width → WordLocW width}
    {md smd : BitVec width → Bool} {p : Nat → Nat → Nat}
    {c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C)}
    {co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))}
    {cb : WordSemBuffer width 8} {db : WordSemBuffer width width} {g : WordSemGcFun width}
    {hd clk tdep : Nat} {cd : Spt (Nat × WordLangProgHOL (BitVec width))} {b : Bool}
    {ffi : HolFfiState F} :
    cpStateModels cs { s with localsSize := ls } = cpStateModels cs s ∧
    cpStateModels cs { s with fpRegs := fp } = cpStateModels cs s ∧
    cpStateModels cs { s with stack := xs } = cpStateModels cs s ∧
    cpStateModels cs { s with stackLimit := sl } = cpStateModels cs s ∧
    cpStateModels cs { s with stackMax := sm } = cpStateModels cs s ∧
    cpStateModels cs { s with stackSize := ssize } = cpStateModels cs s ∧
    cpStateModels cs { s with memory := m } = cpStateModels cs s ∧
    cpStateModels cs { s with mdomain := md } = cpStateModels cs s ∧
    cpStateModels cs { s with shMdomain := smd } = cpStateModels cs s ∧
    cpStateModels cs { s with permute := p } = cpStateModels cs s ∧
    cpStateModels cs { s with compile := c } = cpStateModels cs s ∧
    cpStateModels cs { s with compileOracle := co } = cpStateModels cs s ∧
    cpStateModels cs { s with codeBuffer := cb } = cpStateModels cs s ∧
    cpStateModels cs { s with dataBuffer := db } = cpStateModels cs s ∧
    cpStateModels cs { s with gcFun := g } = cpStateModels cs s ∧
    cpStateModels cs { s with handler := hd } = cpStateModels cs s ∧
    cpStateModels cs { s with clock := clk } = cpStateModels cs s ∧
    cpStateModels cs { s with termdep := tdep } = cpStateModels cs s ∧
    cpStateModels cs { s with code := cd } = cpStateModels cs s ∧
    cpStateModels cs { s with be := b } = cpStateModels cs s ∧
    cpStateModels cs { s with ffi := ffi } = cpStateModels cs s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- Exact HOL `CPstate_model` (`word_copyProofScript.sml:308-314`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_model"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cpStateModel {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {v : Nat} :
    cpStateModels cs st → sptLookup (lookupEq cs v) st.locals = sptLookup v st.locals := by
  intro ⟨h1, _⟩
  rcases lookupEq_cases cs v with ⟨hv, _⟩ | ⟨c, r, hc, hr, hv⟩
  · rw [hv]
  · rw [hv]; exact (h1 v c r hc hr).symm

/-- Exact HOL `CPstate_modelsI` (`word_copyProofScript.sml:316-335`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsI"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cpStateModelsI {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} :
    cpStateInv cs ∧
      (∀ x y, lookupEq cs x = lookupEq cs y → sptLookup x st.locals = sptLookup y st.locals) ∧
      (∀ x y, lookupStoreEq cs x = some (lookupEq cs y) →
        st.store.lookup x = sptLookup y st.locals) →
    cpStateModels cs st := by
  rintro ⟨⟨_, _, _, h4⟩, hl, hs⟩
  have hrep : ∀ c r, sptLookup c cs.fromEq = some r → lookupEq cs r = r := fun c r hr =>
    lookupEqI cs r r (Or.inr ⟨c, h4 c r hr, hr⟩)
  refine ⟨fun v c vrep hv hc => hl v vrep ?_, fun s c vrep hsc hc => hs s vrep ?_⟩
  · rw [hrep c vrep hc]; exact lookupEqI cs vrep v (Or.inr ⟨c, hv, hc⟩)
  · rw [hrep c vrep hc]; simp [lookupStoreEq, hsc, hc]

/-- Exact HOL `CPstate_modelsD` (`word_copyProofScript.sml:337-350`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cpStateModelsD {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} :
    cpStateInv cs ∧ cpStateModels cs st →
      (∀ x y, lookupEq cs x = lookupEq cs y → sptLookup x st.locals = sptLookup y st.locals) ∧
      (∀ x y, lookupStoreEq cs x = some (lookupEq cs y) →
        st.store.lookup x = sptLookup y st.locals) := by
  rintro ⟨hinv, h1, h2⟩
  refine ⟨fun x y h => ?_, fun x y h => ?_⟩
  · rcases sameClassD ⟨hinv, h⟩ with rfl | ⟨_, c, rep, hx, hy, hc⟩
    · rfl
    · rw [h1 x c rep hx hc, h1 y c rep hy hc]
  · obtain ⟨c, rep, hx, hy, hc⟩ := sameClassD' ⟨hinv, h⟩
    rw [h2 x c rep hx hc, h1 y c rep hy hc]

/-- `empty_eq` models every state (Flapjack infrastructure, from `empty_eq_def`). -/
theorem emptyEqModels {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) : cpStateModels emptyEq st :=
  ⟨fun _ _ _ h => by simp [emptyEq] at h,
    fun _ _ _ h => by simp [emptyEq] at h⟩

/-- Exact HOL `remove_eq_model` (`word_copyProofScript.sml:352-358`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem removeEqModel {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {t : Nat} :
    cpStateModels cs st → cpStateModels (removeEq cs t) st := by
  intro h
  unfold removeEq
  split
  · exact h
  · exact emptyEqModels st

/-- Exact HOL `remove_eq_model_insert'` (`word_copyProofScript.sml:360-375`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_insert'"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem removeEqModelInsert' {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st st' : WordSemStateFiniteExact width C F} {t : Nat} {val : WordLocW width} :
    cpStateInv cs ∧ cpStateModels cs st ∧ st'.locals = sptInsert t val st.locals ∧
      st'.store = st.store →
    cpStateModels (removeEq cs t) st' := by
  rintro ⟨⟨_, _, _, h4⟩, ⟨m1, m2⟩, hl, hs⟩
  unfold removeEq
  cases ht : sptLookup t cs.toEq with
  | some _ => exact emptyEqModels st'
  | none =>
      dsimp only
      have hne : ∀ c vrep, sptLookup c cs.fromEq = some vrep → vrep ≠ t := by
        rintro c vrep hc rfl; have := h4 c vrep hc; rw [ht] at this; cases this
      refine ⟨fun v c vrep hv hc => ?_, fun s c vrep hsc hc => ?_⟩
      · have hvt : v ≠ t := by rintro rfl; rw [ht] at hv; cases hv
        rw [hl, sptLookupInsert, if_neg hvt, sptLookupInsert, if_neg (hne c vrep hc)]
        exact m1 v c vrep hv hc
      · rw [hl, hs, sptLookupInsert, if_neg (hne c vrep hc)]
        exact m2 s c vrep hsc hc

/-- Exact HOL `remove_eq_model_insert` (`word_copyProofScript.sml:377-386`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_insert"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem removeEqModelInsert {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {t : Nat} {val : WordLocW width} :
    cpStateInv cs → cpStateModels cs st →
      cpStateModels (removeEq cs t) { st with locals := sptInsert t val st.locals } :=
  fun hinv hm => removeEqModelInsert' ⟨hinv, hm, rfl, rfl⟩

/-- Exact HOL `remove_eq_model_set_var` (`word_copyProofScript.sml:388-397`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem removeEqModelSetVar {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {t : Nat} {val : WordLocW width} :
    cpStateInv cs ∧ cpStateModels cs st →
      cpStateModels (removeEq cs t) (WordSemStateFiniteExact.setVar t val st) :=
  fun ⟨hinv, hm⟩ => removeEqModelInsert' ⟨hinv, hm, rfl, rfl⟩

/-- Exact HOL `CPstate_models_same` (`word_copyProofScript.sml:399-406`). HOL leaves the
second state's `'c`/`'ffi` parameters independent of the first's; so does the Lean statement. -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_models_same"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cpStateModelsSame {width : Nat} [NeZero width] {C F C' F' : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {st' : WordSemStateFiniteExact width C' F'} :
    cpStateModels cs st ∧ st'.locals = st.locals ∧ st'.store = st.store →
      cpStateModels cs st' := by
  rintro ⟨⟨m1, m2⟩, hl, hs⟩
  refine ⟨fun v c vrep hv hc => ?_, fun s c vrep hsc hc => ?_⟩
  · rw [hl]; exact m1 v c vrep hv hc
  · rw [hl, hs]; exact m2 s c vrep hsc hc

/-- Exact HOL `set_fp_var_model` (`word_copyProofScript.sml:408-416`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_fp_var_model"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setFpVarModel {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {t : Nat} {val : BitVec 64} :
    cpStateModels cs st → cpStateModels cs (WordSemStateFiniteExact.setFpVar t val st) :=
  fun h => cpStateModelsSame ⟨h, rfl, rfl⟩

/-- A key of `inter_eq` is a key of both trees with the same value (Flapjack infrastructure,
from `lookup_inter_eq`). -/
theorem sptLookupInterEq_some {a b : Spt Nat} {k v : Nat} :
    sptLookup k (sptInterEq a b) = some v → sptLookup k a = some v ∧ sptLookup k b = some v := by
  rw [sptLookupInterEq]
  cases h : sptLookup k a with
  | none => intro h'; cases h'
  | some x =>
      dsimp only
      split
      · rename_i h2; intro h'; cases h'; exact ⟨rfl, h2⟩
      · intro h'; cases h'

/-- Exact HOL `merge_eqs_model1` (`word_copyProofScript.sml:418-425`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "merge_eqs_model1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem mergeEqsModel1 {width : Nat} [NeZero width] {C F : Type} {cs1 cs2 : CopyState}
    {st : WordSemStateFiniteExact width C F} :
    cpStateModels cs1 st → cpStateModels (mergeEqs cs1 cs2) st := by
  rintro ⟨m1, m2⟩
  refine ⟨fun v c vrep hv hc => ?_, fun s c vrep hsc hc => ?_⟩
  · exact m1 v c vrep (sptLookupInterEq_some hv).1 (sptLookupInterEq_some hc).1
  · have := (List.mem_filter.mp (listMemOfLookup hsc)).2
    simp only [decide_eq_true_eq] at this
    exact m2 s c vrep this.1 (sptLookupInterEq_some hc).1

/-- Exact HOL `merge_eqs_model2` (`word_copyProofScript.sml:427-434`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "merge_eqs_model2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem mergeEqsModel2 {width : Nat} [NeZero width] {C F : Type} {cs1 cs2 : CopyState}
    {st : WordSemStateFiniteExact width C F} :
    cpStateModels cs2 st → cpStateModels (mergeEqs cs1 cs2) st := by
  rintro ⟨m1, m2⟩
  refine ⟨fun v c vrep hv hc => ?_, fun s c vrep hsc hc => ?_⟩
  · exact m1 v c vrep (sptLookupInterEq_some hv).2 (sptLookupInterEq_some hc).2
  · have := (List.mem_filter.mp (listMemOfLookup hsc)).2
    simp only [decide_eq_true_eq] at this
    exact m2 s c vrep this.2 (sptLookupInterEq_some hc).2

end Flapjack.Compiler.Backend.WordCopy
