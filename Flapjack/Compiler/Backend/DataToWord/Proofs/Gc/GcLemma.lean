module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PushCallEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelGc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PopEnv
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PopEnvConst

@[expose] public section

/-! Generalized collection after saving and cutting the live environment. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
/-- Set up the source and target call states for the generalized collection proof. -/
private theorem preGcRelation {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (cutWords : Spt (WordLocW width) × Spt (WordLocW width)) (ss : Option Nat)
    (h : stateRel conf l1 l2 source target none locs ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    stateRel conf l1 l2 (DataSem.callEnv [] ss (DataSem.pushEnv cutData false source))
      (WordSemStateFiniteExact.callEnv [.loc l1 l2] ss
        (WordSemStateFiniteExact.pushEnv cutWords none target)) none ((l1,l2)::locs) := by
  obtain ⟨related, sourceCut, targetCut⟩ := h
  have incRel := stateRel_incClock conf l1 l2 source target locs related
  have sourceDec : DataSem.decClock {source with clock := source.clock + 1} = source := by
    simp [DataSem.decClock]
  have targetDec : WordSemStateFiniteExact.decClock {target with clock := target.clock + 1} = target := by
    simp [WordSemStateFiniteExact.decClock]
  have pushed := stateRel_callEnv_pushEnv conf l1 l2 l1 l2
    {source with clock := source.clock + 1} {target with clock := target.clock + 1} locs
    [] [] [] ss names cutData cutWords none
    ⟨incRel, rfl, rfl, sourceCut, targetCut⟩
  simpa only [sourceDec, targetDec, Option.isSome_none] using pushed

namespace GcLemmaGenWitnesses
/-- Canonical target-state roundtrip for relations with an existential store. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end GcLemmaGenWitnesses

/-- Generalized collection after saving the cut environment. The two unused
existentials retain independent inhabited HOL types from the source statement. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_lemma_gen"
  (fmap_as_finite_support_relation := [st, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (gc_lemma_existential_inhabitants := [W1._w1, W2._w2])]
theorem gcLemma_gen {width : Nat} [NeZero width] {C F W1 W2 : Type} [Nonempty W1] [Nonempty W2]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (cutWords : Spt (WordLocW width) × Spt (WordLocW width)) (ss : Option Nat) (k : Nat)
    (premises : DataSem.cutEnv names source.locals = some cutData ∧
      stateRel conf l1 l2 source target none locs ∧
      target.store.lookup .allocSize = some (.word (gcAllocSize k)) ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    (let t0 := WordSemStateFiniteExact.callEnv [.loc l1 l2] ss
      (WordSemStateFiniteExact.pushEnv cutWords none target);
    ∃ (t2 : WordSemStateFiniteExact width C F) (wl : List (WordLocW width))
      (m : BitVec width → WordLocW width) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (_w1 : W1) (_w2 : W2) (stack : List (WordSemStackFrame width)),
      t0.gcFun (wordSemEncStack t0.stack, t0.memory, t0.mdomain, t0.store) = some (wl, m, st) ∧
      wordSemDecStack wl t0.stack = some stack ∧
      WordSemStateFiniteExact.popEnv {t0 with stack := stack, store := st, memory := m} = some t2 ∧
      t2.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      t2.store.lookup .allocSize = some (.word (gcAllocSize k)) ∧
      (WordSemStateFiniteExact.hasSpace (.word (gcAllocSize k) : WordLocW width) t2 = some false ∧
        conf.gcKind ≠ .none ∧ DataSem.noThunksInRefs source.refs →
        ∀ (roots2 dups : List Flapjack.Compiler.Backend.DataSem.Value) (n2 : Nat) (r2 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (s2 : NumSet),
          roots2.Perm (dups ++ sptToList cutData ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) ∧
          (∀ v, v ∈ dups → v ∈ sptToList cutData ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) ∧
          DataSem.sizeOfValues source.limits roots2 source.refs .ln = (n2, r2, s2) →
            source.limits.heapLimit < n2 + k) ∧
      stateRel conf l1 l2 {source with locals := cutData, space := 0, stackMax := Option.map₂ max (Option.map₂ max source.stackMax (DataSem.sizeOfStack (.env source.localsSize cutData :: source.stack))) (Option.map₂ (· + ·) (DataSem.sizeOfStack (.env source.localsSize cutData :: source.stack)) ss)} t2 none locs) := by
  obtain ⟨sourceCut, related, allocRead, targetCut⟩ := premises
  let sc := DataSem.callEnv [] ss (DataSem.pushEnv cutData false source)
  let tc := WordSemStateFiniteExact.callEnv [.loc l1 l2] ss
    (WordSemStateFiniteExact.pushEnv cutWords none target)
  have incoming : stateRel conf l1 l2 sc tc none ((l1,l2)::locs) :=
    preGcRelation conf l1 l2 source target locs names cutData cutWords ss ⟨related, sourceCut, targetCut⟩
  have inputs : tc.store.lookup .allocSize = some (.word (gcAllocSize k)) ∧
      sc.locals = .ln ∧ tc.locals = .ls (.loc l1 l2) := by
    simpa [sc, tc, DataSem.callEnv, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.pushEnv, sptFromList, sptFromList2] using allocRead
  obtain ⟨_, wl, m, st, _, _, stack, gcRun, decode, tempRead, allocAfter, failed, gcRelated⟩ :=
    stateRel_gcGen (T2 := Unit) (W1 := Unit) (W2 := Unit)
      conf l1 l2 sc tc ((l1,l2)::locs) k incoming inputs
  let sourceEnd := {sc with locals := cutData, stack := source.stack, localsSize := source.localsSize, space := 0}
  have sourcePop : DataSem.popEnv {sc with space := 0} = some sourceEnd := by
    simp [sourceEnd, sc, DataSem.callEnv, DataSem.pushEnv, DataSem.popEnv]
  obtain ⟨t2, l3, l4, rest, targetPop, locsEq, postRel⟩ :=
    stateRel_popEnv conf l1 l2 {sc with space := 0} sourceEnd
      {tc with stack := stack, store := st, memory := m} none ((l1,l2)::locs) ⟨gcRelated, sourcePop⟩
  have storeAfter : t2.store = st := by
    have h := WordSemStateFiniteExact.popEnvConst _ _ targetPop
    exact h.2.2.2.2.2.2.2.2.1
  rcases List.cons.inj locsEq with ⟨pairEq, restEq⟩
  cases pairEq
  subst rest
  refine ⟨t2, wl, m, st, Classical.choice inferInstance, Classical.choice inferInstance,
    stack, gcRun, decode, targetPop, ?_, ?_, ?_, ?_⟩
  · simpa [storeAfter, tc, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv] using tempRead
  · simpa [storeAfter] using allocAfter
  · intro ⟨hasSpace, kind, thunks⟩
    have failedSpace : WordSemStateFiniteExact.hasSpace (.word (gcAllocSize k) : WordLocW width)
        {tc with store := st} = some false := by
      simpa [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, storeAfter] using hasSpace
    have failBound := failed ⟨failedSpace, kind, by simpa [sc, DataSem.callEnv, DataSem.pushEnv] using thunks⟩
    simpa [sc, DataSem.callEnv, DataSem.pushEnv, DataSem.extractStack, List.append_assoc] using failBound
  · simpa [stateRel, sourceEnd, sc, DataSem.callEnv, DataSem.pushEnv] using postRel
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
