import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.GlobalUpdateSupport
import Flapjack.Pancake.Proofs.PanGlobals.GlobalStoreReload
import Flapjack.Pancake.Proofs.PanGlobals.GlobalStorePreservation

namespace Flapjack.PanGlobalsCompileCorrectAssignGlobal
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical state roundtrips for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Flapjack-only assembly of the original Assign memory and global-update
obligations. All store success, reload and post-relation facts are derived here;
there is no separately named HOL declaration for this proof infrastructure. -/
private theorem globalWriteRelation {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width σ)
    (name : MlS) (oldValue value : ValueHOL width)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hlookup : source.globals.lookup name = some oldValue)
    (hshape : shapeOfHOLExact value = shapeOfHOLExact oldValue) :
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    ∃ address memory,
      context.globals.lookup name = some (shapeOfHOLExact value, address) ∧
      panMemStoresHOL (target.topAddr - address) (flattenHOL value)
        target.memaddrs target.memory = some memory ∧
      panGlobalsStateRelHOLExact true context
        (setGlobalHOLFinite name value source) {target with memory := memory} := by
  classical
  obtain ⟨address, memory, hc, hstore, hload⟩ :=
    PanGlobalsGlobalStoreReload.stateRel_storeReload context source target name oldValue value
      hrel hlookup hshape
  have hcOld : context.globals.lookup name = some (shapeOfHOLExact oldValue, address) := by
    simpa only [hshape] using hc
  obtain ⟨hother, hmemoryNew⟩ := PanGlobalsGlobalStorePreservation.stateRel_storePreserves
    context source target name oldValue value address memory hrel hlookup hcOld hshape hstore
  rcases hrel with ⟨htoprel, hlocals, hbase, hbe, heshapes, hclock, hsstructs, htstructs,
    hglobals, hcontextWf, hsub, hshared, _, hffi, hcode, hdisjoint, hnot, htop, hw⟩
  have hsupport := PanGlobalsGlobalUpdateSupport.globalUpdate_invariants source target.topAddr
    context.globals name oldValue value hlookup hshape hdisjoint
  refine ⟨address, memory, hc, hstore, htoprel, hlocals, hbase, hbe, heshapes, hclock,
    hsstructs, htstructs, ?_, hcontextWf, hsub, hshared, hmemoryNew, hffi, hcode,
    hsupport.2.1, hnot, htop, hw⟩
  intro key stored hkey
  change (source.globals.update (name, value)).lookup key = some stored at hkey
  rw [HolFiniteMapExact.lookup_update_pointwise] at hkey
  by_cases heq : key = name
  · subst key
    simp only [if_true, Option.some.injEq] at hkey
    subst stored
    obtain ⟨oldAddress, hc0, hwf, _, hseparate, haligned⟩ := hglobals name oldValue hlookup
    have ha : oldAddress = address := by
      rw [hcOld] at hc0
      exact (congrArg Prod.snd (Option.some.inj hc0)).symm
    subst oldAddress
    refine ⟨address, hc, ?_, hload, ?_, haligned⟩
    · simpa only [hshape] using hwf
    · simpa only [setGlobalHOLFinite, hshape] using hseparate
  · simp only [if_neg heq] at hkey
    obtain ⟨otherAddress, hc', hwf', _, hseparate', haligned'⟩ := hglobals key stored hkey
    obtain ⟨otherAddress', hc'', hload'⟩ := hother key stored heq hkey
    have ha : otherAddress' = otherAddress := by
      rw [hc'] at hc''
      exact (congrArg Prod.snd (Option.some.inj hc'')).symm
    subst otherAddress'
    exact ⟨otherAddress, hc', hwf', hload', hseparate', haligned'⟩

/-- Global-variable branch of HOL compile_correct's original Assign case
(535-591). The original source relation, evaluation and non-Error conjunction
imply an existential compiled run and the full post-state relation. Arbitrary
structured values are admitted; expression correctness and all memory/update
obligations are proved internally, with no induction or successful-store premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_AssignGlobal {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name : MlS) (expression : ExpHOL width) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.assign .global name expression) = (res, post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.assign .global name expression)) =
          (res, targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel, hev, hne⟩
  rw [evaluateHOLFiniteState_assign] at hev
  cases hi : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) expression with
  | none =>
    simp only [hi] at hev
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact False.elim (hne rfl)
  | some value =>
    simp only [hi] at hev
    by_cases hv : isValidValueHOLFinite source .global name value = true
    · simp only [hv, ite_true] at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      cases hl : source.globals.lookup name with
      | none => simp [isValidValueHOLFinite, lookupKvarHOLFinite, hl] at hv
      | some oldValue =>
        have hshape : shapeOfHOLExact value = shapeOfHOLExact oldValue := by
          apply (shapeEqHOL_eq_true _ _).mp
          simpa only [isValidValueHOLFinite, lookupKvarHOLFinite, hl] using hv
        obtain ⟨address, memory, hc, hstore, hrelNew⟩ :=
          globalWriteRelation context source target name oldValue value hrel hl hshape
        have he := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source expression value
          context target ⟨hrel, hi⟩
        change evalHOLExact target.toExact (compileExpExactHOL context expression) = some value at he
        have haddress : evalHOLExact target.toExact (.op .sub [.topAddr, .const address]) =
            some (.val (.word (target.topAddr - address))) := by
          simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, wordOpHOL, wordOp]
        refine ⟨{target with memory := memory}, ?_, hrelNew⟩
        simp only [compileProgExactHOL, hc, evaluateHOLFiniteState_store, haddress, he, hstore]
    · simp only [hv] at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact False.elim (hne rfl)

end Flapjack.PanGlobalsCompileCorrectAssignGlobal
