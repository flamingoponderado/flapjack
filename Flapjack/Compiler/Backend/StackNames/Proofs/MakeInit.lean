import Flapjack.Compiler.Backend.StackNames.Proofs.CompileSemantics
import Flapjack.Misc.PredSet

/-!
# stack_namesProof: `make_init_def` and `make_init_semantics`

Ports of `cakeml/compiler/backend/proofs/stack_namesProofScript.sml` lines 557-587: the initial
state of the stack_names target, built with the left inverse `LINV (find_name f) UNIV`
(`holLinv`), has the semantics of the renamed program's state.
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps Flapjack.StackSemEvaluate

namespace MakeInit

/-- Canonical imported StackSem carrier roundtrip for the `make_init` ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end MakeInit

/-- Exact HOL `make_init_def` (`stack_namesProofScript.sml:557-569`). `LINV (find_name f) UNIV`
is `holLinv (findNameSpt f) (fun _ => True)`, `MAP_KEYS` the choice rendering
`HolFiniteMapExact.mapKeys`, and `IMAGE` over the Boolean `ffi_save_regs` set the decided
existential, as in `rename_state_def`. The commented-out buffer resets of the HOL source are
not part of the definition. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "make_init_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def makeInit {width : Nat} [NeZero width] {C F : Type} (f : Spt Nat)
    (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  open Classical in
  { s with
    code := code
    regs := HolFiniteMapExact.mapKeys (holLinv (findNameSpt f) (fun _ => True)) s.regs
    compile := fun cfg => s.compile cfg ∘ compileHOL f
    compileOracle := oracle
    ffiSaveRegs := fun y =>
      decide (∃ x, s.ffiSaveRegs x = true ∧ y = holLinv (findNameSpt f) (fun _ => True) x) }

namespace MakeInit

/-- HOL `MAP_KEYS_BIJ_LINV` on the finite-support carrier (Flapjack infrastructure). -/
theorem mapKeys_mapKeys_linv {β : Type} {g : Nat → Nat} (hg : Function.Bijective g)
    (m : HolFiniteMapExact Nat β) :
    HolFiniteMapExact.mapKeys g (HolFiniteMapExact.mapKeys (holLinv g (fun _ => True)) m) = m := by
  have hinv : ∀ y, g (holLinv g (fun _ => True) y) = y := apply_holLinv_of_surjective hg.2
  have hlinj : Function.Injective (holLinv g (fun _ => True)) := by
    intro a b hab; rw [← hinv a, ← hinv b, hab]
  apply HolFiniteMapExact.ext_lookup
  intro j
  rw [← hinv j, HolFiniteMapExact.lookup_mapKeys_of_injective hg.1,
    HolFiniteMapExact.lookup_mapKeys_of_injective hlinj, hinv j]

end MakeInit

/-- Exact HOL `make_init_semantics` (`stack_namesProofScript.sml:571-587`). HOL's free `s`,
`f`, `code`, `oracle` and `start` are the implicit binders; `ALL_DISTINCT` is `List.Nodup`,
`I ## compile f ## I` is `Prod.map id (Prod.map (compileHOL f) id)`. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "make_init_semantics"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem makeInitSemantics {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} {f : Spt Nat} {code : List (Nat × HolProg width)}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)} {start : Nat} :
    ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧ Function.Bijective (findNameSpt f) ∧
        (code.map Prod.fst).Nodup ∧ s.code = sptFromAList (compileHOL f code) ∧
        s.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle →
      semantics start s = semantics start (makeInit f (sptFromAList code) oracle s) := by
  rintro ⟨ha, hs, hk, hf, -, hcode, hor⟩
  have hinv : ∀ y, findNameSpt f (holLinv (findNameSpt f) (fun _ => True) y) = y :=
    apply_holLinv_of_surjective hf.2
  refine compileSemanticsAlt (f := f) _ s ⟨hf, ?_, rfl, ha, hs, hk⟩
  have hc : sptFromAList (compileHOL f (sptToAList (sptFromAList code))) = s.code := by
    rw [hcode]
    refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
    rw [sptLookup_sptFromAList, sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
      sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, sptLookup_sptFromAList,
      sptAListLookup_compileHOL]
  classical
  have hsave : (fun y => decide (∃ x, decide (∃ z, s.ffiSaveRegs z = true ∧
      x = holLinv (findNameSpt f) (fun _ => True) z) = true ∧ y = findNameSpt f x)) =
      s.ffiSaveRegs := by
    funext y
    by_cases hy : s.ffiSaveRegs y = true
    · rw [hy, decide_eq_true_iff]
      exact ⟨holLinv (findNameSpt f) (fun _ => True) y,
        decide_eq_true_iff.mpr ⟨y, hy, rfl⟩, (hinv y).symm⟩
    · rw [Bool.not_eq_true] at hy
      rw [hy, decide_eq_false_iff_not]
      rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := decide_eq_true_iff.mp hx
      rw [hinv z, hz] at hy
      exact Bool.noConfusion hy
  simp only [renameState, makeInit, MakeInit.mapKeys_mapKeys_linv hf, hc, ← hor]
  refine Eq.trans ?_ (show { s with ffiSaveRegs := s.ffiSaveRegs } = s from rfl)
  congr 1

end Flapjack.Compiler.Backend.StackNames
