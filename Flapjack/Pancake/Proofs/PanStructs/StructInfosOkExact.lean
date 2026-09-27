import Flapjack.HolRef
import Flapjack.Pancake.PanLang.Decl

namespace Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

open Flapjack.Pancake.PanLang

private theorem structInfosOkExact_lookup_mem
    (name : MlS) (entries : StructContextExact) (info : StructInfoHOLExact)
    (hlookup : structContextLookupHOL name entries = some info) :
    name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [structContextLookupHOL] at hlookup
  | cons entry entries ih =>
      obtain ⟨candidate, candidateInfo⟩ := entry
      by_cases hmatch : name = candidate
      · subst name
        simp
      · simp only [structContextLookupHOL, if_neg hmatch] at hlookup
        have htail := ih hlookup
        simp [hmatch, htail]

private theorem structInfosOkExact_lookup_drop
    (n : Nat) (context : StructContextExact) (name : MlS) (info : StructInfoHOLExact)
    (hlookup : structContextLookupHOL name (context.drop n) = some info)
    (hnodup : (context.map Prod.fst).Nodup) :
    structContextLookupHOL name context = some info := by
  induction n generalizing context with
  | zero => simpa using hlookup
  | succ n ih =>
      cases context with
      | nil => simp at hlookup
      | cons entry rest =>
          obtain ⟨candidate, candidateInfo⟩ := entry
          have hnames : (candidate :: rest.map Prod.fst).Nodup := by
            simpa using hnodup
          obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hnames
          have htail : structContextLookupHOL name (rest.drop n) = some info := by
            simpa using hlookup
          have hmemTail := structInfosOkExact_lookup_mem name (rest.drop n) info htail
          have hmemRest : name ∈ rest.map Prod.fst := by
            rw [List.map_drop] at hmemTail
            exact List.mem_of_mem_drop hmemTail
          have hne : name ≠ candidate := by
            intro heq
            apply hnot
            rw [← heq]
            exact hmemRest
          have hctx := ih rest htail hrest
          simpa [structContextLookupHOL, hne] using hctx

/-- Internal support for the exact `struct_infos_ok_cons` proof. This is the
    source `size_of_sh_with_ctxt_drop` argument specialized to exact carriers;
    the independently tagged counterpart lives in `CompileCorrect.lean`. -/
private theorem structInfosOkExact_sizeDrop (context : StructContextExact)
    (shape : ShapeHOL) (n : Nat)
    (hwf : isWfShapeExactHOL (context.drop n) shape = true)
    (hnodup : (context.map Prod.fst).Nodup) :
    sizeOfShapeWithContextHOL (context.drop n) shape =
      sizeOfShapeWithContextHOL context shape := by
  let contextDrop := context.drop n
  have hrec := sizeOfShapeWithContextHOL.induct
    (context := contextDrop)
    (motive_1 := fun sh =>
      isWfShapeExactHOL contextDrop sh = true →
        sizeOfShapeWithContextHOL contextDrop sh = sizeOfShapeWithContextHOL context sh)
    (motive_2 := fun shapes =>
      isWfShapesExactHOL contextDrop shapes = true →
        sizeOfShapesWithContextHOL contextDrop shapes =
          sizeOfShapesWithContextHOL context shapes)
    (case1 := by intro _; rfl)
    (case2 := by
      intro shapes ih hshapes
      simpa [sizeOfShapeWithContextHOL_comb] using ih hshapes)
    (case3 := by
      intro name info hlookup _
      have hctx := structInfosOkExact_lookup_drop n context name info hlookup hnodup
      simp [sizeOfShapeWithContextHOL, hlookup, hctx])
    (case4 := by
      intro name hlookup hwfname
      simp [isWfShapeExactHOL, hlookup] at hwfname)
    (case5 := by intro _; rfl)
    (case6 := by
      intro child rest ihChild ihRest hshapes
      simp only [isWfShapesExactHOL, Bool.and_eq_true] at hshapes
      obtain ⟨hchild, hrest⟩ := hshapes
      simp only [sizeOfShapesWithContextHOL]
      rw [ihChild hchild, ihRest hrest])
    shape
  exact hrec hwf

/-- Exact logical reading of HOL `struct_infos_ok_def`
    (`pan_structsProofScript.sml:68-76`). The context and entry are the HOL
    `mlstring`/`shape`/fields-and-size carriers `StructContextExact` and
    `StructInfoHOLExact`; in particular, no production `shapedFields` cache is
    present. HOL's Boolean invariant is represented as a Lean proposition.
    The four clauses retain the source field-key distinctness, context-key
    distinctness, suffix well-formedness, and context-based size condition. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "struct_infos_ok_def"]
def structInfosOkHOLExact (context : StructContextExact) : Prop :=
  (∀ entry ∈ context, (entry.2.fields.map Prod.fst).Nodup) ∧
  (context.map Prod.fst).Nodup ∧
  (∀ (i : Nat) (name : MlS) (info : StructInfoHOLExact),
      context[i]? = some (name, info) →
      isWfShapesExactHOL (context.drop (i + 1)) (info.fields.map Prod.snd) = true) ∧
  (∀ entry ∈ context,
      entry.2.size = sizeOfShapeWithContextHOL context
        (.comb (entry.2.fields.map Prod.snd)))

/-- Exact HOL `struct_infos_ok_cons`
    (`pan_structsProofScript.sml:132-139`). Its five premises and conclusion
    use the exact `StructContextExact` and `StructInfoHOLExact` carriers. The
    `List.Nodup` and exact Boolean well-formedness premises are Lean readings
    of HOL `ALL_DISTINCT` and `EVERY`; `structInfosOkHOLExact` expands to the
    four clauses of the tagged HOL definition above. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "struct_infos_ok_cons"]
theorem structInfosOkHOLExact_cons (xs : StructContextExact) (nm : MlS)
    (info : StructInfoHOLExact)
    (hxs : structInfosOkHOLExact xs)
    (hflds : (info.fields.map Prod.fst).Nodup)
    (hfresh : nm ∉ xs.map Prod.fst)
    (hwf : isWfShapesExactHOL xs (info.fields.map Prod.snd) = true)
    (hsize : info.size = sizeOfShapeWithContextHOL xs
      (.comb (info.fields.map Prod.snd))) :
    structInfosOkHOLExact ((nm, info) :: xs) := by
  rcases hxs with ⟨hfields, hkeys, hshapes, hsizes⟩
  have hkeysCons : (((nm, info) :: xs).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨hfresh, hkeys⟩
  have hsizeDrop (shape : ShapeHOL)
      (hshape : isWfShapeExactHOL xs shape = true) :
      sizeOfShapeWithContextHOL xs shape =
        sizeOfShapeWithContextHOL ((nm, info) :: xs) shape := by
    have hdrop := structInfosOkExact_sizeDrop
      ((nm, info) :: xs) shape 1 (by simpa using hshape) hkeysCons
    simpa using hdrop
  refine ⟨?_, hkeysCons, ?_, ?_⟩
  · intro entry hentry
    rcases List.mem_cons.mp hentry with hhead | htail
    · cases hhead
      exact hflds
    · exact hfields entry htail
  · intro i name oldInfo hget
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        obtain ⟨rfl, rfl⟩ := hget
        simpa using hwf
    | succ k =>
        simp only [List.getElem?_cons_succ] at hget
        have hdrop : ((nm, info) :: xs).drop (Nat.succ k + 1) = xs.drop (k + 1) := by
          rw [Nat.succ_eq_add_one, List.drop_succ_cons]
        rw [hdrop]
        exact hshapes k name oldInfo hget
  · intro entry hentry
    rcases List.mem_cons.mp hentry with hhead | htail
    · cases hhead
      have hwfComb : isWfShapeExactHOL xs
          (.comb (info.fields.map Prod.snd)) = true := by
        simpa [isWfShapeExactHOL] using hwf
      calc
        info.size = sizeOfShapeWithContextHOL xs
            (.comb (info.fields.map Prod.snd)) := hsize
        _ = sizeOfShapeWithContextHOL ((nm, info) :: xs)
            (.comb (info.fields.map Prod.snd)) := hsizeDrop _ hwfComb
    · obtain ⟨name, oldInfo⟩ := entry
      obtain ⟨i, hi, heq⟩ := List.getElem_of_mem htail
      have hget : xs[i]? = some (name, oldInfo) := by
        rw [List.getElem?_eq_getElem hi]
        exact congrArg some heq
      have hwfTail : isWfShapeExactHOL (xs.drop (i + 1))
          (.comb (oldInfo.fields.map Prod.snd)) = true := by
        have hfieldsWf := hshapes i name oldInfo hget
        simpa [isWfShapeExactHOL] using hfieldsWf
      have hdropOld := structInfosOkExact_sizeDrop xs
        (.comb (oldInfo.fields.map Prod.snd)) (i + 1) hwfTail hkeys
      have hdropCons := structInfosOkExact_sizeDrop ((nm, info) :: xs)
        (.comb (oldInfo.fields.map Prod.snd)) (i + 2) (by
          simpa [List.drop] using hwfTail) hkeysCons
      have hdropEq : ((nm, info) :: xs).drop (i + 2) = xs.drop (i + 1) := by
        simp [List.drop]
      rw [hdropEq] at hdropCons
      calc
        oldInfo.size = sizeOfShapeWithContextHOL xs
            (.comb (oldInfo.fields.map Prod.snd)) := hsizes (name, oldInfo) htail
        _ = sizeOfShapeWithContextHOL (xs.drop (i + 1))
            (.comb (oldInfo.fields.map Prod.snd)) := hdropOld.symm
        _ = sizeOfShapeWithContextHOL ((nm, info) :: xs)
            (.comb (oldInfo.fields.map Prod.snd)) := hdropCons

end Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
