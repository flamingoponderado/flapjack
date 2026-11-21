module

public import Flapjack.Pancake.Proofs.PanStructs
public import Flapjack.Misc.ListEl
public import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

@[expose] public section

/-! `pan_structsProofScript.sml:441-470`: a structure found by `ALOOKUP` in a
suffix of a valid context has a unique index in the whole context, that index is
in range, the `EL` entry is the looked-up one, and the field shapes are
well-formed from the following context.  HOL's total `EL` is the reviewed
`holEl`; the `Nonempty` instance it needs is discharged from the concrete
`MlS`/`StructInfoHOLExact` constructors below, so no hypothesis is added. -/

namespace Flapjack.Pancake.Proofs.PanStructs.StructInfosOkHelper

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
open Flapjack.Basis.Pure.MlString

local instance : Nonempty (MlS × StructInfoHOLExact) :=
  ⟨(ofString "", ⟨[], 0⟩)⟩

/-- Splitting `EVERY (is_wf_shape ctxt)` over a shape list into its members. -/
private theorem isWfShapesExactHOL_mem {α : Type} (context : List (MlS × α)) :
    ∀ (shapes : List ShapeHOL), isWfShapesExactHOL context shapes = true →
      ∀ sh, sh ∈ shapes → isWfShapeExactHOL context sh = true := by
  intro shapes
  induction shapes with
  | nil =>
    intro hall sh hmem
    simp at hmem
  | cons shape rest ih =>
    intro hall sh hmem
    simp only [isWfShapesExactHOL, Bool.and_eq_true] at hall
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hall.1
    · exact ih hall.2 sh hmem

/-- Bridge from the reviewed HOL `ALOOKUP` rendering `holAlookup` to the
`BEq`-based `List.lookup` used by the `afindi` list lemmas in this counterpart
module. Flapjack list infrastructure; no separate HOL declaration. -/
private theorem holAlookup_eq_lookup {α β : Type} [DecidableEq α] [BEq α]
    [LawfulBEq α] (entries : List (α × β)) (key : α) :
    holAlookup entries key = List.lookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨first, second⟩ := entry
    rw [holAlookup, List.lookup_cons]
    by_cases h : first = key
    · subst h
      simp
    · have hb : (key == first) = false := beq_eq_false_iff_ne.mpr (fun he => h he.symm)
      simp [h, hb, ih]

/-- Exact port of HOL `wf_shape_struct_infos_ok_helper[local]`
(`pan_structsProofScript.sml:441-470`). The typed capture
`wf_shape_struct_infos_ok_helper_typed`
(`pancake_pan_structs_proof_typed_probe.out`) gives
`ALOOKUP (DROP n ctxt) nm = SOME info ∧ struct_infos_ok ctxt ⇒
 ∃i. afindi nm (DROP n ctxt) = SOME i ∧ i + n < LENGTH ctxt ∧
     EL (i + n) ctxt = (nm,info) ∧ afindi nm ctxt = SOME (i + n) ∧
     ∀sh. MEM sh (MAP SND info.fields) ⇒
       is_wf_shape (DROP (i + n + 1) ctxt) sh`,
with the two conjuncts as ONE premise and the binder order `n ctxt nm info`.
`ALOOKUP` is the reviewed `holAlookup` (bridged to the `BEq`-based
`List.lookup` only inside the proof, because the `afindi` list lemmas of this
counterpart are stated over `List.lookup`), `struct_infos_ok` is
`structInfosOkHOLExact`, `LENGTH` is `.length`, `EL` is the reviewed total
`holEl` and `is_wf_shape` is `isWfShapeExactHOL`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "wf_shape_struct_infos_ok_helper"]
theorem wfShapeStructInfosOkHelper (n : Nat) (ctxt : StructContextExact) (nm : MlS)
    (info : StructInfoHOLExact)
    (h : holAlookup (ctxt.drop n) nm = some info ∧ structInfosOkHOLExact ctxt) :
    ∃ i : Nat,
      afindi nm (ctxt.drop n) = some i ∧
      i + n < ctxt.length ∧
      holEl (i + n) ctxt = (nm, info) ∧
      afindi nm ctxt = some (i + n) ∧
      ∀ sh, sh ∈ info.fields.map Prod.snd →
        isWfShapeExactHOL (ctxt.drop (i + n + 1)) sh = true := by
  obtain ⟨hlookupHol, hok⟩ := h
  have hlookup : List.lookup nm (ctxt.drop n) = some info := by
    rw [← holAlookup_eq_lookup]
    exact hlookupHol
  rw [structInfosOkHOLExact] at hok
  rcases hok with ⟨hfields, hkeys, hshapes, hsizes⟩
  have hafindiExists : ∃ i : Nat, afindi nm (ctxt.drop n) = some i ∧
      ((ctxt.drop n)[i]?).map Prod.snd = some info := by
    have hlu := afindi_lookup nm (ctxt.drop n)
    rw [hlookup] at hlu
    cases hfind : afindi nm (ctxt.drop n) with
    | none =>
      rw [hfind] at hlu
      simp at hlu
    | some i =>
      rw [hfind] at hlu
      simp only [Option.bind_some] at hlu
      exact ⟨i, rfl, hlu.symm⟩
  obtain ⟨i, haf, hget⟩ := hafindiExists
  have hpair : (ctxt.drop n)[i]? = some (nm, info) := by
    have hfst := afindi_el_fst nm (ctxt.drop n) i haf
    cases hx : (ctxt.drop n)[i]? with
    | none =>
      rw [hx] at hfst
      simp at hfst
    | some entry =>
      rw [hx] at hfst hget
      simp only [Option.map_some, Option.some.injEq] at hfst hget
      obtain ⟨first, second⟩ := entry
      dsimp only at hfst hget
      rw [hfst, hget]
  have hilt : i < (ctxt.drop n).length := afindi_less_length nm (ctxt.drop n) i haf
  have hlen : (ctxt.drop n).length = ctxt.length - n := List.length_drop
  have hnlt : i + n < ctxt.length := by omega
  have hmemGet : ctxt[i + n]? = some (nm, info) := by
    have hidx : i + n = n + i := Nat.add_comm i n
    rw [hidx, ← List.getElem?_drop (xs := ctxt) (i := n) (j := i)]
    exact hpair
  have hholEl : holEl (i + n) ctxt = (nm, info) := by
    rw [holEl_eq_getElem (i + n) ctxt hnlt]
    have hg := hmemGet
    rw [List.getElem?_eq_getElem hnlt] at hg
    exact Option.some.inj hg
  have hnotmem : nm ∉ (ctxt.take n).map Prod.fst :=
    (lookup_drop_helper n ctxt nm info hlookup hkeys).1
  have hnone : afindi nm (ctxt.take n) = none := by
    cases htake : afindi nm (ctxt.take n) with
    | none => rfl
    | some j =>
      exfalso
      apply hnotmem
      have hel := afindi_el_fst nm (ctxt.take n) j htake
      cases hx : (ctxt.take n)[j]? with
      | none =>
        rw [hx] at hel
        simp at hel
      | some entry =>
        rw [hx] at hel
        simp only [Option.map_some, Option.some.injEq] at hel
        exact List.mem_map.mpr ⟨entry, List.mem_of_getElem? hx, hel⟩
  have htakeLen : (ctxt.take n).length = n := by
    rw [List.length_take]
    omega
  have happend : afindi nm ctxt = some (i + n) := by
    have hcat := afindi_append nm (ctxt.take n) (ctxt.drop n)
    rw [List.take_append_drop] at hcat
    rw [hnone, haf] at hcat
    simp only [Option.map_some] at hcat
    rw [htakeLen] at hcat
    exact hcat
  refine ⟨i, haf, hnlt, hholEl, happend, ?_⟩
  intro sh hsh
  exact isWfShapesExactHOL_mem (ctxt.drop (i + n + 1))
    (info.fields.map Prod.snd) (hshapes (i + n) nm info hmemGet) sh hsh

end Flapjack.Pancake.Proofs.PanStructs.StructInfosOkHelper
