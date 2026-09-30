import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.Semantics.PanCommonProps

/-!
# crep_inline: locals-update and `res_var` lookup lemmas of the Call case

Counterparts of `cakeml/pancake/proofs/crep_inlineProofScript.sml:2586-2717`
(bead `flapjack-pxn.18.5.5.48`), used by the inlined `Tail`/`Nontail` paths of
`inline_prog_correct`'s Call case.  The cluster also contains
`FOLDL_res_var_ZIP_lookup_var` and `FOLDL_res_var_ZIP_lookup`, which are
already ported in `Flapjack.Pancake.Proofs.CrepInline`.

Renderings, as in the other crep_inline ports:
* HOL `|++` (`FUPDATE_LIST`) on a finite map is `HolFiniteMapExact.updateListEq`;
* `FLOOKUP` is `.lookup`, `OPT_MMAP` is `List.mapM`, and `SUBMAP` is
  `HolFiniteMapExact.submap`;
* `res_var` is the tagged `HolFiniteMapExact.resVarEq`;
* `var_cexp` is `crepExpVarsHOL`, and `FLAT (MAP var_cexp es)` is
  `(es.map crepExpVarsHOL).flatten`;
* `FDOM f` is `crepHolFdom f.lookup`.  `FDIFF f s SUBMAP g` is `crepHolSubmap`
  of the generic lookup-level `FDIFF` below and `g.lookup`.
-/

namespace Flapjack

namespace CrepInlineUpdateListLocals

open HolFiniteMapExact

/-- HOL `FDIFF f s` on lookup functions: `f` restricted to the complement of
    the key set `s`.  Key-generic companion of the `Nat`-keyed `crepHolFdiff`.
    Untagged infrastructure. -/
def holFdiff {κ β : Type} (f : κ → Option β) (s : κ → Bool) : κ → Option β :=
  fun k => if s k then none else f k

/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- A lookup at a key outside the update keys is unchanged. -/
private theorem lookup_updateListEq_zip_not_mem {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (zs : List α) (ys : List β) (x : α) (hx : x ∉ zs) :
    (m.updateListEq (zs.zip ys)).lookup x = m.lookup x := by
  have h : x ∉ (zs.zip ys).map Prod.fst := by
    intro hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact hx (List.of_mem_zip he).1
  exact FLOOKUP_FUPDATE_LIST_HOL_not_mem m.lookup (zs.zip ys) x h

/-- With distinct keys, the `i`-th key looks up the `i`-th value. -/
private theorem lookup_updateListEq_zip_getElem {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (zs : List α) (ys : List β) (i : Nat)
    (hd : zs.Nodup) (hlen : zs.length = ys.length) (hi : i < zs.length) :
    (m.updateListEq (zs.zip ys)).lookup (zs[i]'hi) = some (ys[i]'(by rw [← hlen]; exact hi)) := by
  change FUPDATE_LIST_HOL m.lookup (zs.zip ys) (zs[i]'hi) = _
  rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  exact updateEqZipFlookupHOL zs ys m.lookup i hd hlen hi

/-- Exact HOL `update_list_locals_not_vars_eval_eq`
    (`crep_inlineProofScript.sml:2586-2589`):
    `∀vs s res e vals. (!x. MEM x vs ⇒ ¬MEM x (var_cexp e)) ∧ eval s e = res ∧
      LENGTH vs = LENGTH vals ⇒
      eval (s with locals := s.locals |++ ZIP (vs, vals)) e = res`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "update_list_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem updateListLocalsNotVarsEvalEq {width : Nat} [NeZero width] {σ : Type} :
    ∀ (vs : List Nat) (s : CrepSemHOLState width σ) (res : Option (HolWordLab width))
      (e : CrepExpHOL width) (vals : List (HolWordLab width)),
      (∀ x, x ∈ vs → x ∉ crepExpVarsHOL e) ∧ evalCrepSemHOLExp s e = res ∧
        vs.length = vals.length →
      evalCrepSemHOLExp { s with locals := s.locals.updateListEq (vs.zip vals) } e = res := by
  intro vs s res e vals ⟨hx, he, _⟩
  rw [← he]
  exact evalCrepSemHOLExp_updateLocalsList_eq_of_not_vars s
    (fun a => Classical.propDecidable (s.memaddrs a)) e (vs.zip vals)
    (fun entry hm => hx entry.1 (List.of_mem_zip hm).1)

/-- Exact HOL `opt_mmap_update_list_locals_not_vars_eval_eq`
    (`crep_inlineProofScript.sml:2601-2604`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml"
  "opt_mmap_update_list_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem optMmapUpdateListLocalsNotVarsEvalEq {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (vs : List Nat) (vals : List (HolWordLab width))
      (s : CrepSemHOLState width σ) (res : Option (List (HolWordLab width))),
      (∀ x, x ∈ vs → x ∉ (es.map crepExpVarsHOL).flatten) ∧
        es.mapM (evalCrepSemHOLExp s) = res ∧ vs.length = vals.length →
      es.mapM (evalCrepSemHOLExp { s with locals := s.locals.updateListEq (vs.zip vals) }) =
        res := by
  intro es
  induction es with
  | nil =>
    intro vs vals s res ⟨_, h, _⟩
    simpa using h
  | cons e es ih =>
    intro vs vals s res ⟨hx, h, hlen⟩
    rw [← h]
    simp only [List.mapM_cons]
    have hx1 : ∀ x, x ∈ vs → x ∉ crepExpVarsHOL e := fun x hm hc =>
      hx x hm (by simp [hc])
    have hx2 : ∀ x, x ∈ vs → x ∉ (es.map crepExpVarsHOL).flatten := fun x hm hc =>
      hx x hm (by simp only [List.map_cons, List.flatten_cons, List.mem_append]; exact Or.inr hc)
    rw [updateListLocalsNotVarsEvalEq vs s _ e vals ⟨hx1, rfl, hlen⟩,
      ih vs vals s _ ⟨hx2, rfl, hlen⟩]

/-- Exact HOL `opt_mmap_update_list_locals_not_vars_eval_eq'`
    (`crep_inlineProofScript.sml:2611-2614`).  HOL's binder `ws` is unused
    and of an unconstrained type, so it is a binder of an arbitrary type `δ`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml"
  "opt_mmap_update_list_locals_not_vars_eval_eq'"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem optMmapUpdateListLocalsNotVarsEvalEq' {width : Nat} [NeZero width] {σ δ : Type} :
    ∀ (es : List (CrepExpHOL width)) (vs : List Nat) (_ws : δ) (vals : List (HolWordLab width))
      (s : CrepSemHOLState width σ) (locs : HolFiniteMapExact Nat (HolWordLab width)),
      (∀ x, x ∈ vs → x ∉ (es.map crepExpVarsHOL).flatten) ∧ vs.length = vals.length →
      es.mapM (evalCrepSemHOLExp { s with locals := locs.updateListEq (vs.zip vals) }) =
        es.mapM (evalCrepSemHOLExp { s with locals := locs }) := by
  intro es vs _ vals s locs ⟨hx, hlen⟩
  exact optMmapUpdateListLocalsNotVarsEvalEq es vs vals { s with locals := locs } _ ⟨hx, rfl, hlen⟩

/-- Exact HOL `FDIFF_fupdate_list_empty_flookup_var`
    (`crep_inlineProofScript.sml:2622-2628`, local). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FDIFF_fupdate_list_empty_flookup_var"
  (fmap_as_finite_support_relation := [fm, fm'])]
theorem fdiffFupdateListEmptyFlookupVar {α β γ : Type} [DecidableEq α] :
    ∀ (fm : HolFiniteMapExact α β) (zs : List α) (val : β) (val2 : γ)
      (fm' : HolFiniteMapExact α β) (x : α) (v : β),
      crepHolSubmap
          (holFdiff (fm.updateListEq (zs.zip (List.replicate zs.length val))).lookup
            (crepHolFdom (HolFiniteMapExact.empty.updateListEq
              (zs.zip (List.replicate zs.length val2))).lookup))
          fm'.lookup ∧
        fm.lookup x = some v ∧ x ∉ zs →
      fm'.lookup x = some v := by
  intro fm zs val val2 fm' x v ⟨hsub, hv, hx⟩
  apply hsub x v
  unfold holFdiff crepHolFdom
  rw [lookup_updateListEq_zip_not_mem _ _ _ _ hx, lookup_updateListEq_zip_not_mem _ _ _ _ hx]
  simpa [HolFiniteMapExact.empty] using hv

/-- Exact HOL `FDIFF_fupdate_list_empty_flookup`
    (`crep_inlineProofScript.sml:2639-2645`, local). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FDIFF_fupdate_list_empty_flookup"
  (fmap_as_finite_support_relation := [fm, fm'])]
theorem fdiffFupdateListEmptyFlookup {α β γ : Type} [DecidableEq α] :
    ∀ (xs : List α) (fm : HolFiniteMapExact α β) (zs : List α) (val : β) (val2 : γ)
      (fm' : HolFiniteMapExact α β) (vs : List β),
      crepHolSubmap
          (holFdiff (fm.updateListEq (zs.zip (List.replicate zs.length val))).lookup
            (crepHolFdom (HolFiniteMapExact.empty.updateListEq
              (zs.zip (List.replicate zs.length val2))).lookup))
          fm'.lookup ∧
        xs.mapM fm.lookup = some vs ∧ (∀ x, x ∈ xs → x ∉ zs) →
      xs.mapM fm'.lookup = some vs := by
  intro xs fm zs val val2 fm' vs ⟨hsub, h, hx⟩
  have hpt : ∀ x, x ∈ xs → fm'.lookup x = fm.lookup x := by
    intro x hxmem
    obtain ⟨y, hy⟩ := (OPT_MMAP_SOME_ALL (fun x => fm.lookup x) xs).mp ⟨vs, h⟩ x hxmem
    rw [fdiffFupdateListEmptyFlookupVar fm zs val val2 fm' x y ⟨hsub, hy, hx x hxmem⟩, hy]
  rw [OPT_MMAP_ALL_EQ (fun x => fm'.lookup x) (fun x => fm.lookup x) xs hpt]
  exact h

/-- Exact HOL `submap_finish_flookup` (`crep_inlineProofScript.sml:2693-2699`,
    local). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "submap_finish_flookup"
  (fmap_as_finite_support_relation := [fm, fm'])]
theorem submapFinishFlookup {α β : Type} [DecidableEq α] :
    ∀ (fm : HolFiniteMapExact α β) (q : List α) (l : List β) (fm' : HolFiniteMapExact α β)
      (ns : List α),
      (∀ x y, x ∉ q ∧ x ∉ ns ∧ fm.lookup x = some y → fm'.lookup x = some y) ∧
        (∀ x, x ∈ q → x ∉ ns) ∧ q.Nodup ∧ q.mapM fm'.lookup = some l →
      (fm.updateListEq (q.zip l)).submap
        ((ns.zip (ns.map fm.lookup)).foldl resVarEq fm') := by
  intro fm q l fm' ns ⟨hout, hdisj, hq, hl⟩ key value hlk
  have hlen : q.length = l.length := opt_mmap_length_eq q fm'.lookup l hl
  by_cases hkq : key ∈ q
  · have hkns : key ∉ ns := hdisj key hkq
    rw [flookupResVarDistinctZipEqHOL ns (ns.map fm.lookup) fm' key ⟨by simp, hkns⟩]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkq
    rw [lookup_updateListEq_zip_getElem fm q l i hq hlen hi] at hlk
    rw [opt_mmap_el q fm'.lookup l i hl hi]
    exact hlk
  · rw [lookup_updateListEq_zip_not_mem _ _ _ _ hkq] at hlk
    by_cases hkns : key ∈ ns
    · rw [flookup_res_var_is_mem_zip_eq_exact ns key fm' fm hkns]
      exact hlk
    · rw [flookupResVarDistinctZipEqHOL ns (ns.map fm.lookup) fm' key ⟨by simp, hkns⟩]
      exact hout key value ⟨hkq, hkns, hlk⟩

end CrepInlineUpdateListLocals

end Flapjack

namespace Flapjack.CrepInlineUpdateListLocals

/-- Untagged support for `SUBMAP_DIFF_LIST`, parameterized by the key
    equality used by `updateListEq`; the tagged `submapDiffListExact` below
    instantiates it with classical equality. -/
theorem submapDiffList {α β : Type} [DecidableEq α]
    (l : HolFiniteMapExact α β) (vs : List α) (vals : List β)
    (_hlen : vs.length = vals.length) (_hdist : vs.Pairwise (· ≠ ·))
    (hfresh : ∀ v ∈ vs, crepHolFdom l.lookup v = false) :
    l.submap (l.updateListEq (vs.zip vals)) := by
  intro key value hlookup
  have hnot : key ∉ vs := by
    intro hmem
    have h := hfresh key hmem
    simp [crepHolFdom, hlookup] at h
  rw [lookup_updateListEq_zip_not_mem l vs vals key hnot]
  exact hlookup

open Classical in
/-- HOL SUBMAP_DIFF_LIST: adding fresh, distinct local names preserves every
old binding. The length and distinctness premises are retained exactly even
though the lookup proof needs only freshness. Key and value types are
arbitrary as in HOL; `|++` uses classical key equality, so no public
decidability binder is exposed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_DIFF_LIST"
  (fmap_as_finite_support_relation := [l])]
theorem submapDiffListExact {α β : Type}
    (l : HolFiniteMapExact α β) (vs : List α) (vals : List β)
    (hlen : vs.length = vals.length) (hdist : vs.Pairwise (· ≠ ·))
    (hfresh : ∀ v ∈ vs, crepHolFdom l.lookup v = false) :
    l.submap (l.updateListEq (vs.zip vals)) :=
  submapDiffList l vs vals hlen hdist hfresh

end Flapjack.CrepInlineUpdateListLocals
