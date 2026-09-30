import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Assembly
import Flapjack.Pancake.Proofs.CrepInline.TransformBranch.Assembly

/-!
# crep_inline `wrapped_transform_if` and `var_prog` lemmas

Counterparts of `cakeml/pancake/proofs/crep_inlineProofScript.sml:2168-2273`
(bead `flapjack-pxn.18.5.5.47.4`): `cont_res` over the exact result carrier,
`wrapped_transform_if` (from `transform_eoc_correct` and
`transform_branch_correct`), and the `var_prog` inclusions
`mem_var_prog_nested_seq`, `mem_var_prog_transform_eoc` and
`mem_var_prog_transform_branch` (`MEM_MAP2_IMP` is already ported as
`panMap2_mem`).
-/

namespace Flapjack

namespace CrepInlineWrappedTransformIf

open HolFiniteMapExact
open CrepInlineExact

/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Exact HOL `cont_res_def` (`crep_inlineProofScript.sml:2168-2171`) over the
    width-indexed exact result carrier `CrepResultHOLExact` of the exact Crep
    evaluator (the existing `contResHOL` is over the production
    `CrepResultHOL`).  Five clauses: `NONE`, `Break`, `Continue`, `Error` are
    `T`; everything else `F`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "cont_res_def"
  (words_as_type_indexed_bitvec)]
def contResHOLExact {width : Nat} [NeZero width] : Option (CrepResultHOLExact width) → Bool
  | none => true
  | some (.break _) => true
  | some (.continue _) => true
  | some .error => true
  | _ => false

/-- Local support: `1w ≠ 0w` at a positive word width. -/
private theorem one_ne_zero {width : Nat} [NeZero width] : (1 : BitVec width) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  have hw := NeZero.ne width
  have hlt : 1 < 2 ^ width := Nat.one_lt_two_pow hw
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this

/-- Exact HOL `wrapped_transform_if` (`crep_inlineProofScript.sml:2188-2224`).
    `Const 1w` is `.const 1`; HOL's `if not_branch_ret p then ...` is the
    Boolean test of the tagged `notBranchRetHOLExact`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "wrapped_transform_if"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem wrappedTransformIf {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat)
      (loc : HolFiniteMapExact Nat (HolWordLab width)),
      evalCrepSemHOLProgExact { decClockCrepSemHOL s with locals := loc } p = (r, s') ∧
        unreachElimHOLExact p = (p, res) ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact p) ∧
        (∃ z, rts.mapM loc.lookup = some z) ∧
        rts.Nodup ∧
        contResHOLExact r = false ∧
        s.clock ≠ 0 ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact { s with locals := loc }
          (if notBranchRetHOLExact p then .seq .tick (transformEocHOLExact rts p)
           else .while (.const 1) (transformBranchHOLExact 0 rts p)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some (.exception eid) => r1 = some (.exception eid)
        | some .timeOut => r1 = some .timeOut
        | some (.finalFfi ffi) => r1 = some (.finalFfi ffi)
        | _ => False := by
  intro p s r s' res rts loc ⟨hev, hue, hlen, hfresh, hz, hnd, hcont, hc, hne⟩
  have hdec : decClockCrepSemHOL { s with locals := loc } =
      { decClockCrepSemHOL s with locals := loc } := rfl
  by_cases hnb : notBranchRetHOLExact p = true
  · rw [if_pos hnb]
    obtain ⟨r1, s1, hev1, hrel1, hpost1⟩ :=
      CrepInlineTransformEoc.transformEocCorrect p { decClockCrepSemHOL s with locals := loc }
        r s' res rts ⟨hev, hue, hnb, hlen, hfresh, hz, hnd, hne⟩
    refine ⟨r1, s1, ?_, hrel1, ?_⟩
    · rw [evalCrepSemHOLProgExact_seq_fixClockFree, evalCrepSemHOLProgExact_tick,
        if_neg hc]
      dsimp only
      rw [hdec, hev1]
    · rcases r with _ | ⟨_ | _ | n | n | vs | ex | ev⟩ <;>
        simp_all [contResHOLExact]
  · rw [if_neg hnb]
    obtain ⟨r1, s1, hev1, hrel1, hpost1⟩ :=
      CrepInlineTransformBranch.transformBranchCorrect p { decClockCrepSemHOL s with locals := loc }
        r s' 0 rts ⟨hev, hlen, hfresh, hz, hnd, hne⟩
    rw [evalCrepSemHOLProgExact_while_holShape]
    have hconst : evalCrepSemHOLExp { s with locals := loc } (.const (1 : BitVec width)) =
        some (.word 1) := by
      simp [evalCrepSemHOLExp]
    rw [hconst]
    dsimp only
    rw [if_pos one_ne_zero, if_neg hc, hdec, hev1]
    dsimp only
    rcases r with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
    · simp [contResHOLExact] at hcont
    · exact absurd rfl hne
    · obtain ⟨rfl⟩ := hpost1
      exact ⟨_, _, rfl, hrel1, rfl⟩
    · simp [contResHOLExact] at hcont
    · simp [contResHOLExact] at hcont
    · obtain ⟨rfl, hl⟩ := hpost1
      exact ⟨_, _, rfl, hrel1, rfl, hl⟩
    · obtain ⟨rfl⟩ := hpost1
      exact ⟨_, _, rfl, hrel1, rfl⟩
    · obtain ⟨rfl⟩ := hpost1
      exact ⟨_, _, rfl, hrel1, rfl⟩

/-- Exact HOL `mem_var_prog_nested_seq` (`crep_inlineProofScript.sml:2226-2231`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "mem_var_prog_nested_seq"
  (words_as_type_indexed_bitvec)]
theorem memVarProgNestedSeq {width : Nat} [NeZero width] :
    ∀ (ps : List (CrepProgHOL width)) (x : Nat),
      (x ∈ crepVarProgHOLExact (crepNestedSeqHOL ps)) = (x ∈ (ps.map crepVarProgHOLExact).flatten)
  | [], x => by simp [crepNestedSeqHOL, crepVarProgHOLExact]
  | p :: ps, x => by
      simp [crepNestedSeqHOL, crepVarProgHOLExact, memVarProgNestedSeq ps x]

/-- Local support: the `Return` clause of both transformations. -/
private theorem mem_var_prog_zip_assign {width : Nat} [NeZero width] (rts : List Nat)
    (es : List (CrepExpHOL width)) (x : Nat)
    (h : x ∈ crepVarProgHOLExact (crepNestedSeqHOL
      (rts.zipWith (fun name value => CrepProgHOL.assign name value) es))) :
    x ∈ es.flatMap crepExpVarsHOL ∨ x ∈ rts := by
  rw [memVarProgNestedSeq] at h
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hl
  rw [← CrepInlineTransformEoc.panMap2_eq_zipWith] at hq
  obtain ⟨y1, y2, rfl, h1, h2⟩ := panMap2_mem hq
  simp only [crepVarProgHOLExact, List.mem_append, List.mem_singleton] at hx
  rcases hx with rfl | hx
  · exact Or.inr h1
  · exact Or.inl (List.mem_flatMap.2 ⟨y2, h2, hx⟩)

/-- Exact HOL `mem_var_prog_transform_eoc` (`crep_inlineProofScript.sml:2241-2256`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "mem_var_prog_transform_eoc"
  (words_as_type_indexed_bitvec)]
theorem memVarProgTransformEoc {width : Nat} [NeZero width] :
    ∀ (rts : List Nat) (p : CrepProgHOL width) (x : Nat),
      x ∈ crepVarProgHOLExact (transformEocHOLExact rts p) →
        x ∈ crepVarProgHOLExact p ∨ x ∈ rts := by
  intro rts p
  induction p using transformEocHOLExact.induct <;> intro x hx <;>
    simp only [transformEocHOLExact] at hx
  all_goals first
    | exact Or.inl hx
    | (have := mem_var_prog_zip_assign rts _ x hx
       simpa [crepVarProgHOLExact] using this)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih1 ih2
       rcases hx with (hx | hx) | hx
       · exact Or.inl (Or.inl (Or.inl hx))
       · rcases ih1 x hx with h | h <;> simp_all
       · rcases ih2 x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih
       rcases hx with (hx | hx) | hx
       · exact Or.inl (Or.inl (Or.inl hx))
       · exact Or.inl (Or.inl (Or.inr hx))
       · rcases ih x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih1 ih2
       rcases hx with hx | hx
       · rcases ih1 x hx with h | h <;> simp_all
       · rcases ih2 x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih
       rcases hx with hx | hx
       · exact Or.inl (Or.inl hx)
       · rcases ih x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih
       rcases hx with (hx | hx) | hx
       · exact Or.inl (Or.inl (Or.inl hx))
       · exact Or.inl (Or.inl (Or.inr hx))
       · rcases ih x hx with h | h <;> simp_all)

/-- Exact HOL `mem_var_prog_transform_branch` (`crep_inlineProofScript.sml:2258-2273`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "mem_var_prog_transform_branch"
  (words_as_type_indexed_bitvec)]
theorem memVarProgTransformBranch {width : Nat} [NeZero width] :
    ∀ (ld : Nat) (rts : List Nat) (p : CrepProgHOL width) (x : Nat),
      x ∈ crepVarProgHOLExact (transformBranchHOLExact ld rts p) →
        x ∈ crepVarProgHOLExact p ∨ x ∈ rts := by
  intro ld rts p
  induction ld, p using transformBranchHOLExact.induct <;> intro x hx <;>
    simp only [transformBranchHOLExact] at hx
  all_goals first
    | exact Or.inl hx
    | (have := mem_var_prog_zip_assign rts _ x hx
       simpa [crepVarProgHOLExact] using this)
    | (simp only [crepVarProgHOLExact, List.mem_append, List.not_mem_nil, or_false] at hx
       have := mem_var_prog_zip_assign rts _ x hx
       simpa [crepVarProgHOLExact] using this)
    | (simp only [crepVarProgHOLExact, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
       simp_all
       done)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih1 ih2
       rcases hx with (hx | hx) | hx
       · exact Or.inl (Or.inl (Or.inl hx))
       · rcases ih1 x hx with h | h <;> simp_all
       · rcases ih2 x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih
       rcases hx with (hx | hx) | hx
       · exact Or.inl (Or.inl (Or.inl hx))
       · exact Or.inl (Or.inl (Or.inr hx))
       · rcases ih x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih1 ih2
       rcases hx with hx | hx
       · rcases ih1 x hx with h | h <;> simp_all
       · rcases ih2 x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih
       rcases hx with hx | hx
       · exact Or.inl (Or.inl hx)
       · rcases ih x hx with h | h <;> simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       simp_all)
    | (simp only [crepVarProgHOLExact, List.mem_append] at hx ⊢
       rename_i ih
       rcases hx with (hx | hx) | hx
       · exact Or.inl (Or.inl (Or.inl hx))
       · exact Or.inl (Or.inl (Or.inr hx))
       · rcases ih x hx with h | h <;> simp_all)

end CrepInlineWrappedTransformIf

end Flapjack
