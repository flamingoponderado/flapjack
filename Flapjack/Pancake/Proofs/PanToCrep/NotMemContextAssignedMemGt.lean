import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.PanToCrep.CompileExact

/-!
# `not_mem_context_assigned_mem_gt` over the exact compiler

Exact port of HOL `not_mem_context_assigned_mem_gt`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1252-1440`): a slot at most
`ctxt.vmax` that no context variable owns is never assigned by
`compile ctxt p`. `compile` is the tagged `compileProgExactHOLW`,
`assigned_free_vars` is the tagged `crepAssignedFreeVarsHOL`, and `ctxt_max` is
`ctxtMaxFiniteExact` over the exact `PanToCrepContextExact.vars` map.

The proof goes through a stronger invariant, proved by recursion on the
program (HOL uses `compile_ind`): every assigned free variable of
`compile ctxt p` is a slot of some context variable or lies above `ctxt.vmax`.
The DecCall case of `pc_compile_correct` uses the theorem to show that caller
slots are untouched by the continuation (bead `flapjack-pxn.18.4.3.95.4`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL)

namespace NotMemContextAssignedWitnesses

/-- Same-module canonical carrier witness for the
    `fmap_as_finite_support_relation` qualifier: the roundtrip of the context
    carrier owning `vars`. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  Flapjack.holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact context

end NotMemContextAssignedWitnesses

private theorem afv_nestedSeq {width : Nat} [NeZero width] :
    ∀ (l : List (CrepProgHOL width)),
      crepAssignedFreeVarsHOL (crepNestedSeqHOL l) = l.flatMap crepAssignedFreeVarsHOL
  | [] => by simp [crepNestedSeqHOL, crepAssignedFreeVarsHOL]
  | c :: l => by
      simp only [crepNestedSeqHOL, crepAssignedFreeVarsHOL, List.flatMap_cons, afv_nestedSeq l]

private theorem afv_nestedDecs_sub {width : Nat} [NeZero width] :
    ∀ (names : List Nat) (values : List (CrepExpHOL width)) (body : CrepProgHOL width) (x : Nat),
      x ∈ crepAssignedFreeVarsHOL (nestedDecsHOL names values body) →
      x ∈ crepAssignedFreeVarsHOL body
  | [], [], body, x, h => by simpa [nestedDecsHOL] using h
  | [], _ :: _, body, x, h => by simp [nestedDecsHOL, crepAssignedFreeVarsHOL] at h
  | _ :: _, [], body, x, h => by simp [nestedDecsHOL, crepAssignedFreeVarsHOL] at h
  | n :: names, v :: values, body, x, h => by
      simp only [nestedDecsHOL, crepAssignedFreeVarsHOL, List.mem_filter] at h
      exact afv_nestedDecs_sub names values body x h.1

private theorem afv_panMap2_assign {width : Nat} [NeZero width] :
    ∀ (ns : List Nat) (es : List (CrepExpHOL width)) (x : Nat),
      x ∈ (panMap2 (fun d s => CrepProgHOL.assign d s) ns es).flatMap crepAssignedFreeVarsHOL →
      x ∈ ns
  | [], _, x, h => by simp [panMap2] at h
  | _ :: _, [], x, h => by simp [panMap2] at h
  | n :: ns, e :: es, x, h => by
      simp only [panMap2, List.flatMap_cons, crepAssignedFreeVarsHOL, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | h
      · simp [h]
      · exact List.mem_cons_of_mem _ (afv_panMap2_assign ns es x h)

private theorem afv_zipWith_assign {width : Nat} [NeZero width] :
    ∀ (ns : List Nat) (es : List (CrepExpHOL width)) (x : Nat),
      x ∈ (List.zipWith CrepProgHOL.assign ns es).flatMap crepAssignedFreeVarsHOL → x ∈ ns
  | [], _, x, h => by simp at h
  | _ :: _, [], x, h => by simp at h
  | n :: ns, e :: es, x, h => by
      simp only [List.zipWith_cons_cons, List.flatMap_cons, crepAssignedFreeVarsHOL,
        List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · simp [h]
      · exact List.mem_cons_of_mem _ (afv_zipWith_assign ns es x h)

private theorem afv_stores {width : Nat} [NeZero width] :
    ∀ (a : CrepExpHOL width) (vs : List (CrepExpHOL width)) (off : BitVec width),
      (storesHOL a vs off).flatMap crepAssignedFreeVarsHOL = []
  | a, [], off => by simp [storesHOL]
  | a, v :: vs, off => by
      simp only [storesHOL, List.flatMap_cons, afv_stores a vs, List.append_nil]
      simp [crepAssignedFreeVarsHOL]

private theorem afv_storeGlobals {width : Nat} [NeZero width] :
    ∀ (a : BitVec 5) (vs : List (CrepExpHOL width)),
      (storeGlobalsHOL a vs).flatMap crepAssignedFreeVarsHOL = []
  | a, [] => by simp [storeGlobalsHOL]
  | a, v :: vs => by
      simp only [storeGlobalsHOL, List.flatMap_cons, afv_storeGlobals (a + 1) vs, List.append_nil]
      simp [crepAssignedFreeVarsHOL]

/-- Flapjack-specific invariant: `x` is a slot of some context variable or lies above `vmax`. -/
private def CompileAfvOK {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) (x : Nat) : Prop :=
  (∃ v sh ns, ctxt.vars.lookup v = some (sh, ns) ∧ x ∈ ns) ∨ ctxt.vmax < x

private theorem okOfExtend {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (name : MlS) (sh : ShapeHOL) (names : List Nat) (vmax' : Nat) (x : Nat)
    (hnames : ∀ y, y ∈ names → ctxt.vmax < y) (hle : ctxt.vmax ≤ vmax')
    (h : CompileAfvOK { ctxt with vars := ctxt.vars.update (name, (sh, names)), vmax := vmax' } x) :
    CompileAfvOK ctxt x := by
  rcases h with ⟨v, sh', ns, hl, hx⟩ | h
  · simp only [HolFiniteMapExact.lookup_update, FUPDATE] at hl
    split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl
      rw [← hl.2] at hx
      exact Or.inr (hnames x hx)
    · exact Or.inl ⟨v, sh', ns, hl, hx⟩
  · exact Or.inr (by simp only at h; omega)

private theorem mem_vmaxNames {n vmax x : Nat}
    (h : x ∈ (List.range n).map (fun i => vmax + i + 1)) : vmax < x := by
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, _, rfl⟩ := h
  omega

private theorem afv_expHdl {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (evar : MlS) (x : Nat)
    (h : x ∈ crepAssignedFreeVarsHOL (expHdlExact (width := width) ctxt.vars evar)) :
    CompileAfvOK ctxt x := by
  unfold expHdlExact at h
  split at h
  · simp [crepAssignedFreeVarsHOL] at h
  · rename_i sh names hl
    rw [afv_nestedSeq] at h
    exact Or.inl ⟨evar, sh, names, hl, afv_panMap2_assign _ _ x h⟩

private theorem wrapRtHOL_some {o : Option (ShapeHOL × List Nat)} {sh : ShapeHOL}
    {ns : List Nat} (h : wrapRtHOL o = some (sh, ns)) : o = some (sh, ns) := by
  unfold wrapRtHOL at h
  split at h <;> simp_all

private theorem mem_retNames {vmax x : Nat} {rs : Option ShapeHOL}
    (h : x ∈ (match rs with
      | none => []
      | some shape => (List.range (sizeOfShapeHOL shape)).map (fun i => vmax + i + 1))) :
    vmax < x := by
  split at h
  · simp at h
  · exact mem_vmaxNames h

/-- Every assigned free variable of `compile ctxt p` satisfies `CompileAfvOK ctxt`. -/
private theorem compileAfvOK {width : Nat} [NeZero width] :
    ∀ (p : ProgHOL width) (ctxt : PanToCrepContextExact width) (x : Nat),
      x ∈ crepAssignedFreeVarsHOL (compileProgExactHOLW ctxt p) → CompileAfvOK ctxt x
  | .skip, ctxt, x, h => by simp [compileProgExactHOLW, crepAssignedFreeVarsHOL] at h
  | .break, ctxt, x, h => by simp [compileProgExactHOLW, crepAssignedFreeVarsHOL] at h
  | .continue, ctxt, x, h => by simp [compileProgExactHOLW, crepAssignedFreeVarsHOL] at h
  | .tick, ctxt, x, h => by simp [compileProgExactHOLW, crepAssignedFreeVarsHOL] at h
  | .annot _ _, ctxt, x, h => by simp [compileProgExactHOLW, crepAssignedFreeVarsHOL] at h
  | .seq p1 p2, ctxt, x, h => by
      simp only [compileProgExactHOLW, crepAssignedFreeVarsHOL, List.mem_append] at h
      rcases h with h | h
      · exact compileAfvOK p1 ctxt x h
      · exact compileAfvOK p2 ctxt x h
  | .dec name shape e body, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileDecExactHOLW] at h
      rcases hc : compileExpExactHOLW ctxt e with ⟨values, cs⟩
      rw [hc] at h
      dsimp only at h
      split at h
      · simp [crepAssignedFreeVarsHOL] at h
      · have h' := afv_nestedDecs_sub _ _ _ x h
        exact okOfExtend ctxt name cs _ _ x (fun y hy => mem_vmaxNames hy) (by omega)
          (compileAfvOK body _ x h')
  | .assign .global name e, ctxt, x, h => by
      simp [compileProgExactHOLW, compileGlobalAssignExactHOLW, crepAssignedFreeVarsHOL] at h
  | .assign .local name e, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileLocalAssignExactHOLW] at h
      rcases hc : compileExpExactHOLW ctxt e with ⟨exprs, sh0⟩
      rw [hc] at h
      dsimp only at h
      split at h
      · simp [crepAssignedFreeVarsHOL] at h
      · rename_i sh names hl
        split at h
        · simp [crepAssignedFreeVarsHOL] at h
        · split at h
          · rw [afv_nestedSeq] at h
            exact Or.inl ⟨name, sh, names, hl, afv_zipWith_assign _ _ x h⟩
          · have h' := afv_nestedDecs_sub _ _ _ x h
            rw [afv_nestedSeq] at h'
            exact Or.inl ⟨name, sh, names, hl, afv_zipWith_assign _ _ x h'⟩
  | .primitive name op args, ctxt, x, h => by
      simp only [compileProgExactHOLW, compilePrimitiveExactHOLW] at h
      split at h
      · simp [crepAssignedFreeVarsHOL] at h
      · rename_i sh names hl
        have h' := afv_nestedDecs_sub _ _ _ x h
        simp only [crepAssignedFreeVarsHOL] at h'
        exact Or.inl ⟨name, sh, names, hl, h'⟩
  | .store a v, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileStoreExactHOLW] at h
      split at h
      · rcases hc : compileExpExactHOLW ctxt v with ⟨values, sh⟩
        rw [hc] at h
        dsimp only at h
        split at h
        · simp [crepAssignedFreeVarsHOL] at h
        · have h' := afv_nestedDecs_sub _ _ _ x h
          rw [afv_nestedSeq, afv_stores] at h'
          simp at h'
      · simp [crepAssignedFreeVarsHOL] at h
  | .store32 a v, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileStore32ExactHOLW] at h
      split at h <;> simp [crepAssignedFreeVarsHOL] at h
  | .storeByte a v, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileStoreByteExactHOLW] at h
      split at h <;> simp [crepAssignedFreeVarsHOL] at h
  | .ite c t e, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileIfExactHOLW] at h
      split at h
      · simp only [crepAssignedFreeVarsHOL, List.mem_append] at h
        rcases h with h | h
        · exact compileAfvOK t ctxt x h
        · exact compileAfvOK e ctxt x h
      · simp [crepAssignedFreeVarsHOL] at h
  | .while c body, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileWhileExactHOLW] at h
      split at h
      · simp only [crepAssignedFreeVarsHOL] at h
        exact compileAfvOK body ctxt x h
      · simp [crepAssignedFreeVarsHOL] at h
  | .decCall name shape f args body, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileDecCallExactHOLW] at h
      have h' := afv_nestedDecs_sub _ _ _ x h
      simp only [crepAssignedFreeVarsHOL, List.mem_append] at h'
      rcases h' with h' | h'
      · exact Or.inr (mem_vmaxNames h')
      · exact okOfExtend ctxt name shape _ _ x (fun y hy => mem_vmaxNames hy) (by omega)
          (compileAfvOK body _ x h')
  | .extCall f c cl a al, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileExtCallExactHOLW] at h
      split at h <;> simp [crepAssignedFreeVarsHOL] at h
  | .raise eid e, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileRaiseExactHOLW] at h
      split at h
      · simp [crepAssignedFreeVarsHOL] at h
      · rcases hc : compileExpExactHOLW ctxt e with ⟨values, sh⟩
        rw [hc] at h
        dsimp only at h
        split at h
        · simp [crepAssignedFreeVarsHOL] at h
        · simp only [crepAssignedFreeVarsHOL, List.append_nil] at h
          have h' := afv_nestedDecs_sub _ _ _ x h
          rw [afv_nestedSeq, afv_storeGlobals] at h'
          simp at h'
  | .return e, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileReturnExactHOLW] at h
      split at h <;> simp [crepAssignedFreeVarsHOL] at h
  | .shMemLoad op .global name a, ctxt, x, h => by
      simp [compileProgExactHOLW, compileGlobalShMemLoadExactHOLW, crepAssignedFreeVarsHOL] at h
  | .shMemLoad op .local name a, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileShMemLoadExactHOLW] at h
      split at h
      · split at h
        · rename_i sh d ds hl
          simp only [crepAssignedFreeVarsHOL, List.mem_singleton] at h
          exact Or.inl ⟨name, sh, d :: ds, hl, by simp [h]⟩
        · simp [crepAssignedFreeVarsHOL] at h
      · simp [crepAssignedFreeVarsHOL] at h
  | .shMemStore op a v, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileShMemStoreExactHOLW] at h
      split at h <;> simp [crepAssignedFreeVarsHOL] at h
  | .call none f args, ctxt, x, h => by
      simp [compileProgExactHOLW, compileCallNoReturnExactHOLW, crepAssignedFreeVarsHOL] at h
  | .call (some (none, none)) f args, ctxt, x, h => by
      simp only [compileProgExactHOLW, compileCallResultNoHandlerExactHOLW] at h
      have h' := afv_nestedDecs_sub _ _ _ x h
      simp only [crepAssignedFreeVarsHOL] at h'
      exact Or.inr (mem_retNames h')
  | .call (some (none, some (en, ev, body))) f args, ctxt, x, h => by
      simp only [compileProgExactHOLW] at h
      split at h
      · simp only [compileCallHandlerMissingEidExactHOLW,
          compileCallResultNoHandlerExactHOLW] at h
        have h' := afv_nestedDecs_sub _ _ _ x h
        simp only [crepAssignedFreeVarsHOL] at h'
        exact Or.inr (mem_retNames h')
      · simp only [compileCallHandlerPresentEidExactHOLW] at h
        have h' := afv_nestedDecs_sub _ _ _ x h
        simp only [crepAssignedFreeVarsHOL, List.mem_append] at h'
        rcases h' with h' | h' | h'
        · exact Or.inr (mem_retNames h')
        · exact afv_expHdl ctxt ev x h'
        · exact compileAfvOK body ctxt x h'
  | .call (some (some (k, rn), none)) f args, ctxt, x, h => by
      simp only [compileProgExactHOLW] at h
      split at h
      · simp [compileCallWrappedResultFallbackNoHandlerExactHOLW,
          crepAssignedFreeVarsHOL] at h
      · rename_i sh ns hw
        simp only [compileCallWrappedResultNoHandlerExactHOLW, crepAssignedFreeVarsHOL] at h
        exact Or.inl ⟨rn, sh, ns, wrapRtHOL_some hw, h⟩
  | .call (some (some (k, rn), some (en, ev, body))) f args, ctxt, x, h => by
      simp only [compileProgExactHOLW] at h
      split at h
      · split at h
        · simp [compileCallWrappedResultFallbackHandlerMissingEidExactHOLW,
            compileCallWrappedResultFallbackNoHandlerExactHOLW, crepAssignedFreeVarsHOL] at h
        · simp only [compileCallWrappedResultFallbackHandlerPresentEidExactHOLW,
            crepAssignedFreeVarsHOL, List.nil_append, List.mem_append] at h
          rcases h with h | h
          · exact afv_expHdl ctxt ev x h
          · exact compileAfvOK body ctxt x h
      · rename_i sh ns hw
        split at h
        · simp only [compileCallWrappedResultHandlerMissingEidExactHOLW,
            compileCallWrappedResultNoHandlerExactHOLW, crepAssignedFreeVarsHOL] at h
          exact Or.inl ⟨rn, sh, ns, wrapRtHOL_some hw, h⟩
        · simp only [compileCallWrappedResultHandlerPresentEidExactHOLW,
            crepAssignedFreeVarsHOL, List.mem_append] at h
          rcases h with h | h | h
          · exact Or.inl ⟨rn, sh, ns, wrapRtHOL_some hw, h⟩
          · exact afv_expHdl ctxt ev x h
          · exact compileAfvOK body ctxt x h
termination_by p => sizeOf p

/-- Exact port of HOL `not_mem_context_assigned_mem_gt`
    (`pan_to_crepProofScript.sml:1252-1257`): `!ctxt p x.
    ctxt_max ctxt.vmax ctxt.vars /\
    (!v sh ns'. FLOOKUP ctxt.vars v = SOME (sh, ns') ==> ~MEM x ns') /\
    x <= ctxt.vmax ==> ~MEM x (assigned_free_vars (compile ctxt p))`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "not_mem_context_assigned_mem_gt"
  (fmap_as_finite_support_relation := [PanToCrepContextExact.vars])
  (words_as_type_indexed_bitvec)]
theorem notMemContextAssignedMemGtHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanToCrepContextExact width) (p : ProgHOL width) (x : Nat),
      ctxtMaxFiniteExact ctxt.vmax ctxt.vars ∧
        (∀ v sh ns', ctxt.vars.lookup v = some (sh, ns') → x ∉ ns') ∧
        x ≤ ctxt.vmax →
      x ∉ crepAssignedFreeVarsHOL (compileProgExactHOLW ctxt p) := by
  intro ctxt p x ⟨_, hnot, hle⟩ hmem
  rcases compileAfvOK p ctxt x hmem with ⟨v, sh, ns, hl, hx⟩ | hgt
  · exact hnot v sh ns hl hx
  · omega

end Flapjack
