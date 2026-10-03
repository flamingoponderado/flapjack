import Flapjack.Pancake.Proofs.PanStructs.CompileShapeN
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL

/-!
The original pan_structs `mem_load_conversion` (`pan_structsProofScript.sml:609-677`)
and its `mem_load` list helpers (`mem_load_flds_eq`, `mem_loads_convert_helper`,
`mem_loads_EL`, `mem_loads_mem`), over the exact `memLoadHOLExact`, `convertV`,
`valueFldsOkHOLExact` and `compileShapeNHOL`.
-/

namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang

/-- Exact HOL `mem_load_flds_eq` (`pan_structsProofScript.sml:391-402`); the free
`madd memry stcs` are bound explicitly and `ZIP` is `List.zip`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_flds_eq"
  (words_as_type_indexed_bitvec)]
theorem memLoadFldsEq {width : Nat} [NeZero width] (madd : BitVec width → Prop)
    [DecidablePred madd] (memry : BitVec width → HolWordLab width) (stcs : StructContextHOLM) :
    ∀ (fld_shs : List (MlStringHOLM × ShapeHOL)) (vflds : List (MlStringHOLM × ValueHOL width))
      (x : BitVec width),
      memLoadFldsHOLExact fld_shs x madd memry stcs = some vflds →
      ∃ vs, memLoadsHOLExact (fld_shs.map Prod.snd) x madd memry stcs = some vs ∧
        vs.length = fld_shs.length ∧ vflds = (fld_shs.map Prod.fst).zip vs := by
  intro fld_shs
  induction fld_shs with
  | nil =>
    intro vflds x h
    rw [memLoadFldsHOLExact] at h
    cases h
    exact ⟨[], by rw [List.map_nil, memLoadsHOLExact], rfl, rfl⟩
  | cons fs rest ih =>
    obtain ⟨field, shape⟩ := fs
    intro vflds x h
    rw [memLoadFldsHOLExact] at h
    split at h
    · rename_i value values hv hvs
      cases h
      obtain ⟨vs, hvs', hlen, hz⟩ := ih values _ hvs
      refine ⟨value :: vs, ?_, by simp [hlen], by simp [hz]⟩
      rw [List.map_cons, memLoadsHOLExact, hv, hvs']
    · cases h

/-- Exact HOL `mem_loads_mem` (`pan_structsProofScript.sml:595-607`); the free
`madd memry stcs v` are bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_loads_mem"
  (words_as_type_indexed_bitvec)]
theorem memLoadsMem {width : Nat} [NeZero width] (madd : BitVec width → Prop)
    [DecidablePred madd] (memry : BitVec width → HolWordLab width) (stcs : StructContextHOLM)
    (v : ValueHOL width) :
    ∀ (shs : List ShapeHOL) (vs : List (ValueHOL width)) (x : BitVec width),
      memLoadsHOLExact shs x madd memry stcs = some vs ∧ v ∈ vs →
      ∃ sh y, sh ∈ shs ∧ memLoadHOLExact sh y madd memry stcs = some v := by
  intro shs
  induction shs with
  | nil =>
    rintro vs x ⟨h, hv⟩
    rw [memLoadsHOLExact] at h
    cases h
    simp at hv
  | cons sh rest ih =>
    rintro vs x ⟨h, hv⟩
    rw [memLoadsHOLExact] at h
    split at h
    · rename_i value values hval hvals
      cases h
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨sh, x, List.mem_cons_self .., hval⟩
      · obtain ⟨sh', y, hsh', hy⟩ := ih values _ ⟨hvals, hv⟩
        exact ⟨sh', y, List.mem_cons_of_mem _ hsh', hy⟩
    · cases h

/-- Exact HOL `mem_loads_EL` (`pan_structsProofScript.sml:583-593`); the free
`madd memry stcs` are bound explicitly and `EL` is the reviewed `holEl`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_loads_EL"
  (words_as_type_indexed_bitvec)]
theorem memLoadsEL {width : Nat} [NeZero width] (madd : BitVec width → Prop)
    [DecidablePred madd] (memry : BitVec width → HolWordLab width) (stcs : StructContextHOLM) :
    ∀ (shs : List ShapeHOL) (vs : List (ValueHOL width)) (x : BitVec width) (i : Nat),
      memLoadsHOLExact shs x madd memry stcs = some vs ∧ i < shs.length →
      ∃ y : BitVec width,
        memLoadHOLExact (@holEl _ ⟨.one⟩ i shs) y madd memry stcs =
          some (@holEl _ ⟨.val (.word 0)⟩ i vs) := by
  intro shs
  induction shs with
  | nil => rintro vs x i ⟨_, hi⟩; simp at hi
  | cons sh rest ih =>
    rintro vs x i ⟨h, hi⟩
    rw [memLoadsHOLExact] at h
    split at h
    · rename_i value values hval hvals
      cases h
      cases i with
      | zero => exact ⟨x, hval⟩
      | succ i =>
        obtain ⟨y, hy⟩ := ih values _ i ⟨hvals, by simpa using hi⟩
        exact ⟨y, hy⟩
    · cases h

/-- Exact HOL `mem_loads_convert_helper` (`pan_structsProofScript.sml:567-581`,
local in HOL); the free `madd memry stcs stcs2 f` are bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_loads_convert_helper"
  (words_as_type_indexed_bitvec)]
theorem memLoadsConvertHelper {width : Nat} [NeZero width] (madd : BitVec width → Prop)
    [DecidablePred madd] (memry : BitVec width → HolWordLab width)
    (stcs stcs2 : StructContextHOLM) (f : ShapeHOL → ShapeHOL) :
    ∀ (shs : List ShapeHOL) (vs : List (ValueHOL width)) (x : BitVec width),
      memLoadsHOLExact shs x madd memry stcs = some vs ∧
        (∀ sh y v, sh ∈ shs ∧ memLoadHOLExact sh y madd memry stcs = some v →
          sizeOfShapeWithContextHOL stcs2 (f sh) = sizeOfShapeWithContextHOL stcs sh ∧
            memLoadHOLExact (f sh) y madd memry stcs2 = some (convertV v)) →
      memLoadsHOLExact (shs.map f) x madd memry stcs2 = some (vs.map convertV) := by
  intro shs
  induction shs with
  | nil =>
    rintro vs x ⟨h, -⟩
    rw [memLoadsHOLExact] at h
    cases h
    rw [List.map_nil, memLoadsHOLExact]
    rfl
  | cons sh rest ih =>
    rintro vs x ⟨h, hf⟩
    rw [memLoadsHOLExact] at h
    split at h
    · rename_i value values hval hvals
      cases h
      obtain ⟨hsize, hload⟩ := hf sh x value ⟨List.mem_cons_self .., hval⟩
      have hrest := ih values _ ⟨hvals, fun sh' y v ⟨hm, hl⟩ =>
        hf sh' y v ⟨List.mem_cons_of_mem _ hm, hl⟩⟩
      rw [List.map_cons, memLoadsHOLExact, hload, hsize, hrest]
      rfl
    · cases h

/-- `compile_shape_n` on a shape list is `MAP (compile_shape_n sctxt n)`.
Flapjack infrastructure; no HOL original. -/
theorem compileShapesNHOL_eq_map {α : Type} (sctxt : List (MlS × List (α × ShapeHOL))) (n : Nat) :
    ∀ shs : List ShapeHOL, compileShapesNHOL sctxt n shs = shs.map (compileShapeNHOL sctxt n)
  | [] => by rw [compileShapesNHOL]; rfl
  | sh :: shs => by rw [compileShapesNHOL, compileShapesNHOL_eq_map sctxt n shs]; rfl

/-- `mem_load (Named nm)` reads the fields of the first matching struct in the
context suffix after it. Flapjack infrastructure; no HOL original. -/
theorem memLoadNamedAfindi {width : Nat} [NeZero width] (madd : BitVec width → Prop)
    [DecidablePred madd] (memry : BitVec width → HolWordLab width) (nm : MlS) (x : BitVec width) :
    ∀ (ctx : StructContextHOLM) (j : Nat) (hj : j < ctx.length), afindi nm ctx = some j →
      memLoadHOLExact (.named nm) x madd memry ctx =
        (memLoadFldsHOLExact (ctx[j]'hj).2.fields x madd memry (ctx.drop (j + 1))).map
          (fun fields => ValueHOL.nStruct (ctx[j]'hj).1 fields)
  | [], j, hj, _ => by simp at hj
  | (candidate, info) :: rest, j, hj, h => by
      rw [afindi_cons] at h
      rw [memLoadHOLExact]
      by_cases hc : nm = candidate
      · rw [if_pos hc] at h
        cases h
        simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero]
        rw [if_pos hc.symm]
        cases memLoadFldsHOLExact info.fields x madd memry rest <;> rfl
      · rw [if_neg hc] at h
        rw [if_neg (fun h' => hc h'.symm)]
        cases h' : afindi nm rest with
        | none => rw [h'] at h; cases h
        | some k =>
          rw [h'] at h
          cases h
          have hk : k < rest.length := by simpa using hj
          rw [memLoadNamedAfindi madd memry nm x rest k hk h']
          simp

/-- Field validity of zipped names and values is validity of the values.
Flapjack infrastructure; no HOL original. -/
theorem fieldsFldsOkHOLExact_zip {width : Nat} [NeZero width] (ctx : StructContextExact) :
    ∀ (names : List MlS) (vs : List (ValueHOL width)), names.length = vs.length →
      fieldsFldsOkHOLExact ctx (names.zip vs) = valuesFldsOkHOLExact ctx vs
  | [], [], _ => by rw [List.zip_nil_left, fieldsFldsOkHOLExact, valuesFldsOkHOLExact]
  | _ :: names, _ :: vs, h => by
      rw [List.zip_cons_cons, fieldsFldsOkHOLExact, valuesFldsOkHOLExact,
        fieldsFldsOkHOLExact_zip ctx names vs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Exact HOL `mem_load_conversion` (`pan_structsProofScript.sml:609-673`). The free
`madd memry str_ctxt` are bound explicitly; `struct_infos_ok` is the reviewed
`structInfosOkHOLExact`, `convert_v` is `convertV` and `v_flds_ok` is
`valueFldsOkHOLExact`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_conversion"
  (words_as_type_indexed_bitvec)]
theorem memLoadConversion {width : Nat} [NeZero width] (madd : BitVec width → Prop)
    [DecidablePred madd] (memry : BitVec width → HolWordLab width) (str_ctxt : StructContextExact) :
    ∀ (str2 : List (MlS × List (MlS × ShapeHOL))) (n : Nat) (shape : ShapeHOL) (x : BitVec width)
      (v : ValueHOL width),
      memLoadHOLExact shape x madd memry (str_ctxt.drop n) = some v ∧
        str2 = str_ctxt.map (fun entry => (entry.1, entry.2.fields)) ∧
        isWfShapeExactHOL (str_ctxt.drop n) shape = true ∧
        Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact str_ctxt →
      memLoadHOLExact (compileShapeNHOL str2 n shape) x madd memry [] = some (convertV v) ∧
        valueFldsOkHOLExact str_ctxt v = true := by
  intro str2 n shape x v ⟨hload, hs2, hwf, hok⟩
  subst hs2
  have hok' := hok
  obtain ⟨hfieldsNd, hkeys, hshapes, hsizes⟩ := hok'
  have hafindi : ∀ (nm : MlS) (m : Nat),
      afindi nm ((str_ctxt.map (fun entry => (entry.1, entry.2.fields))).drop m) =
        afindi nm (str_ctxt.drop m) := by
    intro nm m
    rw [← List.map_drop, afindi_map_eq]
    intro _ _ _; rfl
  revert x v hload hwf
  induction n, shape using compileShapeNHOL.induct
      (str_ctxt.map (fun entry => (entry.1, entry.2.fields)))
    (motive2 := fun n shs => ∀ (x : BitVec width) (vs : List (ValueHOL width)),
      memLoadsHOLExact shs x madd memry (str_ctxt.drop n) = some vs →
      isWfShapesExactHOL (str_ctxt.drop n) shs = true →
      memLoadsHOLExact (compileShapesNHOL (str_ctxt.map (fun entry => (entry.1, entry.2.fields))) n shs)
          x madd memry [] = some (vs.map convertV) ∧
        valuesFldsOkHOLExact str_ctxt vs = true) with
  | case1 n =>
    intro x v hload _
    rw [memLoadHOLExact] at hload
    rw [compileShapeNHOL, memLoadHOLExact]
    split at hload
    · rename_i hx
      cases hload
      rw [if_pos hx]
      exact ⟨by rw [convertV], by rw [valueFldsOkHOLExact]⟩
    · cases hload
  | case2 n shs ih =>
    intro x v hload hwf
    rw [memLoadHOLExact] at hload
    split at hload
    · rename_i vs hvs
      cases hload
      obtain ⟨hc, hflds⟩ := ih x vs hvs (by simpa [isWfShapeExactHOL] using hwf)
      rw [compileShapeNHOL, memLoadHOLExact, hc]
      refine ⟨?_, by rw [valueFldsOkHOLExact]; exact hflds⟩
      rw [convertV]
    · cases hload
  | case3 n nm h =>
    intro x v hload hwf
    exfalso
    simp only [isWfShapeExactHOL, structContextLookupHOL_eq_lookup, afindi_lookup] at hwf
    rw [hafindi] at h
    simp [h] at hwf
  | case4 n nm j h hlt ih =>
    intro x v hload _
    have hj : n + j < str_ctxt.length := by simpa using hlt
    have h' : afindi nm (str_ctxt.drop n) = some j := by rw [← hafindi]; exact h
    have hjd : j < (str_ctxt.drop n).length := by simp; omega
    have hentry : (str_ctxt.drop n)[j]'hjd = str_ctxt[n + j]'hj := by simp
    have hname : (str_ctxt[n + j]'hj).1 = nm := by
      have := afindi_el_fst nm (str_ctxt.drop n) j h'
      simp only [List.getElem?_drop] at this
      rw [List.getElem?_eq_getElem hj] at this
      simpa using this
    rw [memLoadNamedAfindi madd memry nm x (str_ctxt.drop n) j hjd h', hentry] at hload
    simp only [List.drop_drop] at hload
    cases hfl : memLoadFldsHOLExact (str_ctxt[n + j]'hj).2.fields x madd memry
        (str_ctxt.drop (n + (j + 1))) with
    | none =>
      rw [hfl] at hload; cases hload
    | some fl =>
      rw [hfl] at hload
      cases hload
      obtain ⟨vs, hvs, hlen, hz⟩ :=
        memLoadFldsEq madd memry _ (str_ctxt[n + j]'hj).2.fields fl x hfl
      have hwfF : isWfShapesExactHOL (str_ctxt.drop (n + j + 1))
          ((str_ctxt[n + j]'hj).2.fields.map Prod.snd) = true :=
        hshapes (n + j) _ _ (by rw [List.getElem?_eq_getElem hj])
      have hel : @holEl _ ⟨(Flapjack.Basis.Pure.MlString.ofString "", [])⟩ (n + j)
          (str_ctxt.map (fun entry => (entry.1, entry.2.fields))) =
          ((str_ctxt[n + j]'hj).1, (str_ctxt[n + j]'hj).2.fields) := by
        rw [@holEl_eq_getElem _ ⟨(Flapjack.Basis.Pure.MlString.ofString "", [])⟩ _ _ hlt]
        simp
      rw [hel] at ih
      have hvs' : memLoadsHOLExact ((str_ctxt[n + j]'hj).2.fields.map Prod.snd) x madd memry
          (str_ctxt.drop (n + j + 1)) = some vs := by
        have : n + j + 1 = n + (j + 1) := by omega
        rw [this]; exact hvs
      obtain ⟨hc, hflds⟩ := ih x vs hvs' hwfF
      rw [compileShapeNHOL]
      split
      · rename_i h''; rw [h] at h''; cases h''
      · rename_i j' h''
        rw [h] at h''
        cases h''
        dsimp only
        rw [hel, memLoadHOLExact, hc]
        have hlookup : structContextLookupHOL nm str_ctxt = some (str_ctxt[n + j]'hj).2 := by
          rw [structContextLookupHOL_eq_lookup]
          apply lookup_of_mem_nodup nm _ str_ctxt hkeys
          rw [← hname]
          exact List.getElem_mem hj
        have hlenN : ((str_ctxt[n + j]'hj).2.fields.map Prod.fst).length = vs.length := by
          simp [hlen]
        have hsnd : ((((str_ctxt[n + j]'hj).2.fields.map Prod.fst).zip vs).map Prod.snd) = vs := by
          rw [List.map_snd_zip]; omega
        have hfst : ((((str_ctxt[n + j]'hj).2.fields.map Prod.fst).zip vs).map Prod.fst) =
            (str_ctxt[n + j]'hj).2.fields.map Prod.fst := by
          rw [List.map_fst_zip]; omega
        have hshape := (memLoadHOLExact_shape_eq (width := width)).2.1 _ x madd memry _ vs hvs
        subst hz
        refine ⟨?_, ?_⟩
        · have e : (((str_ctxt[n + j]'hj).2.fields.map Prod.fst).zip vs).map
              (fun pair => convertV pair.2) = vs.map convertV := by
            calc _ = ((((str_ctxt[n + j]'hj).2.fields.map Prod.fst).zip vs).map Prod.snd).map
                  convertV := by simp [List.map_map, Function.comp_def]
              _ = vs.map convertV := by rw [hsnd]
          rw [convertV, e]
        · rw [valueFldsOkHOLExact, fieldsFldsOkHOLExact_zip _ _ _ hlenN, hflds, hname, hlookup]
          have hshapes' : ((((str_ctxt[n + j]'hj).2.fields.map Prod.fst).zip vs).map
              (fun field => shapeOfHOLExact field.2)) =
              (str_ctxt[n + j]'hj).2.fields.map Prod.snd := by
            calc _ = ((((str_ctxt[n + j]'hj).2.fields.map Prod.fst).zip vs).map Prod.snd).map
                  shapeOfHOLExact := by simp [List.map_map, Function.comp_def]
              _ = vs.map shapeOfHOLExact := by rw [hsnd]
              _ = _ := hshape
          simp only [hfst, hshapes', beq_self_eq_true, Bool.true_and,
            (shapeEqListHOL_eq_true _ _).mpr rfl]
  | case5 n x vs hload _ =>
    rw [memLoadsHOLExact] at hload
    cases hload
    rw [compileShapesNHOL, memLoadsHOLExact]
    exact ⟨rfl, by rw [valuesFldsOkHOLExact]⟩
  | case6 n sh shs ih1 ih2 x vs hload hwf =>
    simp only [isWfShapesExactHOL, Bool.and_eq_true] at hwf
    rw [memLoadsHOLExact] at hload
    split at hload
    · rename_i value values hval hvals
      cases hload
      obtain ⟨hc1, hf1⟩ := ih1 x value hval hwf.1
      have hsize : sizeOfShapeWithContextHOL []
          (compileShapeNHOL (str_ctxt.map (fun entry => (entry.1, entry.2.fields))) n sh) =
          sizeOfShapeWithContextHOL (str_ctxt.drop n) sh := by
        rw [sizeOfCompileShapeN str_ctxt _ n sh ⟨rfl, hwf.1, hok⟩,
          sizeOfShapeWithContextHOL_drop str_ctxt sh n hwf.1 hkeys]
      obtain ⟨hc2, hf2⟩ := ih2 _ values hvals hwf.2
      rw [compileShapesNHOL, memLoadsHOLExact, hc1, hsize, hc2]
      exact ⟨rfl, by rw [valuesFldsOkHOLExact, hf1, hf2]; rfl⟩
    · cases hload

/-- Exact HOL `mem_load_conversion_inst` (`pan_structsProofScript.sml:675-677`,
local in HOL): `mem_load_conversion` at `n = 0`, simplified with
`compile_shape_n_eq`. The elaborated statement (free `madd memry str_ctxt`) is
reproduced by `pan_structs_mem_load_probe`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_conversion_inst"
  (words_as_type_indexed_bitvec)]
theorem memLoadConversionInst {width : Nat} [NeZero width] (madd : BitVec width → Prop)
    [DecidablePred madd] (memry : BitVec width → HolWordLab width) (str_ctxt : StructContextExact) :
    ∀ (shape : ShapeHOL) (x : BitVec width) (v : ValueHOL width),
      memLoadHOLExact shape x madd memry str_ctxt = some v ∧
        isWfShapeExactHOL str_ctxt shape = true ∧
        Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact str_ctxt →
      memLoadHOLExact (compileShapeExact (str_ctxt.map (fun entry => (entry.1, entry.2.fields)))
          shape) x madd memry [] = some (convertV v) ∧
        valueFldsOkHOLExact str_ctxt v = true := by
  rintro shape x v ⟨hload, hwf, hok⟩
  have h := memLoadConversion madd memry str_ctxt _ 0 shape x v
    ⟨by simpa using hload, rfl, by simpa using hwf, hok⟩
  rw [compileShapeNEq, List.drop_zero] at h
  exact h

end Flapjack.Pancake.PanStructs.CompileShapeExact
