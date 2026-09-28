import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assign

/-!
# `pc_compile_correct` ExtCall case over the exact carriers

This module proves the ExtCall constructor conjunct in HOL's `evaluate_ind`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ProgHOL ExpHOL)

/-- Lean-only specialization of `compile_exp_val_rel` used to expose a single
    compiled word expression in the ExtCall case. HOL proves this extraction
    inline; this helper has no separate HOL declaration. -/
private theorem compileExpWord
    {width : Nat} {σ : Type} [NeZero width]
    (source : Flapjack.PanSemStateFiniteExact width σ)
    [DecidablePred source.memaddrs]
    (target : Flapjack.CrepSemHOLState width σ)
    [DecidablePred target.memaddrs]
    (ctxt : Flapjack.PanToCrepContextExact width) (e : ExpHOL width)
    (w : BitVec width)
    (heval : source.evalHOLFinite e = some (.val (.word w)))
    (hstate : Flapjack.panToCrepStateRelFiniteExact source target)
    (hcode : Flapjack.codeRelExactHOLW ctxt source.code target.code)
    (hlocals : Flapjack.panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (hloc : Flapjack.localisedExpHOL e = true) :
    ∃ ce, Flapjack.compileExpExactHOLW ctxt e = ([ce], .one) ∧
    Flapjack.evalCrepSemHOLExp target ce = some (.word w) ∧
      (∀ x, x ∈ Flapjack.crepExpVarsHOL ce → x ≤ ctxt.vmax) := by
  rcases hc : Flapjack.compileExpExactHOLW ctxt e with ⟨es, shape⟩
  have hrel := Flapjack.compileExpValRelHOL source ctxt target e
    (Flapjack.ValueHOL.val (Flapjack.HolWordLab.word w)) es shape
    heval hstate hcode hlocals hloc hc
  rcases hrel with ⟨hevalTarget, hlen, hshape, _⟩
  have hshape' : shape = .one := by
    simpa [Flapjack.shapeOfHOLExact] using hshape.symm
  have hlen' : es.length = 1 := by
    simpa [hshape'] using hlen
  cases es with
  | nil => simp at hlen'
  | cons ce rest =>
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons x xs => simp at hlen'
      subst rest
      simp only [Flapjack.flattenHOL, List.map_cons, List.map_nil, List.cons.injEq] at hevalTarget
      rcases hevalTarget with ⟨hevalTarget, _⟩
      have hevalTarget' : Flapjack.evalCrepSemHOLExp target ce =
          some (Flapjack.HolWordLab.word w) := hevalTarget
      refine ⟨ce, ?_, hevalTarget', ?_⟩
      · simp [hshape']
      · intro x hx
        have hce : x ∈ (Flapjack.compileExpExactHOLW ctxt e).1.flatMap
            Flapjack.crepExpVarsHOL := by
          rw [hc]
          simp [hx]
        obtain ⟨n, sh, slots, hlk, hslot⟩ :=
          (Flapjack.compileExpExactHOLW_vars_from_context ctxt).1 e x hce
        exact hlocals.2.1.2 n sh slots hlk x hslot

/-- Lean-only monotonicity helper for the fresh ExtCall temporary bound; HOL
    proves its corresponding `MAX_LIST` reasoning inline in the case proof. -/
private theorem extCall_foldl_max_mono (xs : List Nat) : ∀ a b, a ≤ b →
    xs.foldl (fun m n => Nat.max m n) a ≤ xs.foldl (fun m n => Nat.max m n) b := by
  induction xs with
  | nil => intro a b h; simpa
  | cons x xs ih =>
      intro a b h
      have hmax : Nat.max a x ≤ Nat.max b x :=
        Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left b x), Nat.le_max_right b x⟩
      simpa [List.foldl_cons] using ih (Nat.max a x) (Nat.max b x) hmax

/-- Lean-only lower-bound helper for the fresh ExtCall temporary bound; HOL
    proves its corresponding `MAX_LIST` reasoning inline in the case proof. -/
private theorem extCall_foldl_max_ge (xs : List Nat) : ∀ a,
    a ≤ xs.foldl (fun m n => Nat.max m n) a := by
  induction xs with
  | nil => intro a; exact Nat.le_refl a
  | cons x xs ih =>
      intro a
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left a x) (ih (Nat.max a x))

/-- Lean-only list-member bound for the fresh ExtCall temporary bound; HOL
    proves its corresponding `MAX_LIST_NOT_MEM` reasoning inline. -/
private theorem extCall_mem_le_foldl_max : ∀ (xs : List Nat) (x : Nat), x ∈ xs →
    x ≤ xs.foldl (fun m n => Nat.max m n) 0
  | [], x, hx => by simp at hx
  | a :: xs, x, hx => by
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with hxa | hx
      · subst x
        exact Nat.le_trans (Nat.le_max_right 0 a) (extCall_foldl_max_ge xs (Nat.max 0 a))
      · exact Nat.le_trans (extCall_mem_le_foldl_max xs x hx)
          (extCall_foldl_max_mono xs 0 (Nat.max 0 a) (Nat.zero_le _))

namespace PcCompileCorrectExtCallWitnesses

/-! Same-module witnesses for the finite-support relation qualifier below. -/

/-! Same-module canonical finite-support relation witness required by the
tagged ExtCall case; this wrapper delegates to the checked roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact

/-! Same-module canonical finite-support relation witness required by the
tagged ExtCall case; this wrapper delegates to the checked roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    context

/-! Same-module canonical finite-support relation witness required by the
tagged ExtCall case; this wrapper delegates to the checked roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} {σ : Type} [NeZero width]
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_CrepSemHOLState state

end PcCompileCorrectExtCallWitnesses

/-- HOL `pc_compile_correct`, `ExtCall` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4485-4545`), for the
    `ExtCall ffi_index ptr1 len1 ptr2 len2` conjunct of the rebound
    `panSem$evaluate_ind` (`panSemScript.sml:777-778`). This case has no
    recursive induction hypotheses. It uses the four expression evaluations
    from the HOL compile arm, then proves both `FinalFFI` and `Ret newFfi
    newBytes` outcomes. The returned-byte branch uses the exact bytearray write
    congruence helper to preserve the source/target memory relation under their
    independently chosen `DecidablePred` instances. The source/target
    evaluators, compiler, and relations are the exact carriers described in
    `PcCompileCorrect.lean`; no target-run, result, or post-state relation is
    assumed. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_ExtCall {width : Nat} {σ : Type} [NeZero width]
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width)
    (source : Flapjack.PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
      (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width),
      source.evaluateHOLFiniteState
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width) =
          (res, s1) →
      res ≠ some .error →
      panToCrepStateRelFiniteExact source t →
      codeRelExactHOLW ctxt source.code t.code →
      panToCrepExcpRelFiniteExact ctxt.eids source.eshapes →
      panToCrepLocalsRelFiniteExact ctxt source.locals t.locals →
      localisedProgHOL
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width) =
          true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact t
          (compileProgExactHOLW ctxt
            (.extCall function configuration configurationLength array arrayLength : ProgHOL width)) =
            (res1, t1) ∧
        panToCrepStateRelFiniteExact s1 t1 ∧
        codeRelExactHOLW ctxt s1.code t1.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
        pcCompileCorrectResultRel ctxt s1 t1 res res1 := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  rw [Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState_extCall_source] at hrun
  split at hrun <;> simp_all
  all_goals try { apply False.elim; apply hres; exact (congrArg Prod.fst hrun).symm }
  split at hrun
  all_goals try { apply False.elim; apply hres; exact (congrArg Prod.fst hrun).symm }
  split at hrun
  all_goals try { apply False.elim; apply hres; exact (congrArg Prod.fst hrun).symm }
  case h_1 =>
    rename_i a b c d
    rename_i bytes1 bytes2 hread1 hread2 address1 length1 address2 length2
    rename_i v0 v1 v2 v3 srcAddress1 srcLength1 srcAddress2 srcLength2
    simp only [Flapjack.localisedProgHOL, Bool.and_eq_true] at hloc
    obtain ⟨ec, hec, hecEval, hboundc⟩ := compileExpWord source t ctxt configuration v3
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using srcLength2)
      hstate hcode hlocals hloc.1.1.1
    obtain ⟨el, hel, helEval, hboundl⟩ := compileExpWord source t ctxt configurationLength srcAddress1
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using bytes1)
      hstate hcode hlocals hloc.1.1.2
    obtain ⟨ea, hea, heaEval, hbounda⟩ := compileExpWord source t ctxt array srcLength1
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using bytes2)
      hstate hcode hlocals hloc.1.2
    obtain ⟨eal, heal, healEval, hboundal⟩ := compileExpWord source t ctxt arrayLength srcAddress2
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using hread1)
      hstate hcode hlocals hloc.2
    let es : List (Flapjack.CrepExpHOL width) := [ec, el, ea, eal]
    let values : List (Flapjack.HolWordLab width) :=
      [.word v3, .word srcAddress1, .word srcLength1, .word srcAddress2]
    let memoryVariables := es.flatMap fun e =>
      Flapjack.crepExpVarsW (Flapjack.crepExpOfHOL e)
    let m := memoryVariables.foldl (fun maximum variableIndex => Nat.max maximum variableIndex) 0
    let temps := [m + 1, m + 2, m + 3, m + 4]
    have hvariables : es.flatMap Flapjack.crepExpVarsHOL = memoryVariables := by
      simp [es, memoryVariables, Flapjack.crepExpVarsW_eq_crepExpVarsHOL_crepExpToHOL,
        Flapjack.crepExpToHOL_crepExpOfHOL]
    have hnodup : temps.Nodup := by simp [temps, List.nodup_cons]
    have hdist : Flapjack.distinctListsHol temps (es.flatMap Flapjack.crepExpVarsHOL) = true := by
      apply (Flapjack.distinctListsHol_eq_true_iff_listDisjoint _ _).mpr
      intro x htemp hvarmem
      have hx' : x ∈ memoryVariables := by rw [← hvariables]; exact hvarmem
      have hle := extCall_mem_le_foldl_max memoryVariables x hx'
      have hle' : x ≤ m := by simpa [m] using hle
      simp [temps] at htemp
      omega
    have hmap : es.map (Flapjack.evalCrepSemHOLExp t) = values.map some := by
      simp [es, values, hecEval, helEval, heaEval, healEval]
    have hcomp : Flapjack.compileProgExactHOLW ctxt
        (.extCall function configuration configurationLength array arrayLength) =
      Flapjack.nestedDecsHOL temps es
        (.extCall function (m + 1) (m + 2) (m + 3) (m + 4)) := by
      simp only [Flapjack.compileProgExactHOLW, Flapjack.compileExtCallExactHOLW,
        hec, hel, hea, heal]
      simp [temps, es, memoryVariables, m, Flapjack.nestedDecsHOL]
    let t' : Flapjack.CrepSemHOLState width σ :=
      { t with locals := t.locals.updateListEq (temps.zip values) }
    have hstateExpanded := hstate
    simp only [Flapjack.panToCrepStateRelFiniteExact] at hstateExpanded
    have hmemory : source.memory = t.memory := hstateExpanded.1
    have hmemaddrs : source.memaddrs = t.memaddrs := hstateExpanded.2.1
    have hbe : source.be = t.be := hstateExpanded.2.2.2.2.2.2.1
    have hffi : source.ffi = t.ffi := hstateExpanded.2.2.2.2.2.2.2.1
    have hread1Target : Flapjack.readBytearrayWordHOL v3 srcAddress1.toNat
        (Flapjack.panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some length1 := by
      rw [hmemory, hmemaddrs, hbe] at length2
      exact length2
    have hread2Target : Flapjack.readBytearrayWordHOL srcLength1 srcAddress2.toNat
        (Flapjack.panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some address2 := by
      rw [hmemory, hmemaddrs, hbe] at a
      exact a
    have hbody : Flapjack.evalCrepSemHOLProgExact t'
        (.extCall function (m + 1) (m + 2) (m + 3) (m + 4)) =
          (some (.finalFfi c), t') := by
      rw [Flapjack.evalCrepSemHOLProgExact_extCall_holShape]
      have hlookupM := Flapjack.mapM_lookup_updateListEq t.locals temps values hnodup
        (by simp [temps, values])
      have hlookupMap : temps.map t'.locals.lookup = values.map some :=
        Flapjack.map_eq_of_mapM_eq_some _ temps values (by simpa [t'] using hlookupM)
      simp only [temps, values, List.map_cons, List.map_nil, List.cons.injEq] at hlookupMap
      rcases hlookupMap with ⟨h1, h2, h3, h4⟩
      rcases h4 with ⟨h4, _⟩
      rw [h1, h2, h3, h4]
      rw [hffi] at d
      simp only [t']
      simp only [hread1Target, hread2Target]
      rw [d]
    have hnest := Flapjack.evalNestedDecsSeqResVarEqHOL es temps t values
      (.extCall function (m + 1) (m + 2) (m + 3) (m + 4))
      ⟨hmap, by simp [temps, es], hdist, hnodup⟩
    rw [hbody] at hnest
    have hrestore : (List.zip temps (temps.map t.locals.lookup)).foldl
        (fun current entry => current.resVarEq entry) t'.locals = t.locals :=
      Flapjack.resVarLookupOriginalEqHOL temps values t.locals
        ⟨hnodup, by simp [temps, values]⟩
    have htarget : Flapjack.evalCrepSemHOLProgExact t
        (Flapjack.compileProgExactHOLW ctxt
          (.extCall function configuration configurationLength array arrayLength)) =
        (some (.finalFfi c), t) := by
      rw [hcomp]
      simpa [t', hrestore] using hnest
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    refine ⟨some (.finalFfi c), t, htarget, ?_, ?_, ?_, ?_⟩
    · simpa [Flapjack.panToCrepStateRelFiniteExact,
        Flapjack.PanSemStateFiniteExact.emptyLocalsHOLFinite] using hstate
    · exact hcode
    · exact hexcp
    · rfl

  case h_2 =>
    all_goals try
      have hresEq : res = some Flapjack.PanSemResultExact.error := by
        simpa using (congrArg Prod.fst hrun).symm
      exact (hres hresEq).elim
    simp only [Flapjack.localisedProgHOL, Bool.and_eq_true] at hloc
    rename_i a b c d
    rename_i bytes1 bytes2 hread1 hread2 address1 length1 address2 length2
    rename_i v0 v1 v2 v3 srcAddress1 srcLength1 srcAddress2 srcLength2
    obtain ⟨ec, hec, hecEval, hboundc⟩ := compileExpWord source t ctxt configuration v2
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using srcAddress2)
      hstate hcode hlocals hloc.1.1.1
    obtain ⟨el, hel, helEval, hboundl⟩ := compileExpWord source t ctxt configurationLength v3
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using srcLength2)
      hstate hcode hlocals hloc.1.1.2
    obtain ⟨ea, hea, heaEval, hbounda⟩ := compileExpWord source t ctxt array srcAddress1
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using bytes1)
      hstate hcode hlocals hloc.1.2
    obtain ⟨eal, heal, healEval, hboundal⟩ := compileExpWord source t ctxt arrayLength srcLength1
      (by simpa [Flapjack.PanSemStateFiniteExact.evalHOLFinite] using bytes2)
      hstate hcode hlocals hloc.2
    let es : List (Flapjack.CrepExpHOL width) := [ec, el, ea, eal]
    let values : List (Flapjack.HolWordLab width) :=
      [.word v2, .word v3, .word srcAddress1, .word srcLength1]
    let memoryVariables := es.flatMap fun e =>
      Flapjack.crepExpVarsW (Flapjack.crepExpOfHOL e)
    let m := memoryVariables.foldl (fun maximum variableIndex => Nat.max maximum variableIndex) 0
    let temps := [m + 1, m + 2, m + 3, m + 4]
    have hvariables : es.flatMap Flapjack.crepExpVarsHOL = memoryVariables := by
      simp [es, memoryVariables, Flapjack.crepExpVarsW_eq_crepExpVarsHOL_crepExpToHOL,
        Flapjack.crepExpToHOL_crepExpOfHOL]
    have hnodup : temps.Nodup := by simp [temps, List.nodup_cons]
    have hdist : Flapjack.distinctListsHol temps (es.flatMap Flapjack.crepExpVarsHOL) = true := by
      apply (Flapjack.distinctListsHol_eq_true_iff_listDisjoint _ _).mpr
      intro x htemp hvarmem
      have hx' : x ∈ memoryVariables := by rw [← hvariables]; exact hvarmem
      have hle := extCall_mem_le_foldl_max memoryVariables x hx'
      have hle' : x ≤ m := by simpa [m] using hle
      simp [temps] at htemp
      omega
    have hmap : es.map (Flapjack.evalCrepSemHOLExp t) = values.map some := by
      simp [es, values, hecEval, helEval, heaEval, healEval]
    have hcomp : Flapjack.compileProgExactHOLW ctxt
        (.extCall function configuration configurationLength array arrayLength) =
      Flapjack.nestedDecsHOL temps es
        (.extCall function (m + 1) (m + 2) (m + 3) (m + 4)) := by
      simp only [Flapjack.compileProgExactHOLW, Flapjack.compileExtCallExactHOLW,
        hec, hel, hea, heal]
      simp [temps, es, memoryVariables, m, Flapjack.nestedDecsHOL]
    let t' : Flapjack.CrepSemHOLState width σ :=
      { t with locals := t.locals.updateListEq (temps.zip values) }
    have hstateExpanded := hstate
    simp only [Flapjack.panToCrepStateRelFiniteExact] at hstateExpanded
    have hmemory : source.memory = t.memory := hstateExpanded.1
    have hmemaddrs : source.memaddrs = t.memaddrs := hstateExpanded.2.1
    have hbe : source.be = t.be := hstateExpanded.2.2.2.2.2.2.1
    have hffi : source.ffi = t.ffi := hstateExpanded.2.2.2.2.2.2.2.1
    have hread1Target : Flapjack.readBytearrayWordHOL v2 v3.toNat
        (Flapjack.panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some address1 := by
      rw [hmemory, hmemaddrs, hbe] at address2
      exact address2
    have hread2Target : Flapjack.readBytearrayWordHOL srcAddress1 srcLength1.toNat
        (Flapjack.panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some length1 := by
      rw [hmemory, hmemaddrs, hbe] at length2
      exact length2
    let tAfter : Flapjack.CrepSemHOLState width σ :=
      { t' with
        memory := Flapjack.panWriteBytearrayWord8HOL srcAddress1 c t.memory t.memaddrs t.be
        ffi := b }
    have hbody : Flapjack.evalCrepSemHOLProgExact t'
        (.extCall function (m + 1) (m + 2) (m + 3) (m + 4)) = (none, tAfter) := by
      rw [Flapjack.evalCrepSemHOLProgExact_extCall_holShape]
      have hlookupM := Flapjack.mapM_lookup_updateListEq t.locals temps values hnodup
        (by simp [temps, values])
      have hlookupMap : temps.map t'.locals.lookup = values.map some :=
        Flapjack.map_eq_of_mapM_eq_some _ temps values (by simpa [t'] using hlookupM)
      simp only [temps, values, List.map_cons, List.map_nil, List.cons.injEq] at hlookupMap
      rcases hlookupMap with ⟨h1, h2, h3, h4⟩
      rcases h4 with ⟨h4, _⟩
      rw [h1, h2, h3, h4]
      rw [hffi] at d
      simp only [t']
      simp only [hread1Target, hread2Target]
      rw [d]
    have hnest := Flapjack.evalNestedDecsSeqResVarEqHOL es temps t values
      (.extCall function (m + 1) (m + 2) (m + 3) (m + 4))
      ⟨hmap, by simp [temps, es], hdist, hnodup⟩
    rw [hbody] at hnest
    have hrestore : (List.zip temps (temps.map t.locals.lookup)).foldl
        (fun current entry => current.resVarEq entry) t'.locals = t.locals :=
      Flapjack.resVarLookupOriginalEqHOL temps values t.locals
        ⟨hnodup, by simp [temps, values]⟩
    let t1 : Flapjack.CrepSemHOLState width σ := { tAfter with locals := t.locals }
    have htarget : Flapjack.evalCrepSemHOLProgExact t
        (Flapjack.compileProgExactHOLW ctxt
          (.extCall function configuration configurationLength array arrayLength)) = (none, t1) := by
      rw [hcomp]
      simpa [t', tAfter, t1, hrestore] using hnest
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    have hstateAfter := Flapjack.panToCrepStateRelFiniteExact_writeBytearray
      source t srcAddress1 c (inferInstance : DecidablePred source.memaddrs)
      (inferInstance : DecidablePred t.memaddrs) b hstate
    refine ⟨none, t1, htarget, ?_, ?_, ?_, ?_⟩
    · simpa [t1, tAfter, Flapjack.panToCrepStateRelFiniteExact] using hstateAfter
    · simpa [Flapjack.PanSemStateFiniteExact.ofExact] using hcode
    · simpa [Flapjack.PanSemStateFiniteExact.ofExact] using hexcp
    · exact ⟨rfl, hlocals⟩

end Flapjack
