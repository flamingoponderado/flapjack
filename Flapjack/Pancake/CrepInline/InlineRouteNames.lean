import Flapjack.Pancake.CrepInline.InlineRouteBridge

/-! Byte-name preservation for the executed recursive inliner. These are
Flapjack codec obligations, with no separate HOL declaration, needed to turn
encoded-output correspondence into decoded-output equality. -/

namespace Flapjack.CrepInlineRoute

private theorem crepNameRanged_decode (name : Flapjack.Basis.Pure.MlString.MlString) :
    CrepNameRanged (Flapjack.Basis.Pure.MlString.toStringOfBytes name) := by
  intro character hmem
  simp only [Flapjack.Basis.Pure.MlString.toStringOfBytes, String.toList_ofList,
    List.mem_map] at hmem
  obtain ⟨byte, _, rfl⟩ := hmem
  have hb : byte.toNat < 256 := by simpa using byte.isLt
  rw [Flapjack.Basis.Pure.MlString.ofNat_toNat_char byte]
  exact hb

/-- Decoding an exact Crep program supplies the byte-name invariant without an
input assumption. This is codec infrastructure, not a HOL theorem port. -/
theorem crepProgOfHOL_nameRanged {width : Nat} [NeZero width]
    (program : CrepProgHOL width) : CrepProgNameRanged (crepProgOfHOL program) := by
  fun_induction crepProgOfHOL program <;>
    simp_all [CrepProgNameRanged, crepNameRanged_decode]

/-- Loading arguments introduces only numeric local names. -/
theorem nestedDecs_nameRanged {width : Nat} (names : List Nat)
    (arguments : List (CrepExp (BitVec width))) (program : CrepProg (BitVec width))
    (h : CrepProgNameRanged program) :
    CrepProgNameRanged (nestedDecs names arguments program) := by
  fun_induction nestedDecs names arguments program <;>
    simp_all [CrepProgNameRanged]

/-- A sequence retains the byte-name invariant of its constituent programs. -/
theorem crepNestedSeq_nameRanged {width : Nat}
    (programs : List (CrepProg (BitVec width)))
    (h : ∀ program ∈ programs, CrepProgNameRanged program) :
    CrepProgNameRanged (crepNestedSeq programs) := by
  fun_induction crepNestedSeq programs <;>
    simp_all [CrepProgNameRanged]

/-- Argument loading does not add function names. -/
theorem crepArgLoad_nameRanged {width : Nat} (temporaryNames argumentNames : List Nat)
    (arguments : List (CrepExp (BitVec width))) (program : CrepProg (BitVec width))
    (h : CrepProgNameRanged program) :
    CrepProgNameRanged (crepArgLoad temporaryNames arguments argumentNames program) := by
  exact nestedDecs_nameRanged _ _ _ (nestedDecs_nameRanged _ _ _ h)

/-- Early-exit elimination only discards or structurally rewrites programs. -/
theorem crepUnreachElim_nameRanged {width : Nat} (program : CrepProg (BitVec width))
    (h : CrepProgNameRanged program) :
    CrepProgNameRanged (crepUnreachElim program).1 := by
  fun_induction crepUnreachElim program <;>
    simp_all [CrepProgNameRanged] <;>
    split <;> simp_all [CrepProgNameRanged]

private theorem assignments_nameRanged {width : Nat} (names : List Nat)
    (values : List (CrepExp (BitVec width))) :
    CrepProgNameRanged (crepNestedSeq (names.zipWith CrepProg.assign values)) := by
  apply crepNestedSeq_nameRanged
  intro program h
  induction names generalizing values with
  | nil => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.zipWith, List.mem_cons] at h
          rcases h with rfl | h
          · simp [CrepProgNameRanged]
          · exact ih values h

/-- Return rewriting preserves function names and only generates local assignments. -/
theorem crepTransformEoc_nameRanged {width : Nat} (names : List Nat)
    (program : CrepProg (BitVec width)) (h : CrepProgNameRanged program) :
    CrepProgNameRanged (crepTransformEoc names program) := by
  fun_induction crepTransformEoc names program <;>
    simp_all [CrepProgNameRanged, assignments_nameRanged]

/-- Branch-return rewriting introduces only numeric loop exits. -/
theorem crepTransformBranch_nameRanged {width : Nat} (depth : Nat) (names : List Nat)
    (program : CrepProg (BitVec width)) (h : CrepProgNameRanged program) :
    CrepProgNameRanged (crepTransformBranch depth names program) := by
  fun_induction crepTransformBranch depth names program <;>
    simp_all [CrepProgNameRanged, assignments_nameRanged]

/-- Non-tail scaffolding introduces only local variable assignments. -/
theorem crepInlineNontail_nameRanged {width : Nat}
    (program : CrepProg (BitVec width)) (returns temporaryReturns temporaryNames : List Nat)
    (arguments : List (CrepExp (BitVec width))) (argumentNames : List Nat)
    (h : CrepProgNameRanged program) :
    CrepProgNameRanged
      (crepInlineNontail program returns temporaryReturns temporaryNames arguments argumentNames) := by
  unfold crepInlineNontail
  apply nestedDecs_nameRanged
  simp only [CrepProgNameRanged]
  change CrepProgNameRanged (crepArgLoad _ _ _ _) ∧ _
  refine ⟨crepArgLoad_nameRanged _ _ _ _ h, ?_⟩
  simpa only [List.zipWith_map_right] using
    assignments_nameRanged returns (temporaryReturns.map (CrepExp.var : Nat → CrepExp (BitVec width)))

/-- Inlining a call does not create new function names. The original call and
handler, when retained, must themselves satisfy the byte-name invariant. -/
theorem crepInlineCallBody_nameRanged {width : Nat}
    (info : Option (List Nat × Option (BitVec width × CrepProg (BitVec width))))
    (name : FunName) (arguments : List (CrepExp (BitVec width))) (params : List Nat)
    (body : CrepProg (BitVec width)) (hbody : CrepProgNameRanged body)
    (hcall : CrepProgNameRanged (.call info name arguments)) :
    CrepProgNameRanged (crepInlineCallBody info name arguments params body) := by
  cases info with
  | none =>
      simpa only [crepInlineCallBody, crepInlineTail, CrepProgNameRanged, true_and] using
        crepArgLoad_nameRanged (crepInlineTmpNames (arguments.flatMap crepExpVars) params)
          params arguments body hbody
  | some info =>
      rcases info with ⟨returns, handler⟩
      cases handler with
      | some handler => simpa only [crepInlineCallBody] using hcall
      | none =>
          simp only [crepInlineCallBody]
          split
          · exact hcall
          · apply crepInlineNontail_nameRanged
            split
            · simp only [CrepProgNameRanged]
              change True ∧ _
              exact ⟨True.intro, crepTransformEoc_nameRanged _ _ hbody⟩
            · simp only [CrepProgNameRanged]
              change CrepProgNameRanged (crepTransformBranch _ _ _)
              exact crepTransformBranch_nameRanged _ _ _ hbody

/-- The executed recursive inliner preserves byte-ranged names when its input
and every successfully looked-up callee body are byte-ranged. No evaluation or
simulation assumption is needed; this is production codec infrastructure. -/
theorem crepInlineProgRecursive_nameRanged {width : Nat}
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    (entries : List (CrepInlineEntry (BitVec width))) (active : Std.HashSet FunName)
    (program : CrepProg (BitVec width))
    (hlookup : ∀ name params body, crepInlineLookup name entries = some (params, body) →
      CrepProgNameRanged body)
    (hprogram : CrepProgNameRanged program) :
    CrepProgNameRanged (crepInlineProgRecursive entries active program) := by
  fun_induction crepInlineProgRecursive entries active program <;>
    simp_all [CrepProgNameRanged]
  all_goals
    apply crepInlineCallBody_nameRanged
    · grind [crepUnreachElim_nameRanged]
    · simp only [CrepProgNameRanged]
      assumption

private theorem crepInlineLookup_nameRanged {width : Nat}
    [BEq FunName] (entries : List (CrepInlineEntry (BitVec width)))
    (hentries : ∀ entry ∈ entries, CrepProgNameRanged entry.2.2)
    (name : FunName) (params : List Nat) (body : CrepProg (BitVec width))
    (hlookup : crepInlineLookup name entries = some (params, body)) :
    CrepProgNameRanged body := by
  induction entries with
  | nil => simp [crepInlineLookup] at hlookup
  | cons entry entries ih =>
      rcases entry with ⟨key, parameters, program⟩
      simp only [crepInlineLookup] at hlookup
      split at hlookup
      · cases hlookup
        exact hentries (key, params, body) (List.mem_cons_self)
      · exact ih (fun entry h => hentries entry (List.mem_cons_of_mem _ h)) hlookup

/-- The executed top-level inline pass preserves table names and byte-ranged
bodies; its filtered inline map inherits the range obligation from the input.
This is Flapjack codec infrastructure with no separate HOL original. -/
theorem compileInlTopHOL_nameRanged {width : Nat}
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    (names : List FunName)
    (functions : List (FunName × List Nat × CrepProg (BitVec width)))
    (hfunctions : ∀ function ∈ functions,
      CrepNameRanged function.1 ∧ CrepProgNameRanged function.2.2) :
    ∀ function ∈ compileInlTopHOL names functions,
      CrepNameRanged function.1 ∧ CrepProgNameRanged function.2.2 := by
  intro function hfunction
  unfold compileInlTopHOL at hfunction
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hfunction
  refine ⟨(hfunctions source hsource).1, ?_⟩
  apply crepInlineProgRecursive_nameRanged
  · intro name params body hlookup
    apply crepInlineLookup_nameRanged _ ?_ name params body hlookup
    intro entry hentry
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hentry
    exact (hfunctions source (List.mem_filter.mp hsource).1).2
  · exact (hfunctions source hsource).2

/-- On decoded native tables, the executed inliner equals the decoded exact
inliner for every table and inline-name list. Byte-name obligations follow from
native decoding and are not public premises. This is Flapjack codec
infrastructure, not a distinct HOL theorem port. -/
theorem compileInlTopHOL_decode_eq {width : Nat} [NeZero width]
    (names : List CrepInlineMapHOLName)
    (functions : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    compileInlTopHOL (names.map Flapjack.Basis.Pure.MlString.toStringOfBytes)
        (functions.map fun t => (Flapjack.Basis.Pure.MlString.toStringOfBytes t.1,
          t.2.1, crepProgOfHOL t.2.2)) =
      (CrepInlineCanonical.compileInlTopHOLExact names functions).map
        (fun t => (Flapjack.Basis.Pure.MlString.toStringOfBytes t.1,
          t.2.1, crepProgOfHOL t.2.2)) := by
  let decode := fun t : CrepInlineMapHOLName × List Nat × CrepProgHOL width =>
    (Flapjack.Basis.Pure.MlString.toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)
  let encode := fun t : FunName × List Nat × CrepProg (BitVec width) =>
    (Flapjack.Basis.Pure.MlString.ofString t.1, t.2.1, crepProgToHOL t.2.2)
  let inlineNames := names.map Flapjack.Basis.Pure.MlString.toStringOfBytes
  have hinput : ∀ t ∈ functions.map decode,
      CrepNameRanged t.1 ∧ CrepProgNameRanged t.2.2 := by
    intro t ht
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp ht
    exact ⟨crepNameRanged_decode _, crepProgOfHOL_nameRanged _⟩
  have hencoded : (compileInlTopHOL inlineNames (functions.map decode)).map encode =
      CrepInlineCanonical.compileInlTopHOLExact names functions := by
    have h := crepProgToHOL_compileInlTopHOL names (functions.map decode)
      (fun t ht => (hinput t ht).1) (fun t ht => (hinput t ht).2)
    simpa [decode, encode, inlineNames, List.map_map, Function.comp_def,
      Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes,
      crepProgToHOL_crepProgOfHOL, Prod.eta, List.map_id] using h
  have houtput := compileInlTopHOL_nameRanged inlineNames (functions.map decode) hinput
  change compileInlTopHOL inlineNames (functions.map decode) = _
  calc
    compileInlTopHOL inlineNames (functions.map decode) =
        (compileInlTopHOL inlineNames (functions.map decode)).map id := by simp
    _ = ((compileInlTopHOL inlineNames (functions.map decode)).map encode).map decode := by
      rw [List.map_map]
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply, encode, decode]
      rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes _ (houtput t ht).1,
        crepProgOfHOL_crepProgToHOL _ (houtput t ht).2]
      rcases t with ⟨name, params, body⟩
      rfl
    _ = _ := congrArg (List.map decode) hencoded

end Flapjack.CrepInlineRoute
