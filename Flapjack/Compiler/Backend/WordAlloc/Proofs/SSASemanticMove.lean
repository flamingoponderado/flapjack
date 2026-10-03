import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsForceRename
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsListRename
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileLookupProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts

namespace Flapjack.Compiler.Backend.WordAlloc

-- Flapjack factoring of the original Move proof's bounded parallel-list lookups;
-- these helpers have no independently claimed HOL declaration.
private theorem insertAbsent {α : Type} (key : Nat) (names : List Nat)
    (values : List α) (tree : Spt α) (absent : key ∉ names) :
    sptLookup key (LoopSemStateFiniteExact.sptAlistInsert names values tree) =
      sptLookup key tree := by
  induction names generalizing values with
  | nil => rfl
  | cons name names ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      have different : key ≠ name := by intro same; exact absent (by simp [same])
      rw [LoopSemStateFiniteExact.sptAlistInsert,
        sptLookup_sptInsert_ne name key value _ different]
      exact ih values (fun member => absent (List.mem_cons_of_mem name member))

private theorem insertIndexed {α : Type} [Nonempty α]
    (names : List Nat) (values : List α) (tree : Spt α) (index : Nat)
    (distinct : names.Nodup) (bound : index < names.length)
    (lengths : values.length = names.length) :
    sptLookup (holEl index names)
      (LoopSemStateFiniteExact.sptAlistInsert names values tree) =
      some (holEl index values) := by
  rw [lookup_alist_insert_any]
  have lookup := alookupZipMapSome names values index id
    ⟨by simpa using distinct, bound, lengths⟩
  simp only [List.map_id, id_eq] at lookup
  rw [lookup]

private theorem readIndexed {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F)
    (read : WordSemStateFiniteExact.getVars names state = some values)
    (index : Nat) (bound : index < names.length) :
    sptLookup (holEl index names) state.locals = some (holEl index values) := by
  induction names generalizing values index with
  | nil => simp at bound
  | cons name names ih =>
    cases head : WordSemStateFiniteExact.getVar name state with
    | none => simp [WordSemStateFiniteExact.getVars, head] at read
    | some value =>
      cases tail : WordSemStateFiniteExact.getVars names state with
      | none => simp [WordSemStateFiniteExact.getVars, head, tail] at read
      | some suffix =>
        have equal : value :: suffix = values := by
          simpa [WordSemStateFiniteExact.getVars, head, tail] using read
        subst values
        cases index with
        | zero => simpa [holEl, holHd, WordSemStateFiniteExact.getVar] using head
        | succ index => simpa [holEl] using ih suffix tail index (by simpa using bound)

namespace SemanticMoveWitnesses

/-- Canonical roundtrip of the actual imported native state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticMoveWitnesses

/-- Full original nonrecursive Move simulation. All six original premises and
Error-exempt source permutation, target execution, frame, and locals conclusion
are retained. The evaluator's duplicate-destination and missing-read branches
remain present. Inherits reals_as_rational_cuts through the evaluator (SOUNDNESS8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectMove {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next priority : Nat) (moves : List (Nat × Nat))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.move priority moves) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.move priority moves) source target ssa next tables := by
  classical
  let names := moves.map Prod.fst
  let inputs := moves.map Prod.snd
  let permuted := {source with permute := target.permute}
  have related : ssaLocalsRel next ssa permuted.locals target.locals := h.2.1
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [Flapjack.WordAlloc.wordStateEqRel, permuted] using h.1
  refine ⟨target.permute, ?_⟩
  change let sourceRun := WordSemStateFiniteExact.evaluate (.move priority moves) permuted
         if sourceRun.1 = some .error then True else _
  by_cases distinct : names.Nodup
  · cases read : WordSemStateFiniteExact.getVars inputs permuted with
    | none => simp [WordSemStateFiniteExact.evaluate, names, inputs, distinct, read]
    | some values =>
      have lengths := Flapjack.WordAlloc.getVarsLength inputs permuted values read
      have namesLengths : values.length = names.length := by
        simpa [inputs, names] using lengths
      have bounds : ∀ name ∈ names, name < next := by
        have all := h.2.2.2.1
        simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at all
        exact all.1
      have nonphysical : ¬ isPhyVar next := by
        have alloc := h.2.2.1
        simp only [isAllocVar, decide_eq_true_eq] at alloc
        simp only [isPhyVar, decide_eq_true_eq]; omega
      generalize renamed : listNextVarRename names ssa next = result
      rcases result with ⟨outputs, mapOut, counter⟩
      have shape := listNextVarRenameLemma1 names ssa next outputs mapOut counter renamed
      have outLengths : outputs.length = names.length := by rw [shape.2.1]; simp
      have provisional := ssaLocalsRelListNextVarRename names ssa next
        permuted.locals target.locals outputs mapOut counter values
        ⟨renamed, related, h.2.2.2.2.1, namesLengths.symm, bounds, distinct, nonphysical⟩
      let forced := (inputs.zip outputs).filter (fun (name, _) => decide (name ∉ names))
      let sourceAfter := WordSemStateFiniteExact.setVars names values permuted
      let targetAfter := WordSemStateFiniteExact.setVars outputs values target
      have forceFacts : (∀ pair ∈ forced,
          sptLookup pair.1 sourceAfter.locals = sptLookup pair.2 targetAfter.locals) ∧
          (∀ register ∈ forced.map Prod.snd, sptDomain targetAfter.locals register) := by
        have indexed : ∀ pair ∈ forced, ∃ value,
            sptLookup pair.1 sourceAfter.locals = some value ∧
            sptLookup pair.2 targetAfter.locals = some value := by
          intro pair member
          obtain ⟨zipped, absent⟩ := List.mem_filter.mp member
          have absent' : pair.1 ∉ names := by simpa using absent
          obtain ⟨index, bound, entry⟩ := List.mem_iff_getElem.mp zipped
          have inputBound := List.lt_length_left_of_zip bound
          have outputBound := List.lt_length_right_of_zip bound
          have pairEq : pair = (holEl index inputs, holEl index outputs) := by
            rw [holEl_eq_getElem index inputs inputBound,
              holEl_eq_getElem index outputs outputBound]
            exact entry.symm.trans List.getElem_zip
          have sourceRead := readIndexed inputs values permuted read index inputBound
          have targetRead := insertIndexed outputs values target.locals index shape.1 outputBound
            (namesLengths.trans outLengths.symm)
          refine ⟨holEl index values, ?_, ?_⟩
          · dsimp only [sourceAfter, WordSemStateFiniteExact.setVars]
            rw [insertAbsent pair.1 names values permuted.locals absent', pairEq]
            exact sourceRead
          · dsimp only [targetAfter, WordSemStateFiniteExact.setVars]
            rw [pairEq]
            exact targetRead
        constructor
        · intro pair member
          obtain ⟨value, sourceRead, targetRead⟩ := indexed pair member
          exact sourceRead.trans targetRead.symm
        · intro register member
          obtain ⟨pair, inForce, rfl⟩ := List.mem_map.mp member
          obtain ⟨value, _, targetRead⟩ := indexed pair inForce
          exact (sptMem_iff_lookup pair.2 targetAfter.locals).mpr ⟨value, targetRead⟩
      have finalLocals := ssaLocalsRelForceRename counter mapOut sourceAfter.locals
        targetAfter.locals forced ⟨provisional, forceFacts⟩
      have targetReads := ssaLocalsRelGetVars inputs values next ssa permuted target ⟨related, read⟩
      have zipLengths : outputs.length = (inputs.map (optionLookup ssa)).length := by
        simpa [inputs, names] using outLengths
      have targetRun : WordSemStateFiniteExact.evaluate
          (.move priority (outputs.zip (inputs.map (optionLookup ssa)))) target =
          (none, targetAfter) := by
        simp only [WordSemStateFiniteExact.evaluate,
          List.map_fst_zip (Nat.le_of_eq zipLengths),
          List.map_snd_zip (Nat.le_of_eq zipLengths.symm), shape.1, if_true, targetReads]
        rfl
      have sourceRun : WordSemStateFiniteExact.evaluate (.move priority moves) permuted =
          (none, sourceAfter) := by
        simp only [WordSemStateFiniteExact.evaluate]
        change (if names.Nodup then _ else _) = _
        rw [if_pos distinct, read]
      have sourceExpanded := sourceRun
      dsimp only [permuted] at sourceExpanded
      dsimp only
      simp only [sourceRun, sourceExpanded, reduceCtorEq, if_false]
      simp only [ssaCcTrans, show listNextVarRename (moves.map Prod.fst) ssa next =
        (outputs, mapOut, counter) from renamed]
      change none = (WordSemStateFiniteExact.evaluate
        (.move priority (outputs.zip (inputs.map (optionLookup ssa)))) target).1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceAfter (WordSemStateFiniteExact.evaluate
        (.move priority (outputs.zip (inputs.map (optionLookup ssa)))) target).2 ∧
        ssaLocalsRel counter (forceRename forced mapOut) sourceAfter.locals
        (WordSemStateFiniteExact.evaluate
        (.move priority (outputs.zip (inputs.map (optionLookup ssa)))) target).2.locals
      rw [targetRun]
      exact ⟨rfl, by simpa [sourceAfter, targetAfter, WordSemStateFiniteExact.setVars,
        Flapjack.WordAlloc.wordStateEqRel] using frame, finalLocals⟩
  · simp [WordSemStateFiniteExact.evaluate, names, distinct]

end Flapjack.Compiler.Backend.WordAlloc
