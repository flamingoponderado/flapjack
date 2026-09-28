import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedAssign

/-! Exact Pan-to-Crep nested declaration evaluator theorem group. -/

namespace Flapjack

namespace EvalNestedDecsFiniteSupport

/-! Local canonical carrier evidence is required because the reference checker
validates finite-map qualifiers in the theorem's own counterpart module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Flapjack-only map algebra supporting the induction; HOL has no separate
commutation lemma for two `res_var` updates in this theorem's source proof. -/
private theorem resVarEqCommutesAtDistinctKeys {α β : Type} [DecidableEq α]
    (map : HolFiniteMapExact α β) (key other : α)
    (old oldOther : Option β) (hne : key ≠ other) :
    HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq map (key, old)) (other, oldOther) =
      HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq map (other, oldOther)) (key, old) := by
  apply HolFiniteMapExact.ext
  funext query
  cases old with
  | none =>
      cases oldOther with
      | none =>
          exact congrFun (FDOMSUB_HOL_commutes map.lookup key other hne) query
      | some value =>
          exact (congrFun
            (FDOMSUB_HOL_FUPDATE_HOL_neq map.lookup key other value hne) query).symm
  | some value =>
      cases oldOther with
      | none =>
          exact congrFun
            (FDOMSUB_HOL_FUPDATE_HOL_neq map.lookup other key value hne.symm) query
      | some otherValue =>
          exact congrFun
            (FUPDATE_HOL_comm map.lookup key value other otherValue hne) query

/-- Flapjack-only fold consequence of the preceding map algebra; HOL has no
separate theorem for commuting one restoration past a fresh-key fold. -/
private theorem foldlResVarEqCommutesAtFreshKey {β : Type}
    [DecidableEq Nat] (map : HolFiniteMapExact Nat β) (key : Nat)
    (old : Option β) (names : List Nat) (values : List (Option β))
    (hfresh : ∀ name, name ∈ names → key ≠ name) :
    (List.zip names values).foldl
        (fun current entry => HolFiniteMapExact.resVarEq current entry)
        (HolFiniteMapExact.resVarEq map (key, old)) =
      HolFiniteMapExact.resVarEq
        ((List.zip names values).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry) map)
        (key, old) := by
  induction names generalizing values map with
  | nil => simp
  | cons name names ih =>
      cases values with
      | nil => simp
      | cons value values =>
          have hkey : key ≠ name := hfresh name (by simp)
          have htail : ∀ item, item ∈ names → key ≠ item := by
            intro item hmem
            exact hfresh item (by simp [hmem])
          simp only [List.zip_cons_cons, List.foldl_cons]
          rw [resVarEqCommutesAtDistinctKeys map key name old value hkey]
          exact ih (HolFiniteMapExact.resVarEq map (name, value)) values htail

end EvalNestedDecsFiniteSupport

/-- Flapjack-only notation for the exact `FOLDL res_var` result field; HOL's
record update is expressed inline in `eval_nested_decs_seq_res_var_eq`. -/
private def restoreNestedDecsLocals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (names : List Nat)
    (oldValues : List (Option (HolWordLab width))) : CrepSemHOLState width σ :=
  let restored := List.foldl
    (fun current entry => HolFiniteMapExact.resVarEq current entry)
    state.locals (List.zip names oldValues)
  { state with locals := restored }

/-- Flapjack-only recursive form of the HOL `FUPDATE_LIST` input state, used
for induction over `nested_decs`; HOL does not declare this helper. -/
@[reducible] private def nestedDecsUpdatedInput {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (names : List Nat)
    (values : List (HolWordLab width)) : CrepSemHOLState width σ :=
  match names, values with
  | name :: names, value :: values =>
      nestedDecsUpdatedInput (CrepSemHOLState.setVar name value state) names values
  | _, _ => state

/-- Flapjack-only transport of the evaluator's operational memory decider
across local-only updates; HOL's set predicates need no Lean decider argument. -/
private def nestedDecsMemDec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (names : List Nat)
    (values : List (HolWordLab width))
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address)) :
    (address : BitVec width) →
      Decidable ((nestedDecsUpdatedInput state names values).memaddrs address) := by
  intro address
  have hdomain :
      (nestedDecsUpdatedInput state names values).memaddrs address = state.memaddrs address := by
    induction names generalizing values state with
    | nil => cases values <;> rfl
    | cons name names ih =>
        cases values with
        | nil => rfl
        | cons value values =>
            simpa [nestedDecsUpdatedInput, CrepSemHOLState.setVar] using
              ih (CrepSemHOLState.setVar name value state) values
  exact cast (congrArg Decidable hdomain.symm) (memDec address)

/-- Flapjack-only transport of the evaluator's operational shared-memory
decider across local-only updates; HOL has no corresponding explicit input. -/
private def nestedDecsShMemDec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (names : List Nat)
    (values : List (HolWordLab width))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address)) :
    (address : BitVec width) →
      Decidable ((nestedDecsUpdatedInput state names values).shMemaddrs address) := by
  intro address
  have hdomain :
      (nestedDecsUpdatedInput state names values).shMemaddrs address = state.shMemaddrs address := by
    induction names generalizing values state with
    | nil => cases values <;> rfl
    | cons name names ih =>
        cases values with
        | nil => rfl
        | cons value values =>
            simpa [nestedDecsUpdatedInput, CrepSemHOLState.setVar] using
              ih (CrepSemHOLState.setVar name value state) values
  exact cast (congrArg Decidable hdomain.symm) (shMemDec address)

/-- Flapjack-only empty-list equation for the decision-procedure transport;
HOL does not expose the transport helper. -/
@[simp] private theorem nestedDecsMemDecNil {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address)) :
    nestedDecsMemDec state [] [] memDec = memDec := by
  funext address
  simp [nestedDecsMemDec, nestedDecsUpdatedInput]

/-- Flapjack-only empty-list equation for the shared-memory decision-procedure
transport; HOL does not expose the transport helper. -/
@[simp] private theorem nestedDecsShMemDecNil {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address)) :
    nestedDecsShMemDec state [] [] shMemDec = shMemDec := by
  funext address
  simp [nestedDecsShMemDec, nestedDecsUpdatedInput]

/-- Flapjack-only evaluator equation exposing the `Dec` clause with setVar's
domain-decider transport; it packages Lean implementation details, not a
separate HOL theorem. -/
private theorem evalCrepSemHOLProgDecAfterSetVar
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (name : Nat) (expression : CrepExpHOL width) (body : CrepProgHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.dec name expression body) =
      (match crepExactEvalExp state memDec expression with
       | none => (some .error, state)
       | some value =>
           let old := state.locals.lookup name
           let step := evalCrepSemHOLProgAfterSetVar state memDec shMemDec name value body
           (step.1, { step.2 with locals := step.2.locals.resVarEq (name, old) })) := by
  rw [evalCrepSemHOLProg_dec]
  cases hEval : crepExactEvalExp state memDec expression with
  | none => simp
  | some value =>
      have hStep :
          evalCrepSemHOLProg (CrepSemHOLState.setVar name value state) memDec shMemDec body =
            evalCrepSemHOLProg (CrepSemHOLState.setVar name value state)
              (crepSetVarMemDec state memDec name value)
              (crepSetVarShMemDec state shMemDec name value) body := by
        congr 1 <;> funext address <;> exact Subsingleton.elim _ _
      simp only [evalCrepSemHOLProgAfterSetVar]
      rw [hStep]

/-! Lean evaluator deciders are operational inputs, not additional logical
assumptions in the HOL theorem. -/

/-- Flapjack-only proof helper retaining the Lean evaluator's explicit
decidable set-membership arguments. HOL's theorem has no such parameters; the
public tagged wrapper chooses them classically. -/
theorem evalNestedDecsSeqResVarEqCrepHOLWithDeciders
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (expressions : List (CrepExpHOL width)) (names : List Nat)
    (values : List (HolWordLab width)) (body : CrepProgHOL width)
    (hEval : expressions.map (crepExactEvalExp state memDec) = values.map some)
    (hLength : names.length = expressions.length)
    (hDistinct : distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true)
    (hNodup : names.Nodup) :
    evalCrepSemHOLProg state memDec shMemDec (nestedDecsHOL names expressions body) =
      let result := evalCrepSemHOLProg (nestedDecsUpdatedInput state names values)
        (nestedDecsMemDec state names values memDec)
        (nestedDecsShMemDec state names values shMemDec) body
      (result.1, restoreNestedDecsLocals result.2 names (names.map state.locals.lookup)) := by
  induction expressions generalizing names values state memDec shMemDec with
  | nil =>
      cases names with
      | nil =>
          cases values with
          | nil =>
              simp [nestedDecsHOL, nestedDecsUpdatedInput, restoreNestedDecsLocals]
          | cons value values => simp at hEval
      | cons name names => simp at hLength
  | cons expression expressions ih =>
      cases names with
      | nil => simp at hLength
      | cons name names =>
          cases values with
          | nil => simp at hEval
          | cons value values =>
              simp only [List.length_cons] at hLength
              simp only [List.map_cons] at hEval
              obtain ⟨hEvalHead, hEvalTail⟩ := List.cons.inj hEval
              have hLengthTail : names.length = expressions.length := by omega
              have hNodupTail : names.Nodup := (List.nodup_cons.mp hNodup).2
              have hNameNotTail : name ∉ names := (List.nodup_cons.mp hNodup).1
              have hDisjoint :
                  ListDisjoint (name :: names)
                    ((expression :: expressions).flatMap crepExpVarsHOL) :=
                (distinctListsHol_eq_true_iff_listDisjoint _ _).mp hDistinct
              have hNameNotAllVars :
                  name ∉ (expression :: expressions).flatMap crepExpVarsHOL := by
                intro hmem
                exact hDisjoint name (by simp) hmem
              have hDistinctTail :
                  distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true := by
                apply (distinctListsHol_eq_true_iff_listDisjoint _ _).mpr
                intro n hn hvars
                have hvars' :
                    n ∈ (expression :: expressions).flatMap crepExpVarsHOL := by
                  simp only [List.flatMap_cons, List.mem_append]
                  exact Or.inr hvars
                exact hDisjoint n (by simp [hn]) hvars'
              have hNameNotTailVars :
                  ∀ e, e ∈ expressions → name ∉ crepExpVarsHOL e := by
                intro e he hmem
                apply hNameNotAllVars
                exact List.mem_flatMap.mpr ⟨e, by simp [he], hmem⟩
              let boundState : CrepSemHOLState width σ :=
                CrepSemHOLState.setVar name value state
              have hMemDecBound :
                  (address : BitVec width) → Decidable (boundState.memaddrs address) := by
                intro address
                simpa [boundState, CrepSemHOLState.setVar] using memDec address
              have hShMemDecBound :
                  (address : BitVec width) → Decidable (boundState.shMemaddrs address) := by
                intro address
                simpa [boundState, CrepSemHOLState.setVar] using shMemDec address
              have hEvalStateEq :
                  expressions.map (crepExactEvalExp boundState memDec) =
                    expressions.map (crepExactEvalExp state memDec) := by
                apply List.map_congr_left
                intro e he
                have hfresh := hNameNotTailVars e he
                simpa [boundState, CrepSemHOLState.setVar, crepExactEvalExp,
                  evalCrepSemHOLExpWithMemDec] using
                  evalCrepSemHOLExpWithMemDec_updateLocals_eq_of_not_vars
                    state memDec e name value hfresh
              have hEvalTail :
                  expressions.map (crepExactEvalExp boundState memDec) =
                    values.map some := hEvalStateEq.trans hEvalTail
              have hUpdateInput :
                  nestedDecsUpdatedInput boundState names values =
                    nestedDecsUpdatedInput state (name :: names) (value :: values) := rfl
              have hOldLocals :
                  names.map boundState.locals.lookup = names.map state.locals.lookup := by
                apply List.map_congr_left
                intro n hn
                have hne : n ≠ name := by
                  intro heq
                  subst n
                  exact hNameNotTail hn
                simp [boundState, CrepSemHOLState.setVar,
                  HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hne]
              have hOldLocalsSet := hOldLocals
              simp only [boundState] at hOldLocalsSet
              have hEvalTailBound :
                  expressions.map (crepExactEvalExp boundState hMemDecBound) =
                    values.map some := by
                have hMemDecEq :
                    (fun address : BitVec width => memDec address) = hMemDecBound := by
                  funext address
                  exact Subsingleton.elim _ _
                rw [← hMemDecEq]
                exact hEvalTail
              have hMemDecSet :
                  crepSetVarMemDec state memDec name value = hMemDecBound := by
                funext address
                exact Subsingleton.elim _ _
              have hShMemDecSet :
                  crepSetVarShMemDec state shMemDec name value = hShMemDecBound := by
                funext address
                exact Subsingleton.elim _ _
              have hTail := ih boundState hMemDecBound hShMemDecBound names values
                hEvalTailBound hLengthTail hDistinctTail hNodupTail
              simp only [boundState] at hTail
              have hMemFull :
                  nestedDecsMemDec boundState names values hMemDecBound =
                    nestedDecsMemDec state (name :: names) (value :: values) memDec := by
                funext address
                exact Subsingleton.elim _ _
              have hShMemFull :
                  nestedDecsShMemDec boundState names values hShMemDecBound =
                    nestedDecsShMemDec state (name :: names) (value :: values) shMemDec := by
                funext address
                exact Subsingleton.elim _ _
              have hBodyEq :
                  evalCrepSemHOLProg (nestedDecsUpdatedInput boundState names values)
                    (nestedDecsMemDec boundState names values hMemDecBound)
                    (nestedDecsShMemDec boundState names values hShMemDecBound) body =
                  evalCrepSemHOLProg (nestedDecsUpdatedInput state (name :: names) (value :: values))
                    (nestedDecsMemDec state (name :: names) (value :: values) memDec)
                    (nestedDecsShMemDec state (name :: names) (value :: values) shMemDec) body := by
                congr 1 <;> try rfl <;> funext address <;> exact Subsingleton.elim _ _
              simp only [nestedDecsHOL]
              rw [evalCrepSemHOLProgDecAfterSetVar, hEvalHead]
              simp only [evalCrepSemHOLProgAfterSetVar, hMemDecSet, hShMemDecSet,
                hTail]
              rw [hBodyEq]
              have hFold :=
                EvalNestedDecsFiniteSupport.foldlResVarEqCommutesAtFreshKey
                  (map := (evalCrepSemHOLProg
                    (nestedDecsUpdatedInput state (name :: names) (value :: values))
                    (nestedDecsMemDec state (name :: names) (value :: values) memDec)
                    (nestedDecsShMemDec state (name :: names) (value :: values) shMemDec)
                    body).2.locals)
                  name (state.locals.lookup name) names
                  (names.map state.locals.lookup) (by
                    intro n hn
                    have hne : n ≠ name := by
                      intro heq
                      subst n
                      exact hNameNotTail hn
                    exact hne.symm)
              apply Prod.ext
              · rfl
              · simp only [restoreNestedDecsLocals, CrepSemHOLState.mk.injEq]
                constructor
                · simpa [restoreNestedDecsLocals, hOldLocalsSet] using hFold.symm
                all_goals simp

/-- Flapjack-only bridge from induction's recursive local updates to the
HOL-shaped `FUPDATE_LIST` ZIP input; the HOL theorem uses that input directly
and has no separate bridge theorem. -/
private theorem nestedDecsUpdatedInput_eq_updateListEq
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (names : List Nat)
    (values : List (HolWordLab width)) :
    nestedDecsUpdatedInput state names values =
      { state with locals := state.locals.updateListEq (names.zip values) } := by
  induction names generalizing values state with
  | nil => cases values <;> simp [nestedDecsUpdatedInput, HolFiniteMapExact.updateListEq,
      FUPDATE_LIST_HOL]
  | cons name names ih =>
      cases values with
      | nil => simp [nestedDecsUpdatedInput, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]
      | cons value values =>
          simpa [nestedDecsUpdatedInput, CrepSemHOLState.setVar,
            HolFiniteMapExact.updateEq, HolFiniteMapExact.updateListEq,
            FUPDATE_LIST_HOL_cons] using
            ih (CrepSemHOLState.setVar name value state) values

/-! The main statement is shaped directly as HOL's `evaluate` equation. The
recursive update state used by the induction helper is linked to the explicit
`FUPDATE_LIST` ZIP input by `nestedDecsUpdatedInput_eq_updateListEq`. -/

/-- Flapjack-shaped form of HOL `eval_nested_decs_seq_res_var_eq`
    (`pan_to_crepProofScript.sml:596-620`), with separate premises and the
    target run named by `let`. The tagged HOL-shaped statement is
    `evalNestedDecsSeqResVarEqHOL` below; this form stays untagged. -/
theorem evalNestedDecsSeqResVarEqCrepHOL {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (expressions : List (CrepExpHOL width)) (names : List Nat)
    (values : List (HolWordLab width)) (body : CrepProgHOL width)
    (hEval : expressions.map (evalCrepSemHOLExpDefault state) = values.map some)
    (hLength : names.length = expressions.length)
    (hDistinct : distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true)
    (hNodup : names.Nodup) :
    evalCrepSemHOLProgExact state (nestedDecsHOL names expressions body) =
      let result := evalCrepSemHOLProgExact
        { state with locals := state.locals.updateListEq (names.zip values) } body
      (result.1, { result.2 with locals :=
        ((List.zip names (names.map state.locals.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry) result.2.locals) }) := by
  let memDec : (address : BitVec width) → Decidable (state.memaddrs address) :=
    fun address => Classical.propDecidable (state.memaddrs address)
  let shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address) :=
    fun address => Classical.propDecidable (state.shMemaddrs address)
  have hEvalDef : evalCrepSemHOLExpDefault state = crepExactEvalExp state memDec := by
    funext expression
    rfl
  have hEval' : expressions.map (crepExactEvalExp state memDec) = values.map some := by
    rw [← hEvalDef]
    exact hEval
  have hported := evalNestedDecsSeqResVarEqCrepHOLWithDeciders state memDec shMemDec
    expressions names values body hEval' hLength hDistinct hNodup
  have hBodyExact :
      evalCrepSemHOLProgExact
          { state with locals := state.locals.updateListEq (names.zip values) } body =
        evalCrepSemHOLProg (nestedDecsUpdatedInput state names values)
          (nestedDecsMemDec state names values memDec)
          (nestedDecsShMemDec state names values shMemDec) body := by
    rw [← nestedDecsUpdatedInput_eq_updateListEq state names values]
    exact evalCrepSemHOLProgExact_eq_core _ _ _ _
  rw [hBodyExact]
  simpa only [evalCrepSemHOLProgExact_eq_core, restoreNestedDecsLocals] using hported

/-- Exact port of HOL `eval_nested_decs_seq_res_var_eq`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:596-620`):
    `!es ns t ev p. MAP (eval t) es = MAP SOME ev /\ LENGTH ns = LENGTH es /\
      distinct_lists ns (FLAT (MAP var_cexp es)) /\ ALL_DISTINCT ns ==>
      let (q,r) = evaluate (p, t with locals := t.locals |++ ZIP (ns, ev)) in
      evaluate (nested_decs ns es p, t) =
      (q, r with locals := FOLDL res_var r.locals (ZIP (ns, MAP (FLOOKUP t.locals) ns)))`.
    `evaluate` is the tagged line-443 Crep evaluator `evalCrepSemHOLProgExact`
    (`evalCrepSemHOLProgExact_eq_evaluate_def`), and `eval` is the tagged
    `evalCrepSemHOLExp` with the classical address-set decision. The helpers are
    the tagged `nested_decs`, `var_cexp`, `distinct_lists`, `res_var`, and `|++`
    (`updateListEq`). HOL's `let (q,r) = ... in` is the outer `match`.
    Binders and premise conjunction follow HOL. The `CrepSemHOLState` finite
    maps and word width use the reviewed qualifiers. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_nested_decs_seq_res_var_eq"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evalNestedDecsSeqResVarEqHOL {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (ns : List Nat) (t : CrepSemHOLState width σ)
      (ev : List (HolWordLab width)) (p : CrepProgHOL width),
      es.map (@evalCrepSemHOLExp width _ σ t
          (fun address => Classical.propDecidable (t.memaddrs address))) = ev.map some ∧
        ns.length = es.length ∧
        distinctListsHol ns (es.flatMap crepExpVarsHOL) = true ∧
        ns.Nodup →
      match evalCrepSemHOLProgExact
          { t with locals := t.locals.updateListEq (ns.zip ev) } p with
      | (q, r) =>
          evalCrepSemHOLProgExact t (nestedDecsHOL ns es p) =
            (q, { r with locals :=
              ((ns.zip (ns.map t.locals.lookup)).foldl
                (fun current entry => HolFiniteMapExact.resVarEq current entry) r.locals) }) := by
  intro es ns t ev p ⟨hEval, hLength, hDistinct, hNodup⟩
  have h := evalNestedDecsSeqResVarEqCrepHOL t es ns ev p hEval hLength hDistinct hNodup
  rw [h]

/-- Exact port of HOL `globals_lookup` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:435-438`):
`globals_lookup t v = OPT_MMAP (FLOOKUP t.globals) (GENLIST (fun x => n2w x) (size_of_shape (shape_of v)))`.
HOL's `t.globals` is the `5 word |-> 'a word_lab` finite map of the crepSem state, and `GENLIST ...`
is `List.range ... |>.map BitVec.ofNat 5`; `OPT_MMAP (FLOOKUP _)` is `List.mapM` over `.lookup`.
The state finite-map fields use the reviewed `HolFiniteMapExact` translation of HOL's `|->`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "globals_lookup_def"
  (fmap_as_finite_support := [locals, globals, code])]
def globalsLookupHOL {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (value : ValueHOL width) :
    Option (List (HolWordLab width)) :=
  ((List.range (Flapjack.Pancake.PanLang.sizeOfShapeHOL (shapeOfHOLExact value))).map
    (fun index => BitVec.ofNat 5 index)).mapM state.globals.lookup

/-- Flapjack-only list-length proof for the exact `loadGlobalsHOL` recursive
    definition; HOL has no standalone length theorem for this helper. -/
private theorem loadGlobalsHOL_length {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobalsHOL (width := width) address count).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadGlobalsHOL, ih]

/-- Flapjack-only zero-base expansion of exact `loadGlobalsHOL`; HOL has no
    separate theorem equating this list with `GENLIST`'s elementwise form. -/
private theorem loadGlobalsHOL_zero_eq_range {width : Nat} [NeZero width]
    (count : Nat) :
    loadGlobalsHOL (width := width) 0 count =
      (List.range count).map (fun index =>
        CrepExpHOL.loadGlob (BitVec.ofNat 5 index)) := by
  have hGetElem (address : BitVec 5) (index : Nat) (hi : index < count) :
      (loadGlobalsHOL (width := width) address count)[index]'(by
        simpa [loadGlobalsHOL_length] using hi) =
          CrepExpHOL.loadGlob (address + BitVec.ofNat 5 index) := by
    induction count generalizing address index with
    | zero => omega
    | succ count ih =>
        cases index with
        | zero => simp [loadGlobalsHOL]
        | succ index =>
            have hIndex : index < count := by omega
            simp only [loadGlobalsHOL, List.getElem_cons_succ]
            rw [ih (address + 1) index hIndex]
            have hAddress :
                (address + 1) + BitVec.ofNat 5 index =
                  address + BitVec.ofNat 5 (index + 1) := by
              rw [BitVec.ofNat_add]
              simp
              ac_rfl
            rw [hAddress]
  apply List.ext_getElem
  · simp [loadGlobalsHOL_length]
  · intro index hleft hright
    have hindex : index < count := by
      simpa only [loadGlobalsHOL_length] using hleft
    have hload := hGetElem (0 : BitVec 5) index hindex
    rw [hload]
    simp

/-- FLAPJACK-SPECIFIC presentation of HOL candidate
    `evaluate_nested_decs_load_globals` (`pan_to_crepProofScript.sml:4139-4176`).
    Its evaluator now has a tagged, source-reviewed `evaluate_def` clause
    theorem, and the finite-map qualifier witness is settled. This theorem
    remains untagged pending a separate review of its own binders, conjunctive
    premise, and pair-pattern conclusion against HOL; see
    `flapjack-4ac.5.16.5`. -/
theorem evaluateNestedDecsLoadGlobalsCrepHOL {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) (value : ValueHOL width)
    (values : List (HolWordLab width)) (names : List Nat)
    (body : CrepProgHOL width)
    (hLookup : globalsLookupHOL state value = some values)
    (_hSize : Flapjack.Pancake.PanLang.sizeOfShapeHOL (shapeOfHOLExact value) ≤ 32)
    (hDistinct : names.Nodup)
    (hLength : names.length =
      Flapjack.Pancake.PanLang.sizeOfShapeHOL (shapeOfHOLExact value)) :
    evalCrepSemHOLProgExact state
        (nestedDecsHOL names
          (loadGlobalsHOL (width := width) 0
            (Flapjack.Pancake.PanLang.sizeOfShapeHOL (shapeOfHOLExact value))) body) =
      let result := evalCrepSemHOLProgExact
        { state with locals := state.locals.updateListEq (names.zip values) } body
      (result.1, { result.2 with locals :=
        ((List.zip names (names.map state.locals.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry) result.2.locals) }) := by
  let count := Flapjack.Pancake.PanLang.sizeOfShapeHOL (shapeOfHOLExact value)
  let expressions := loadGlobalsHOL (width := width) 0 count
  have hLookupMapM :
      ((List.range count).map (fun index => BitVec.ofNat 5 index)).mapM
        state.globals.lookup = some values := by
    simpa [globalsLookupHOL, count] using hLookup
  have hLookupMap :
      (List.range count).map
        (fun index => state.globals.lookup (BitVec.ofNat 5 index)) =
          values.map some := by
    have hMap :=
      (list_mapM_eq_some_map_some state.globals.lookup
        ((List.range count).map (fun index => BitVec.ofNat 5 index)) values).mp
        hLookupMapM
    simpa only [List.map_map, Function.comp_def] using hMap
  have hLoadEval :
      expressions.map (evalCrepSemHOLExpDefault state) = values.map some := by
    change (loadGlobalsHOL (width := width) 0 count).map
      (evalCrepSemHOLExpDefault state) = values.map some
    rw [loadGlobalsHOL_zero_eq_range]
    have hEvalLoad (index : Nat) :
        evalCrepSemHOLExpDefault state
            (CrepExpHOL.loadGlob (BitVec.ofNat 5 index)) =
          state.globals.lookup (BitVec.ofNat 5 index) := by
      simp [evalCrepSemHOLExpDefault, evalCrepSemHOLExpWithMemDec,
        evalCrepSemHOLExp]
    have hFunctions :
        (fun index => evalCrepSemHOLExpDefault state
          (CrepExpHOL.loadGlob (BitVec.ofNat 5 index))) =
        (fun index => state.globals.lookup (BitVec.ofNat 5 index)) := by
      funext index
      exact hEvalLoad index
    simp only [List.map_map]
    change (List.range count).map (fun index =>
      evalCrepSemHOLExpDefault state
        (CrepExpHOL.loadGlob (BitVec.ofNat 5 index))) = values.map some
    rw [hFunctions]
    exact hLookupMap
  have hLoadLength : expressions.length = count := by
    change (loadGlobalsHOL (width := width) 0 count).length = count
    exact loadGlobalsHOL_length (width := width) 0 count
  have hLoadVariables : expressions.flatMap crepExpVarsHOL = [] := by
    change (loadGlobalsHOL (width := width) 0 count).flatMap crepExpVarsHOL = []
    rw [loadGlobalsHOL_zero_eq_range]
    simp [crepExpVarsHOL]
  have hExpressionDistinct :
      distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true := by
    rw [hLoadVariables]
    simp [distinctListsHol]
  have hNested := evalNestedDecsSeqResVarEqCrepHOL state expressions names
    values body hLoadEval (by simpa [hLoadLength] using hLength)
    hExpressionDistinct hDistinct
  simpa [expressions, count] using hNested

end Flapjack
