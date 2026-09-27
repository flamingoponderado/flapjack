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

/-- Exact port of `pan_to_crepProofScript.sml:596-620`, over the exact
`CrepProgHOL`/`CrepExpHOL` and finite-support `CrepSemHOLState` carriers.
The four premises are exactly successful initialiser evaluation, equal name
and expression lengths, declaration-name/expression-variable disjointness,
and distinct declaration names. The conclusion is HOL's complete
`nested_decs` evaluation equation with the original local bindings restored by
`FOLDL res_var`. The finite-map qualifier records the canonical
`HolFiniteMapExact` representation for HOL's `locals`, `globals`, and `code`;
the same-module witness above checks its carrier roundtrip. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_nested_decs_seq_res_var_eq"
  (fmap_as_finite_support := [locals, globals, code])]
theorem evalNestedDecsSeqResVarEqCrepHOL {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (expressions : List (CrepExpHOL width)) (names : List Nat)
    (values : List (HolWordLab width)) (body : CrepProgHOL width)
    (hEval : expressions.map (evalCrepSemHOLExpDefault state) = values.map some)
    (hLength : names.length = expressions.length)
    (hDistinct : distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true)
    (hNodup : names.Nodup) :
    evalCrepSemHOLProgDefault state (nestedDecsHOL names expressions body) =
      let result := evalCrepSemHOLProgDefault
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
  have hBodyDefault :
      evalCrepSemHOLProgDefault
          { state with locals := state.locals.updateListEq (names.zip values) } body =
        evalCrepSemHOLProg (nestedDecsUpdatedInput state names values)
          (nestedDecsMemDec state names values memDec)
          (nestedDecsShMemDec state names values shMemDec) body := by
    rw [← nestedDecsUpdatedInput_eq_updateListEq state names values]
    simp only [evalCrepSemHOLProgDefault]
    congr 1 <;> funext address <;> exact Subsingleton.elim _ _
  rw [hBodyDefault]
  simpa [evalCrepSemHOLProgDefault, restoreNestedDecsLocals] using hported

end Flapjack
