import Flapjack.CrepeSemantics

/-!
Expression non-interference for fresh Crep locals.  This is the evaluator
lemma needed to discharge temporary-expression stability obligations in
sequential declaration and ExtCall lowering.
-/

namespace Flapjack

theorem evalCrepFullExp_update_of_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α) (expression : CrepExp α)
    (temporary : Nat) (value updateValue : α)
    (hnot : temporary ∉ crepExpVars expression)
    (heval : evalCrepFullExp locals memory baseAddress topAddress expression =
      some value) :
    evalCrepFullExp (updateCrepLocal locals temporary updateValue) memory
      baseAddress topAddress expression = some value := by
  suffices stable : evalCrepFullExp (updateCrepLocal locals temporary updateValue) memory
      baseAddress topAddress expression =
      evalCrepFullExp locals memory baseAddress topAddress expression by
    exact stable.trans heval
  clear heval value
  fun_induction evalCrepFullExp locals memory baseAddress topAddress expression with
  | case2 name =>
      have hne : name ≠ temporary := Ne.symm (by simpa [crepExpVars] using hnot)
      simp [evalCrepFullExp, updateCrepLocal, hne]
  | _ => simp_all [evalCrepFullExp, crepExpVars, crepExpVars.crepExpVarsList]


theorem evalCrepFullExpState_update_of_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α)
    (baseAddress topAddress : α) (expression : CrepExp α)
    (temporary : Nat) (value updateValue : α)
    (hnot : temporary ∉ crepExpVars expression)
    (heval : evalCrepFullExpState state baseAddress topAddress expression =
      some value) :
    evalCrepFullExpState { state with locals := updateCrepLocal state.locals temporary updateValue }
      baseAddress topAddress expression = some value := by
  suffices stable : evalCrepFullExpState
      { state with locals := updateCrepLocal state.locals temporary updateValue }
      baseAddress topAddress expression =
      evalCrepFullExpState state baseAddress topAddress expression by
    exact stable.trans heval
  clear heval value
  fun_induction evalCrepFullExpState state baseAddress topAddress expression with
  | case2 name =>
      have hne : name ≠ temporary := Ne.symm (by simpa [crepExpVars] using hnot)
      simp [evalCrepFullExpState, updateCrepLocal, hne]
  | _ => simp_all [evalCrepFullExpState, crepExpVars, crepExpVars.crepExpVarsList]


theorem evalCrepFullExps_update_of_forall_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α) (expressions : List (CrepExp α))
    (temporary : Nat)
    (updateValue : α)
    (hnot : ∀ expression ∈ expressions,
      temporary ∉ crepExpVars expression)
    (values : List α)
    (heval : evalCrepFullExps locals memory baseAddress topAddress expressions =
      some values) :
    evalCrepFullExps (updateCrepLocal locals temporary updateValue) memory
      baseAddress topAddress expressions = some values := by
  induction expressions generalizing values with
  | nil =>
      simpa [evalCrepFullExps] using heval
  | cons expression expressions ih =>
      have hnotExpression : temporary ∉ crepExpVars expression := by
        exact hnot expression (by simp)
      have hnotExpressions : ∀ expression ∈ expressions,
          temporary ∉ crepExpVars expression := by
        intro expression hmem
        exact hnot expression (by simp [hmem])
      cases hvalue : evalCrepFullExp locals memory baseAddress topAddress expression with
      | none =>
          simp [evalCrepFullExps, hvalue] at heval
      | some value =>
          have hvalue' := evalCrepFullExp_update_of_not_mem
            locals memory baseAddress topAddress expression temporary value updateValue
            hnotExpression hvalue
          cases htail : evalCrepFullExps locals memory baseAddress topAddress expressions with
          | none =>
              simp [evalCrepFullExps, hvalue, htail] at heval
          | some tailValues =>
              have htail' := ih hnotExpressions tailValues htail
              have hvalues : value :: tailValues = values := by
                simpa [evalCrepFullExps, hvalue, htail] using heval
              cases hvalues
              simp [evalCrepFullExps, hvalue', htail']


theorem evalCrepFullExpsState_update_of_forall_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α)
    (baseAddress topAddress : α) (expressions : List (CrepExp α))
    (temporary : Nat)
    (updateValue : α)
    (hnot : ∀ expression ∈ expressions,
      temporary ∉ crepExpVars expression)
    (values : List α)
    (heval : evalCrepFullExpsState state baseAddress topAddress expressions =
      some values) :
    evalCrepFullExpsState { state with locals := updateCrepLocal state.locals temporary updateValue }
      baseAddress topAddress expressions = some values := by
  induction expressions generalizing values with
  | nil =>
      simpa [evalCrepFullExpsState] using heval
  | cons expression expressions ih =>
      have hnotExpression : temporary ∉ crepExpVars expression := by
        exact hnot expression (by simp)
      have hnotExpressions : ∀ expression ∈ expressions,
          temporary ∉ crepExpVars expression := by
        intro expression hmem
        exact hnot expression (by simp [hmem])
      cases hvalue : evalCrepFullExpState state baseAddress topAddress expression with
      | none =>
          simp [evalCrepFullExpsState, hvalue] at heval
      | some value =>
          have hvalue' := evalCrepFullExpState_update_of_not_mem
            state baseAddress topAddress expression temporary value updateValue
            hnotExpression hvalue
          cases htail : evalCrepFullExpsState state baseAddress topAddress expressions with
          | none =>
              simp [evalCrepFullExpsState, hvalue, htail] at heval
          | some tailValues =>
              have htail' := ih hnotExpressions tailValues htail
              have hvalues : value :: tailValues = values := by
                simpa [evalCrepFullExpsState, hvalue, htail] using heval
              cases hvalues
              simp [evalCrepFullExpsState, hvalue', htail']

/-- Cake's `eval_some_var_cexp_local_lookup` (`crepPropsScript.sml:835`):
a successfully evaluated expression binds every variable that occurs in it. -/
theorem evalCrepFullExpState_local_lookup_of_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α)
    (expression : CrepExp α) (value : α) (name : Nat)
    (heval : evalCrepFullExpState state baseAddress topAddress expression = some value)
    (hmem : name ∈ crepExpVars expression) :
    ∃ w, state.locals name = some w := by
  fun_induction evalCrepFullExpState state baseAddress topAddress expression generalizing value with
  | case2 variableName =>
      have hname : name = variableName := by simpa [crepExpVars] using hmem
      exact ⟨value, hname ▸ heval⟩
  | case3 address ih | case4 address ih | case5 address ih =>
      obtain ⟨addressValue, haddress, _⟩ := Option.bind_eq_some_iff.mp heval
      exact ih addressValue haddress (by simpa [crepExpVars] using hmem)
  | case7 _ left right ihLeft ihRight | case8 left right ihLeft ihRight
  | case9 _ left right ihLeft ihRight | case10 _ left right ihLeft ihRight =>
      obtain ⟨leftValue, hleft, hrest⟩ := Option.bind_eq_some_iff.mp heval
      obtain ⟨rightValue, hright, _⟩ := Option.bind_eq_some_iff.mp hrest
      simp only [crepExpVars, crepExpVars.crepExpVarsList, List.mem_append,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with hmem | hmem
      · exact ihLeft leftValue hleft hmem
      · exact ihRight rightValue hright hmem
  | case13 => contradiction
  | _ => simp only [crepExpVars, List.not_mem_nil] at hmem

/-- Helper: a member of the flattened variable lists of a successfully mapped list
comes from an element whose evaluation succeeds. -/
theorem exists_mapM_of_mem_flatten_map {α β γ : Type _}
    (f : α → Option β) (g : α → List γ) (es : List α) (vs : List β) (n : γ)
    (heval : es.mapM f = some vs)
    (hmem : n ∈ (es.map g).flatten) :
    ∃ e ∈ es, ∃ v, f e = some v ∧ n ∈ g e := by
  induction es generalizing vs with
  | nil => simp at hmem
  | cons e es ih =>
      rw [List.mapM_cons] at heval
      cases hfe : f e with
      | none => simp [hfe] at heval
      | some v =>
          simp only [hfe] at heval
          cases hes : es.mapM f with
          | none => simp [hes] at heval
          | some vs' =>
              simp only [hes] at heval
              have hvs : v :: vs' = vs := by simpa using heval
              subst hvs
              simp only [List.map_cons, List.flatten_cons, List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ⟨e, by simp, v, hfe, hmem⟩
              · obtain ⟨e', he'mem, v', hf', hn'⟩ := ih vs' hes hmem
                exact ⟨e', by simp [he'mem], v', hf', hn'⟩

/-- Cake's `opt_mmap_eval_some_var_cexp_local_lookup` (`crepPropsScript.sml:847`):
a successfully evaluated expression list binds every variable occurring in any
of its expressions. -/
theorem evalCrepFullExpsState_local_lookup_of_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α)
    (expressions : List (CrepExp α)) (values : List α) (name : Nat)
    (heval : expressions.mapM (evalCrepFullExpState state baseAddress topAddress) = some values)
    (hmem : name ∈ (expressions.map crepExpVars).flatten) :
    ∃ w, state.locals name = some w := by
  obtain ⟨expression, _hexpression, value, hvalue, hmemExpression⟩ :=
    exists_mapM_of_mem_flatten_map
      (evalCrepFullExpState state baseAddress topAddress) crepExpVars
      expressions values name heval hmem
  exact evalCrepFullExpState_local_lookup_of_mem state baseAddress topAddress
    expression value name hvalue hmemExpression

end Flapjack
