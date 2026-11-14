module

public import Flapjack.PanValues

@[expose] public section

namespace Flapjack

/-! Source evaluator stability lemmas used by Pancake's declaration-call proof.

    These are the Lean counterparts of the `eval_distinct_lists_not_affect'` and
    `opt_mmap_eval_distinct_lists_not_affect` helpers in
    `pan_to_crepProofScript.sml`.  A fresh temporary binding may be installed
    in the local environment without changing an expression that does not
    mention that binding.
-/

/-- Expression evaluation depends on local and global lookups only at names
    occurring in the expression. This infrastructure has no HOL declaration:
    it supports constructing a finite expression view of function-backed maps. -/
theorem evalPanValueExp_lookup_congr
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals locals' globals globals' : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (expression : Exp α) (access : Option (PanValueMemoryAccess α))
    (hloc : ∀ name ∈ expLocalVars expression, locals name = locals' name)
    (hglob : ∀ name ∈ expGlobalVars expression, globals name = globals' name) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression access =
      evalPanValueExp structs locals' globals' memory baseAddress topAddress bytesInWord expression access := by
  have hmain : ∀ expression access,
      (∀ name ∈ expLocalVars expression, locals name = locals' name) →
      (∀ name ∈ expGlobalVars expression, globals name = globals' name) →
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression access =
        evalPanValueExp structs locals' globals' memory baseAddress topAddress bytesInWord expression access := by
    apply evalPanValueExp.induct
      (motive1 := fun es access =>
        (∀ name ∈ expLocalVars.expLocalVarsList es, locals name = locals' name) →
        (∀ name ∈ expGlobalVars.expGlobalVarsList es, globals name = globals' name) →
        evalPanValueExp.evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord es access =
          evalPanValueExp.evalPanValueExps structs locals' globals' memory baseAddress topAddress bytesInWord es access)
      (motive2 := fun e access =>
        (∀ name ∈ expLocalVars e, locals name = locals' name) →
        (∀ name ∈ expGlobalVars e, globals name = globals' name) →
        evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e access =
          evalPanValueExp structs locals' globals' memory baseAddress topAddress bytesInWord e access)
      (motive3 := fun fs access =>
        (∀ name ∈ expLocalVars.expLocalVarsFieldList fs, locals name = locals' name) →
        (∀ name ∈ expGlobalVars.expGlobalVarsFieldList fs, globals name = globals' name) →
        evalPanValueExp.evalPanValueFields structs locals globals memory baseAddress topAddress bytesInWord fs access =
          evalPanValueExp.evalPanValueFields structs locals' globals' memory baseAddress topAddress bytesInWord fs access)
    all_goals
      intros
      simp_all [evalPanValueExp, evalPanValueExp.evalPanValueExps,
        evalPanValueExp.evalPanValueFields, expLocalVars, expLocalVars.expLocalVarsList,
        expLocalVars.expLocalVarsFieldList, expGlobalVars, expGlobalVars.expGlobalVarsList,
        expGlobalVars.expGlobalVarsFieldList, List.mem_append]
  exact hmain expression access hloc hglob

theorem evalPanValueExp_update_local_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq String] [LawfulBEq String]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (expression : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (name : VarName) (replacement : PanValue α)
    (hname : name ∉ expLocalVars expression) :
    evalPanValueExp structs (updatePanValueMap locals name replacement) globals
      memory baseAddress topAddress bytesInWord expression memoryAccess =
    evalPanValueExp structs locals globals memory baseAddress topAddress
      bytesInWord expression memoryAccess := by
  have hmain : ∀ expression memoryAccess,
      name ∉ expLocalVars expression →
      evalPanValueExp structs (updatePanValueMap locals name replacement) globals
          memory baseAddress topAddress bytesInWord expression memoryAccess =
        evalPanValueExp structs locals globals memory baseAddress topAddress
          bytesInWord expression memoryAccess := by
    apply evalPanValueExp.induct
      (motive1 := fun expressions memoryAccess =>
        name ∉ expLocalVars.expLocalVarsList expressions →
        evalPanValueExp.evalPanValueExps structs
            (updatePanValueMap locals name replacement) globals memory
            baseAddress topAddress bytesInWord expressions memoryAccess =
          evalPanValueExp.evalPanValueExps structs locals globals memory
            baseAddress topAddress bytesInWord expressions memoryAccess)
      (motive2 := fun expression memoryAccess =>
        name ∉ expLocalVars expression →
        evalPanValueExp structs (updatePanValueMap locals name replacement)
            globals memory baseAddress topAddress bytesInWord expression memoryAccess =
          evalPanValueExp structs locals globals memory baseAddress topAddress
            bytesInWord expression memoryAccess)
      (motive3 := fun fields memoryAccess =>
        name ∉ expLocalVars.expLocalVarsFieldList fields →
        evalPanValueExp.evalPanValueFields structs
            (updatePanValueMap locals name replacement) globals memory
            baseAddress topAddress bytesInWord fields memoryAccess =
          evalPanValueExp.evalPanValueFields structs locals globals memory
            baseAddress topAddress bytesInWord fields memoryAccess)
    all_goals
      intros
      simp_all [evalPanValueExp, expLocalVars, expLocalVars.expLocalVarsList,
        expLocalVars.expLocalVarsFieldList, updatePanValueMap, beq_iff_eq,
        List.mem_append]
    all_goals
      try simp only [evalPanValueExp.evalPanValueExps,
        evalPanValueExp.evalPanValueFields]
    all_goals
      try rfl
    all_goals
      try (rcases ‹_ ∧ _› with ⟨hhead, htail⟩; simp_all)
    all_goals
      try (intro h; contradiction)
    all_goals
      try (intro h; simp_all)
    all_goals
      try simp only [eq_comm]
  exact hmain expression memoryAccess hname

/-! Cake's `FUPDATE_LIST` applies a sequence of local bindings.  Keeping the
    operation explicit gives the Lean port the same reusable interface as
    Pancake's `eval_distinct_lists_not_affect'` theorem, while avoiding any
    dependence on a particular map representation. -/

def updatePanValueMapList [BEq γ] (values : γ → Option α) :
    List (γ × α) → γ → Option α
  | [] => values
  | (name, value) :: bindings =>
      updatePanValueMapList (updatePanValueMap values name value) bindings

theorem evalPanValueFields_update_local_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq String] [LawfulBEq String]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (name : VarName) (replacement : PanValue α)
    (hname : ∀ field ∈ fields, name ∉ expLocalVars field.2) :
    evalPanValueExp.evalPanValueFields structs
        (updatePanValueMap locals name replacement) globals memory
        baseAddress topAddress bytesInWord fields memoryAccess =
      evalPanValueExp.evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields memoryAccess := by
  induction fields with
  | nil => simp [evalPanValueExp.evalPanValueFields]
  | cons field fields ih =>
      rcases field with ⟨fieldName, expression⟩
      have hexpression := evalPanValueExp_update_local_not_mem structs locals
        globals memory baseAddress topAddress bytesInWord expression memoryAccess
        name replacement (hname (fieldName, expression) (by simp))
      have hfields := ih (fun field hmem => hname field (by simp [hmem]))
      simp only [evalPanValueExp.evalPanValueFields]
      rw [hexpression, hfields]

theorem evalPanValueExp_nStruct_update_local_not_mem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq String] [LawfulBEq String]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (structName : StructName)
    (fields : List (FieldName × Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (name : VarName) (replacement : PanValue α)
    (hname : ∀ field ∈ fields, name ∉ expLocalVars field.2) :
    evalPanValueExp structs (updatePanValueMap locals name replacement)
        globals memory baseAddress topAddress bytesInWord
        (.nStruct structName fields) memoryAccess =
      evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord (.nStruct structName fields) memoryAccess := by
  simp only [evalPanValueExp]
  rw [evalPanValueFields_update_local_not_mem structs locals globals memory
    baseAddress topAddress bytesInWord fields memoryAccess name replacement hname]

end Flapjack
