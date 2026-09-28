import Flapjack.Pancake.LoopLive

/-!
Exact `loopLang$assigned_vars`, `nested_seq`, and selected loopProps theorem
ports over `HolLoopProg`.  The production LoopProg uses String-backed FFI
names, so declarations in LoopLive.lean remain untagged production analogues.
-/

namespace Flapjack

/-- HOL `loopLang$assigned_vars` over its exact width-indexed program carrier. -/
@[hol "cakeml/pancake/loopLangScript.sml" "assigned_vars_def"
  (words_as_type_indexed_bitvec)]
def holLoopAssignedVars {width : Nat} [NeZero width] :
    HolLoopProg width → List Nat
  | .skip => []
  | .assign name _ => [name]
  | .primitive destinations _ _ => destinations
  | .arith operation =>
      match operation with
      | .longMul left right _ _ => [left, right]
      | .longDiv left right _ _ _ => [left, right]
      | .div destination _ _ => [destination]
  | .load32 _ destination => [destination]
  | .loadByte _ destination => [destination]
  | .seq first second => holLoopAssignedVars first ++ holLoopAssignedVars second
  | .ite _ _ _ thenBranch elseBranch _ =>
      holLoopAssignedVars thenBranch ++ holLoopAssignedVars elseBranch
  | .locValue destination _ => [destination]
  | .shMem _ destination _ => [destination]
  | .mark body => holLoopAssignedVars body
  | .loop _ body _ => holLoopAssignedVars body
  | .call none _ _ _ => []
  | .call (some (returns, _)) _ _ none => returns
  | .call (some (returns, _)) _ _ (some (exception, handler, normal, _)) =>
      returns ++ exception :: holLoopAssignedVars handler ++ holLoopAssignedVars normal
  | _ => []

/-- HOL `loopLang$nested_seq` over the exact program carrier. -/
@[hol "cakeml/pancake/loopLangScript.sml" "nested_seq_def"
  (words_as_type_indexed_bitvec)]
def holLoopNestedSeq {width : Nat} [NeZero width] :
    List (HolLoopProg width) → HolLoopProg width
  | [] => .skip
  | statement :: statements => .seq statement (holLoopNestedSeq statements)

/-- Exact HOL `assigned_vars_seq_split` with the HOL binder order `q`, then
    `p` and the exact `loopLang$prog` carrier. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "assigned_vars_seq_split"
  (words_as_type_indexed_bitvec)]
theorem holAssignedVarsSeqSplit {width : Nat} [NeZero width]
    (q p : HolLoopProg width) :
    holLoopAssignedVars (.seq p q) = holLoopAssignedVars p ++ holLoopAssignedVars q := by
  rfl

/-- Exact HOL `assigned_vars_nested_seq_split` over `HolLoopProg`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml"
  "assigned_vars_nested_seq_split" (words_as_type_indexed_bitvec)]
theorem holAssignedVarsNestedSeqSplit {width : Nat} [NeZero width]
    (p q : List (HolLoopProg width)) :
    holLoopAssignedVars (holLoopNestedSeq (p ++ q)) =
      holLoopAssignedVars (holLoopNestedSeq p) ++
        holLoopAssignedVars (holLoopNestedSeq q) := by
  induction p with
  | nil => simp [holLoopNestedSeq, holLoopAssignedVars]
  | cons statement statements ih =>
      simp [holLoopNestedSeq, holLoopAssignedVars, ih, List.append_assoc]

/-- Exact HOL `assigned_vars_nested_assign`. `List.zipWith` is the Lean
    constructor-for-constructor rendering of HOL `MAP2`; the source premise
    preserves equal list lengths. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml"
  "assigned_vars_nested_assign" (words_as_type_indexed_bitvec)]
theorem holAssignedVarsNestedAssign {width : Nat} [NeZero width]
    (xs : List Nat) (ys : List (HolLoopExp width))
    (hLength : xs.length = ys.length) :
    holLoopAssignedVars
      (holLoopNestedSeq (List.zipWith HolLoopProg.assign xs ys)) = xs := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hLength
  | cons x xs ih =>
      cases ys with
      | nil => simp at hLength
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hLength
          simp [holLoopNestedSeq, holLoopAssignedVars, ih ys hLength]

/-- Exact HOL `assigned_vars_MAPi_Assign`. `List.range les.length` followed by
    `map` is the direct Lean rendering of HOL `GENLIST` at `LENGTH les`; the
    preceding `mapIdx` mirrors HOL `MAPi` exactly. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml"
  "assigned_vars_MAPi_Assign" (words_as_type_indexed_bitvec)]
theorem holAssignedVarsMapiAssign {width : Nat} [NeZero width]
    (les : List (HolLoopExp width)) (offset : Nat) :
    holLoopAssignedVars
      (holLoopNestedSeq
        (les.mapIdx (fun index expression =>
          HolLoopProg.assign (index + offset) expression))) =
      (List.range les.length).map (fun index => index + offset) := by
  induction les generalizing offset with
  | nil => rfl
  | cons expression expressions ih =>
      simp only [List.mapIdx_cons, List.length_cons]
      rw [List.range_succ_eq_map]
      simp [holLoopNestedSeq, holLoopAssignedVars, ih, Nat.add_assoc,
        Nat.add_comm 1 offset]

end Flapjack
