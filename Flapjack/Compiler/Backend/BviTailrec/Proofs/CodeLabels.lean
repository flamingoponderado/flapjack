module

public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation
public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels

@[expose] public section

/-! Source-shaped label accounting for the BVI tail-recursion pass. -/
namespace Flapjack.Compiler.Backend.BviTailrec.Proofs

private theorem freshCoverage (code : List (Nat × Nat × Bvi.Exp)) (next k : Nat)
    (bounded : next + k * bvlToBviNamespaces < (compileEachSource next code).1) :
    next + k * bvlToBviNamespaces ∈ (compileEachSource next code).2.map Prod.fst := by
  induction code generalizing next k with
  | nil => simp [compileEachSource] at bounded; omega
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases compiled : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last output =>
        simp only [compileEachSource, compiled, tail] at bounded ⊢
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (by simpa [tail] using ih next k (by simpa [tail] using bounded))
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + bvlToBviNamespaces) rest with
      | mk last output =>
        simp only [compileEachSource, compiled, tail] at bounded ⊢
        simp only [List.map_cons, List.mem_cons]
        cases k with
        | zero => simp
        | succ k =>
          have same : next + (k + 1) * bvlToBviNamespaces =
              (next + bvlToBviNamespaces) + k * bvlToBviNamespaces := by
            simp only [Nat.add_mul, Nat.one_mul]; omega
          right; right
          rw [same] at bounded ⊢
          simpa [tail] using ih (next + bvlToBviNamespaces) k (by simpa [tail] using bounded)

/-- The emitted function labels are exactly the original labels plus the
worker labels allocated in the traversed interval. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_each_labels"]
theorem compileEach_labels (next1 : Nat) (code1 : List (Nat × Nat × Bvi.Exp))
    (next2 : Nat) (code2 : List (Nat × Nat × Bvi.Exp))
    (compiled : compileEachSource next1 code1 = (next2, code2)) :
    ({label | label ∈ code1.map Prod.fst} ∪
      {label | ∃ k, label = next1 + k * bvlToBviNamespaces ∧ next1 + k * bvlToBviNamespaces < next2}) =
      {label | label ∈ code2.map Prod.fst} ∧ next1 ≤ next2 := by
  have mono := compileEachSource_next_mono next1 code1
  simp only [compiled] at mono
  constructor
  · ext label
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro member
      rcases member with original | ⟨k, rfl, bound⟩
      · have h := compileEachSource_preserves_labels code1 next1 label original
        simpa only [compiled] using h
      · have h := freshCoverage code1 next1 k (by simpa only [compiled] using bound)
        simpa only [compiled] using h
    · intro member
      have h := compileEachSource_mem code1 next1 label (by simpa only [compiled] using member)
      simp only [compiled] at h
      rcases h with original | ⟨lo, hi, k, eq⟩
      · exact Or.inl original
      · exact Or.inr ⟨k, eq, by simpa [eq] using hi⟩
  · obtain ⟨k, h⟩ := mono
    omega

/-- Function-list compilation retains every original label. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_each_keeps_names"]
theorem compileEach_keepsNames (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileEachSource next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  have h := compileEachSource_preserves_labels xs next x assumptions.2
  simpa only [assumptions.1] using h

/-- The whole-program tail-recursion pass retains every original label. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_prog_keeps_names"]
theorem compileProg_keepsNames (enabled : Bool) (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileProgSource enabled next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  cases enabled with
  | false =>
    simp only [compileProgSource, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at assumptions
    simpa [← assumptions.1.2] using assumptions.2
  | true =>
    simp only [compileProgSource, ↓reduceIte] at assumptions
    exact compileEach_keepsNames next xs next' ys x assumptions

/-- The wrapper refers exactly to labels in its identity and body. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "get_code_labels_let_wrap"]
theorem letWrap_getCodeLabels (arity : Nat) (identity body : Bvi.Exp) :
    BviProps.getCodeLabels (letWrap arity identity body) = BviProps.getCodeLabels identity ∪ BviProps.getCodeLabels body := by
  ext label
  simp [letWrap, BviProps.getCodeLabels, BviProps.getCodeLabelsList_eq]

open Flapjack.Compiler.Backend.BviProps

private theorem applyOp_labels (op : AssocOp) (x y : Bvi.Exp) :
    getCodeLabels (applyOp op x y) = getCodeLabels x ∪ getCodeLabels y := by
  cases op <;> simp [applyOp, toOp, getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]

private theorem sourceDispatch_labels (loc next acc : Nat) (op : AssocOp)
    (ctx : List ValueType) (e : Bvi.Exp) :
    getCodeLabels (sourceDispatch loc next op acc ctx e).2 ⊆ insert next (getCodeLabels e) := by
  cases checked : checkOp ctx op loc e with
  | none =>
    simp [sourceDispatch, checked, applyOp_labels, getCodeLabels]
  | some result =>
    obtain ⟨pure, ticks, args, termOk, eq, nonzero, original⟩ :=
      checkOp_candidate_call ctx op loc e result checked
    subst result
    cases op <;> simp_all [sourceDispatch, opBinArgs, opEq, applyOp, toOp,
      getBinArgs, argsFrom, pushCall, getCodeLabels, getCodeLabelsList, getCodeLabelsList_eq,
      ClosLang.assignGetCodeLabel, Set.subset_def]
    all_goals try (rcases original with rfl | rfl <;>
      simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel])
    all_goals try simp only [getCodeLabelsList_eq] at *
    all_goals aesop

private theorem rewrite_labels (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (e : Bvi.Exp) :
    getCodeLabels (rewriteSource loc next op acc ctx e).2 ⊆ insert next (getCodeLabels e) := by
  cases e with
  | var n => simp [rewriteSource.eq_def, getCodeLabels]
  | force l n => simp [rewriteSource.eq_def, getCodeLabels]
  | ifThenElse cond yes no =>
    let ctx' := ((scanExpr ctx loc [cond]).headD (ctx, .any, false, none)).1
    rcases hy : rewriteSource loc next op acc ctx' yes with ⟨ry, y⟩
    rcases hn : rewriteSource loc next op acc ctx' no with ⟨rn, n⟩
    have iy := rewrite_labels loc next op acc ctx' yes
    have inn := rewrite_labels loc next op acc ctx' no
    simp only [hy] at iy
    simp only [hn] at inn
    rw [rewriteSource.eq_def]
    dsimp only
    change getCodeLabels (.ifThenElse cond
      (if (rewriteSource loc next op acc ctx' yes).1 then (rewriteSource loc next op acc ctx' yes).2 else applyOp op (.var acc) yes)
      (if (rewriteSource loc next op acc ctx' no).1 then (rewriteSource loc next op acc ctx' no).2 else applyOp op (.var acc) no)) ⊆ _
    rw [hy, hn]
    cases ry <;> cases rn <;>
      simp only [Bool.false_eq_true, ↓reduceIte, getCodeLabels,
        applyOp_labels, Set.empty_union, Set.subset_def, Set.mem_union, Set.mem_insert_iff] at * <;>
      intro label member <;> specialize iy label <;> specialize inn label <;> aesop
  | «let» xs body =>
    let scans := scanExpr ctx loc xs
    let tys := scans.map fun q => q.2.1
    let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
    rcases h : rewriteSource loc next op (acc + xs.length) (tys ++ last) body with ⟨flag, out⟩
    have ih := rewrite_labels loc next op (acc + xs.length) (tys ++ last) body
    simp only [h] at ih
    rw [rewriteSource.eq_def]
    dsimp only
    change getCodeLabels (.let xs (rewriteSource loc next op (acc + xs.length) (tys ++ last) body).2) ⊆ _
    rw [h]
    change getCodeLabels (.let xs out) ⊆ insert next (getCodeLabels (.let xs body))
    simp only [getCodeLabels, Set.subset_def, Set.mem_union, Set.mem_insert_iff] at *
    intro label member
    rcases member with hxs | hbody
    · exact Or.inr (Or.inl hxs)
    · rcases ih label hbody with hnext | hbody
      · exact Or.inl hnext
      · exact Or.inr (Or.inr hbody)
  | tick x =>
    rcases h : rewriteSource loc next op acc ctx x with ⟨flag, out⟩
    have ih := rewrite_labels loc next op acc ctx x
    simp only [h] at ih
    rw [rewriteSource.eq_def]
    dsimp only
    rw [h]
    simpa only [getCodeLabels] using ih
  | raise x => simpa only [rewriteSource.eq_def] using sourceDispatch_labels loc next acc op ctx (.raise x)
  | call ticks dest args handler => simpa only [rewriteSource.eq_def] using sourceDispatch_labels loc next acc op ctx (.call ticks dest args handler)
  | op actual xs => simpa only [rewriteSource.eq_def] using sourceDispatch_labels loc next acc op ctx (.op actual xs)
  | letCall rets ticks dest args body => simpa only [rewriteSource.eq_def] using sourceDispatch_labels loc next acc op ctx (.letCall rets ticks dest args body)
  | «return» xs => simpa only [rewriteSource.eq_def] using sourceDispatch_labels loc next acc op ctx (.return xs)
termination_by sizeOf e

/-- Rewriting introduces at most the fresh worker label. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "get_code_labels_rewrite"]
theorem rewrite_getCodeLabels (loc next : Nat) (op : AssocOp) (arity : Nat) (foo : List ValueType)
    (exp : Bvi.Exp) (bar : Bool) (exp_opt : Bvi.Exp)
    (compiled : rewriteSource loc next op arity foo exp = (bar, exp_opt)) :
    getCodeLabels exp_opt ⊆ insert next (getCodeLabels exp) := by
  have h := rewrite_labels loc next op arity foo exp
  simpa only [compiled] using h

/-- Compiling an expression introduces at most the fresh worker label. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "get_code_labels_compile_exp"]
theorem compileExp_getCodeLabels (loc next arity : Nat) (exp exp_aux exp_opt : Bvi.Exp)
    (compiled : compileExpSource loc next arity exp = some (exp_aux, exp_opt)) :
    getCodeLabels exp_aux ∪ getCodeLabels exp_opt ⊆ insert next (getCodeLabels exp) := by
  cases check : checkExpOriginal loc arity exp with
  | none => simp [compileExpSource, check] at compiled
  | some op =>
    rcases rwResult : rewriteSource loc next op arity (List.replicate arity .any) exp with ⟨flag, worker⟩
    have bound := rewrite_getCodeLabels loc next op arity (List.replicate arity .any) exp flag worker rwResult
    simp [compileExpSource, check, rwResult, Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl, rfl⟩
    rw [letWrap_getCodeLabels]
    have noLabels : getCodeLabels (identity op) = ∅ := by
      cases op <;> simp [identity, getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]
    simpa [noLabels] using bound

private def progLabels (p : List (Nat × Nat × Bvi.Exp)) : Set Nat :=
  ⋃₀ (getCodeLabels '' {e | e ∈ p.map (fun q => q.2.2)})
private def freshLabels (start finish : Nat) : Set Nat :=
  {label | ∃ k, label = start + k * bvlToBviNamespaces ∧ start + k * bvlToBviNamespaces < finish}
private theorem progLabels_cons (name arity : Nat) (body : Bvi.Exp) (tail : List (Nat × Nat × Bvi.Exp)) :
    progLabels ((name, arity, body) :: tail) = getCodeLabels body ∪ progLabels tail := by
  ext label; simp [progLabels]
private theorem freshLabels_step (start finish : Nat) :
    freshLabels (start + bvlToBviNamespaces) finish ⊆ freshLabels start finish := by
  intro label ⟨k, eq, bound⟩
  refine ⟨k + 1, ?_, ?_⟩ <;> simp only [Nat.add_mul, Nat.one_mul] <;> omega

/-- Function-list compilation preserves closure under an allowed label set. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_each_good_code_labels"]
theorem compileEach_goodCodeLabels (n : Nat) (c : List (Nat × Nat × Bvi.Exp)) (n2 : Nat)
    (c2 : List (Nat × Nat × Bvi.Exp)) (all : Set Nat)
    (assumptions : compileEachSource n c = (n2, c2) ∧
      (⋃₀ (getCodeLabels '' {e | e ∈ c.map (fun q => q.2.2)})) ⊆ all ∧
      {label | ∃ k, label = n + k * bvlToBviNamespaces ∧ n + k * bvlToBviNamespaces < n2} ⊆ all) :
    (⋃₀ (getCodeLabels '' {e | e ∈ c2.map (fun q => q.2.2)})) ⊆ all := by
  change compileEachSource n c = (n2, c2) ∧ progLabels c ⊆ all ∧ freshLabels n n2 ⊆ all at assumptions
  change progLabels c2 ⊆ all
  induction c generalizing n n2 c2 with
  | nil =>
    simp [compileEachSource, Prod.mk.injEq] at assumptions
    obtain ⟨⟨rfl, rfl⟩, _, _⟩ := assumptions
    simp [progLabels]
  | cons entry rest ih =>
    rcases entry with ⟨loc, arity, body⟩
    cases decision : compileExpSource loc n arity body with
    | none =>
      rcases tail : compileEachSource n rest with ⟨last, out⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, old, fresh⟩
      simp only [progLabels_cons, Set.union_subset_iff] at old ⊢
      exact ⟨old.1, ih n last out ⟨tail, old.2, fresh⟩⟩
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      rcases tail : compileEachSource (n + bvlToBviNamespaces) rest with ⟨last, out⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, old, fresh⟩
      have tailMono := (compileEach_labels (n + bvlToBviNamespaces) rest last out tail).2
      have pos : 0 < bvlToBviNamespaces := by decide
      have freshNow : n ∈ all := by
        apply fresh
        exact ⟨0, by simp, by omega⟩
      have tailFresh : freshLabels (n + bvlToBviNamespaces) last ⊆ all :=
        Set.Subset.trans (freshLabels_step n last) fresh
      have bodyBound := compileExp_getCodeLabels loc n arity body wrapper worker decision
      simp only [progLabels_cons, Set.union_subset_iff] at old ⊢
      have generated : getCodeLabels wrapper ∪ getCodeLabels worker ⊆ all := by
        intro label h
        rcases bodyBound h with eq | bodyLabel
        · exact eq ▸ freshNow
        · exact old.1 bodyLabel
      have both := Set.union_subset_iff.mp generated
      exact ⟨both.1, both.2, ih (n + bvlToBviNamespaces) last out ⟨tail, old.2, tailFresh⟩⟩

/-- The whole-program pass preserves closure under an allowed label set. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_prog_good_code_labels"]
theorem compileProg_goodCodeLabels (b : Bool) (n : Nat) (c : List (Nat × Nat × Bvi.Exp)) (n2 : Nat)
    (c2 : List (Nat × Nat × Bvi.Exp)) (all : Set Nat)
    (assumptions : compileProgSource b n c = (n2, c2) ∧
      (⋃₀ (getCodeLabels '' {e | e ∈ c.map (fun q => q.2.2)})) ⊆ all ∧
      {label | ∃ k, label = n + k * bvlToBviNamespaces ∧ n + k * bvlToBviNamespaces < n2} ⊆ all) :
    (⋃₀ (getCodeLabels '' {e | e ∈ c2.map (fun q => q.2.2)})) ⊆ all := by
  cases b with
  | false =>
    simp only [compileProgSource, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at assumptions
    simpa only [← assumptions.1.2] using assumptions.2.1
  | true =>
    simp only [compileProgSource, ↓reduceIte] at assumptions
    exact compileEach_goodCodeLabels n c n2 c2 all assumptions

end Flapjack.Compiler.Backend.BviTailrec.Proofs
