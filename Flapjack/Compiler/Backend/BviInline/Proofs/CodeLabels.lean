module

public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels
public import Flapjack.Compiler.Backend.BviInline.Source
import Flapjack.Compiler.Backend.BviInline.Proofs.SourceCorrespondence
public import Flapjack.Misc.Sptree.ToList

@[expose] public section

/-! Code-label preservation for BVI inlining. -/
namespace Flapjack.Compiler.Backend.BviInline.Proofs
open Flapjack.Compiler.Backend.BviProps


/-- Inlining preserves the length of an expression list. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exps_LENGTH"]
theorem inlineExpsLength (cache : Spt (Nat × Bvi.Exp)) (expressions : List Bvi.Exp) :
    (inlineExpsSource cache expressions).length = expressions.length := by
  induction expressions with
  | nil => simp [inlineExpsSource]
  | cons expression rest ih => simp [inlineExpsSource, ih]

/-- Removing ticks preserves the length of an expression list. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_ticks_exps_LENGTH"]
theorem removeTicksExpsLength (expressions : List Bvi.Exp) :
    (removeTicksListSource expressions).length = expressions.length := by
  induction expressions with
  | nil => simp [removeTicksListSource]
  | cons expression rest ih => simp [removeTicksListSource, ih]

/-- Inlining a cons list applies inlining to its head and tail. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exps_CONS"]
theorem inlineExpsCons (cache : Spt (Nat × Bvi.Exp)) (expression : Bvi.Exp) (rest : List Bvi.Exp) :
    inlineExpsSource cache (expression :: rest) =
      inlineExpSource cache expression :: inlineExpsSource cache rest := by
  simp [inlineExpsSource]

/-- Inlining an expression list is pointwise inlining. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exps_MAP"]
theorem inlineExpsMap (cache : Spt (Nat × Bvi.Exp)) (expressions : List Bvi.Exp) :
    inlineExpsSource cache expressions = expressions.map (inlineExpSource cache) := by
  induction expressions with
  | nil => simp [inlineExpsSource]
  | cons expression rest ih => simp [inlineExpsSource, ih]

/-- Inlining commutes with reversing an expression list. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exps_REVERSE"]
theorem inlineExpsReverse (cache : Spt (Nat × Bvi.Exp)) (expressions : List Bvi.Exp) :
    inlineExpsSource cache expressions.reverse = (inlineExpsSource cache expressions).reverse := by
  simp [inlineExpsMap]

/-- Inlining a list of variables leaves it unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exps_MAP_Var"]
theorem inlineExpsMapVar (cache : Spt (Nat × Bvi.Exp)) (names : List Nat) :
    inlineExpsSource cache (names.map Bvi.Exp.var) = names.map Bvi.Exp.var := by
  induction names with
  | nil => simp [inlineExpsSource]
  | cons name rest ih => simp [inlineExpsSource, inlineExpSource, ih]

/-- Inlining generated variables leaves the generated list unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exps_GENLIST_Var"]
theorem inlineExpsGenlistVar (cache : Spt (Nat × Bvi.Exp)) (n : Nat) :
    inlineExpsSource cache ((List.range n).map Bvi.Exp.var) = (List.range n).map Bvi.Exp.var :=
  inlineExpsMapVar cache (List.range n)

/-- A wrapper cached by one incremental compilation is used by the next. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "incremental_wrapper_example"]
theorem incrementalWrapperExample : ∃ cache first second,
    compileIncSource .ln [(10, 0, .letCall 0 0 11 [] (.op (.blockOp (.cons 7)) []))] = (cache, first) ∧
    compileIncSource cache [(12, 0, .call 0 (some 10) [] none)] = (cache, second) ∧
    second = [(12, 0, .let [] (.letCall 0 0 11 [] (.op (.blockOp (.cons 7)) [])))] := by
  refine ⟨sptInsert 10 (0, .letCall 0 0 11 [] (.op (.blockOp (.cons 7)) [])) .ln,
    [(10, 0, .letCall 0 0 11 [] (.op (.blockOp (.cons 7)) []))],
    [(12, 0, .let [] (.letCall 0 0 11 [] (.op (.blockOp (.cons 7)) [])))], ?_, ?_, rfl⟩
  · simp [compileIncSource, inlineAllSource, inlineExpSource, inlineExpsSource,
      wrapperOk, canonicalWrapper, matchesVariables, removeTicksSource, removeTicksListSource]
  · simp [compileIncSource, inlineAllSource, inlineExpSource, inlineExpsSource,
      wrapperOk, canonicalWrapper, removeTicksSource, removeTicksListSource,
      mkTick, sptLookup_sptInsert_same]

/-- A canonical wrapper has exactly the original worker and variable-list shape. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "canonical_wrapper_thm"]
theorem canonicalWrapper_iff (name arity : Nat) (body : Bvi.Exp) :
    canonicalWrapper name arity body = true ↔
      ∃ rets ticks worker tag, worker ≠ name ∧
        body = .letCall rets ticks worker ((List.range arity).map Bvi.Exp.var)
          (.op (.blockOp (.cons tag)) (((List.range rets).map Bvi.Exp.var).reverse)) := by
  cases body with
  | letCall rets ticks worker args continuation =>
    cases continuation with
    | op op values =>
      cases op with
      | blockOp block =>
        cases block with
        | cons tag => simp [canonicalWrapper, matchesVariables_eq_true_iff, List.map_reverse, and_assoc]
        | _ => simp [canonicalWrapper]
      | _ => simp [canonicalWrapper]
    | _ => simp [canonicalWrapper]
  | _ => simp [canonicalWrapper]



/-- Inlining leaves every eligible wrapper unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "wrapper_ok_inline_exp"]
theorem wrapperOk_inlineExp (name arity : Nat) (body : Bvi.Exp) (cache : Spt (Nat × Bvi.Exp))
    (eligible : wrapperOk name arity body = true) : inlineExpSource cache body = body := by
  have canonical : canonicalWrapper name arity body = true := eligible
  obtain ⟨rets, ticks, worker, tag, _, rfl⟩ := (canonicalWrapper_iff name arity body).1 canonical
  simp [inlineExpSource, inlineExpsReverse, inlineExpsGenlistVar]

mutual
private theorem tickLabels (e : Bvi.Exp) :
    getCodeLabels (removeTicksSource e) = getCodeLabels e := by
  cases e with
  | var n => simp only [removeTicksSource, getCodeLabels]
  | ifThenElse x y z => simp only [removeTicksSource, getCodeLabels, tickLabels x, tickLabels y, tickLabels z]
  | «let» xs y => simp only [removeTicksSource, getCodeLabels, tickListLabels xs, tickLabels y]
  | raise x => simp only [removeTicksSource, getCodeLabels, tickLabels x]
  | tick x => simp only [removeTicksSource, getCodeLabels, tickLabels x]
  | call ticks dest xs handler =>
    cases handler with
    | none => simp only [removeTicksSource, getCodeLabels, tickListLabels xs]
    | some body => simp only [removeTicksSource, getCodeLabels, tickLabels body, tickListLabels xs]
  | force loc n => simp only [removeTicksSource, getCodeLabels]
  | op op xs => simp only [removeTicksSource, getCodeLabels, tickListLabels xs]
  | letCall rets ticks dest xs y => simp only [removeTicksSource, getCodeLabels, tickListLabels xs, tickLabels y]
  | «return» xs => simp only [removeTicksSource, getCodeLabels, tickListLabels xs]
termination_by sizeOf e

private theorem tickListLabels (es : List Bvi.Exp) :
    getCodeLabelsList (removeTicksListSource es) = getCodeLabelsList es := by
  cases es with
  | nil => simp only [removeTicksListSource, getCodeLabelsList]
  | cons e es => simp only [removeTicksListSource, getCodeLabelsList, tickLabels e, tickListLabels es]
termination_by sizeOf es
end

/-- Removing ticks preserves the labels in expressions and expression lists. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_ticks_get_code_labels"]
theorem removeTicks_getCodeLabels :
    (∀ e, getCodeLabels (removeTicksSource e) = getCodeLabels e) ∧
    (∀ es, (⋃₀ (getCodeLabels '' {e | e ∈ removeTicksListSource es})) =
      (⋃₀ (getCodeLabels '' {e | e ∈ es}))) := by
  constructor
  · exact tickLabels
  · intro es
    rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq, tickListLabels]

/-- Removing ticks from program bodies preserves their combined label set. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_ticks_prog_code_labels"]
theorem removeTicksProg_codeLabels {α β : Type} (prog : List (α × β × Bvi.Exp)) :
    (⋃₀ (getCodeLabels '' {e | e ∈ (prog.map (fun (name, arity, body) =>
      (name, arity, removeTicksSource body))).map (fun p => p.2.2)})) =
    (⋃₀ (getCodeLabels '' {e | e ∈ prog.map (fun p => p.2.2)})) := by
  rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
  induction prog with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨name, arity, body⟩
    simp only [List.map_cons, getCodeLabelsList, removeTicks_getCodeLabels.1, ih]

/-- Removing ticks from program bodies preserves program keys. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "MAP_FST_remove_ticks_prog"]
theorem removeTicksProg_mapFst {α β : Type} (prog : List (α × β × Bvi.Exp)) :
    (prog.map (fun (name, arity, body) => (name, arity, removeTicksSource body))).map Prod.fst =
      prog.map Prod.fst := by
  induction prog with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨name, arity, body⟩; simp [ih]

/-- Incremental compilation preserves the inlined program's labels through
tick removal. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "compile_inc_code_labels"]
theorem compileInc_codeLabels (cs cs1 : Spt (Nat × Bvi.Exp)) (prog prog1 : List (Nat × Nat × Bvi.Exp))
    (compiled : compileIncSource cs prog = (cs1, prog1)) :
    (⋃₀ (getCodeLabels '' {e | e ∈ prog1.map (fun p => p.2.2)})) =
    (⋃₀ (getCodeLabels '' {e | e ∈ (inlineAllSource cs prog).2.map (fun p => p.2.2)})) := by
  rcases h : inlineAllSource cs prog with ⟨cache, out⟩
  simp only [compileIncSource, h, Prod.mk.injEq] at compiled
  rcases compiled with ⟨rfl, rfl⟩
  exact removeTicksProg_codeLabels out

/-- Inlining preserves the ordered program keys. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_all_MAP_FST"]
theorem inlineAll_mapFst (cs : Spt (Nat × Bvi.Exp)) (prog : List (Nat × Nat × Bvi.Exp)) :
    (inlineAllSource cs prog).2.map Prod.fst = prog.map Prod.fst := by
  induction prog generalizing cs with
  | nil => simp [inlineAllSource]
  | cons entry rest ih =>
    rcases entry with ⟨name, arity, body⟩
    simp [inlineAllSource, ih]

/-- Incremental compilation preserves the ordered program keys. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "compile_inc_MAP_FST"]
theorem compileInc_mapFst (cs cs1 : Spt (Nat × Bvi.Exp)) (prog prog1 : List (Nat × Nat × Bvi.Exp))
    (compiled : compileIncSource cs prog = (cs1, prog1)) :
    prog1.map Prod.fst = prog.map Prod.fst := by
  rcases h : inlineAllSource cs prog with ⟨cache, out⟩
  have names := inlineAll_mapFst cs prog
  simp only [h] at names
  simp only [compileIncSource, h, Prod.mk.injEq] at compiled
  rcases compiled with ⟨rfl, rfl⟩
  rw [removeTicksProg_mapFst, names]

/-- Incremental compilation preserves distinct program keys. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "compile_inc_ALL_DISTINCT"]
theorem compileInc_allDistinct (cs cs1 : Spt (Nat × Bvi.Exp))
    (prog prog1 : List (Nat × Nat × Bvi.Exp))
    (premises : compileIncSource cs prog = (cs1, prog1) ∧ (prog.map Prod.fst).Nodup) :
    (prog1.map Prod.fst).Nodup := by
  rw [compileInc_mapFst cs cs1 prog prog1 premises.1]
  exact premises.2

/-- Labels present in cached inliner bodies. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "cache_code_labels_def"]
def cacheCodeLabels (cs : Spt (Nat × Bvi.Exp)) : Set Nat :=
  ⋃₀ ((fun entry => getCodeLabels entry.2) '' {entry | entry ∈ sptToList cs})

/-- A cached body's labels belong to the cache-label set. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "lookup_cache_code_labels"]
theorem lookup_cacheCodeLabels (n arity : Nat) (body : Bvi.Exp) (cs : Spt (Nat × Bvi.Exp))
    (found : sptLookup n cs = some (arity, body)) : getCodeLabels body ⊆ cacheCodeLabels cs := by
  intro label h
  apply Set.mem_sUnion.mpr
  exact ⟨getCodeLabels body, ⟨(arity, body), (sptMemToList _ _).2 ⟨n, found⟩, rfl⟩, h⟩

/-- Inserting a cached body adds only its labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "cache_code_labels_insert"]
theorem cacheCodeLabels_insert (name arity : Nat) (body : Bvi.Exp) (cs : Spt (Nat × Bvi.Exp)) :
    cacheCodeLabels (sptInsert name (arity, body) cs) ⊆ getCodeLabels body ∪ cacheCodeLabels cs := by
  intro label h
  obtain ⟨_, ⟨value, member, rfl⟩, h⟩ := Set.mem_sUnion.mp h
  obtain ⟨key, found⟩ := (sptMemToList _ _).1 member
  by_cases same : key = name
  · subst key
    rw [sptLookup_sptInsert_same] at found
    cases found
    exact Or.inl h
  · rw [sptLookup_sptInsert_ne name key (arity, body) cs same] at found
    exact Or.inr (lookup_cacheCodeLabels key value.1 value.2 cs found h)

/-- Adding ticks does not change code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "bvi_mk_tick_get_code_labels"]
theorem mkTick_getCodeLabels (n : Nat) (e : Bvi.Exp) : getCodeLabels (mkTick n e) = getCodeLabels e := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [mkTick, getCodeLabels] using ih

mutual
private theorem inlineSing_labels (cs : Spt (Nat × Bvi.Exp)) (e : Bvi.Exp) :
    getCodeLabels (inlineExpSource cs e) ⊆ getCodeLabels e ∪ cacheCodeLabels cs := by
  cases e with
  | var n => simp [inlineExpSource.eq_1, getCodeLabels]
  | force loc n => simp [inlineExpSource.eq_9, getCodeLabels]
  | ifThenElse x y z =>
    have hx := inlineSing_labels cs x
    have hy := inlineSing_labels cs y
    have hz := inlineSing_labels cs z
    simp only [inlineExpSource.eq_2, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; specialize hz label; aesop
  | «let» xs body =>
    have hx := inlineList_labels cs xs
    have hy := inlineSing_labels cs body
    simp only [inlineExpSource.eq_3, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; aesop
  | raise x => simpa [inlineExpSource.eq_4, getCodeLabels] using inlineSing_labels cs x
  | tick x => simpa [inlineExpSource.eq_5, getCodeLabels] using inlineSing_labels cs x
  | op op xs =>
    have hx := inlineList_labels cs xs
    simp only [inlineExpSource.eq_10, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; aesop
  | «return» xs => simpa [inlineExpSource.eq_12, getCodeLabels] using inlineList_labels cs xs
  | letCall rets ticks dest xs body =>
    have hx := inlineList_labels cs xs
    have hy := inlineSing_labels cs body
    simp only [inlineExpSource.eq_11, getCodeLabels, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; aesop
  | call ticks dest xs handler =>
    have hx := inlineList_labels cs xs
    cases handler with
    | some body =>
      have hy := inlineSing_labels cs body
      simp only [inlineExpSource.eq_6, getCodeLabels, Set.subset_def, Set.mem_union] at *
      intro label; specialize hx label; specialize hy label; aesop
    | none =>
      cases dest with
      | none =>
        simp only [inlineExpSource.eq_7, getCodeLabels, Set.subset_def, Set.mem_union,
          Set.mem_empty_iff_false, false_or] at *
        intro label; specialize hx label; aesop
      | some name =>
        cases found : sptLookup name cs with
        | none =>
          simp only [inlineExpSource.eq_8, found, getCodeLabels, Set.subset_def, Set.mem_union,
            Set.mem_empty_iff_false, or_false] at *
          intro label; specialize hx label; aesop
        | some pair =>
          obtain ⟨arity, body⟩ := pair
          have hb := lookup_cacheCodeLabels name arity body cs found
          simp only [inlineExpSource.eq_8, found]
          split
          · simp only [getCodeLabels, mkTick_getCodeLabels, Set.subset_def, Set.mem_union] at *
            intro label; specialize hx label; specialize hb label; aesop
          · simp only [getCodeLabels, Set.subset_def, Set.mem_union,
              Set.mem_empty_iff_false, or_false] at *
            intro label; specialize hx label; aesop
termination_by sizeOf e

private theorem inlineList_labels (cs : Spt (Nat × Bvi.Exp)) (xs : List Bvi.Exp) :
    getCodeLabelsList (inlineExpsSource cs xs) ⊆ getCodeLabelsList xs ∪ cacheCodeLabels cs := by
  cases xs with
  | nil => simp [inlineExpsSource.eq_1, getCodeLabelsList]
  | cons x xs =>
    have hx := inlineSing_labels cs x
    have hy := inlineList_labels cs xs
    simp only [inlineExpsSource.eq_2, getCodeLabelsList, Set.subset_def, Set.mem_union] at *
    intro label; specialize hx label; specialize hy label; aesop
termination_by sizeOf xs
end

/-- Inlining introduces only labels already in the expression or cache. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_exp_code_labels"]
theorem inlineExp_codeLabels :
    (∀ cs e, getCodeLabels (inlineExpSource cs e) ⊆ getCodeLabels e ∪ cacheCodeLabels cs) ∧
    (∀ cs es, (⋃₀ (getCodeLabels '' {e | e ∈ inlineExpsSource cs es})) ⊆
      (⋃₀ (getCodeLabels '' {e | e ∈ es})) ∪ cacheCodeLabels cs) := by
  constructor
  · exact inlineSing_labels
  · intro cs es
    rw [← getCodeLabelsList_eq, ← getCodeLabelsList_eq]
    exact inlineList_labels cs es

private def progLabels (p : List (Nat × Nat × Bvi.Exp)) : Set Nat :=
  ⋃₀ (getCodeLabels '' {e | e ∈ p.map (fun q => q.2.2)})

private theorem progLabels_cons (entry : Nat × Nat × Bvi.Exp) (p : List (Nat × Nat × Bvi.Exp)) :
    progLabels (entry :: p) = getCodeLabels entry.2.2 ∪ progLabels p := by
  ext label
  simp [progLabels]

/-- Inlining a program introduces only labels already in the program or cache. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_all_code_labels"]
theorem inlineAll_codeLabels : ∀ cs prog,
    (⋃₀ (getCodeLabels '' {e | e ∈ (inlineAllSource cs prog).2.map (fun q => q.2.2)})) ⊆
      (⋃₀ (getCodeLabels '' {e | e ∈ prog.map (fun q => q.2.2)})) ∪ cacheCodeLabels cs := by
  intro cs prog
  change progLabels (inlineAllSource cs prog).2 ⊆ progLabels prog ∪ cacheCodeLabels cs
  induction prog generalizing cs with
  | nil => simp [inlineAllSource, progLabels]
  | cons entry rest ih =>
    rcases entry with ⟨name, arity, body⟩
    let converted := inlineExpSource cs body
    let updated := if wrapperOk name arity converted then sptInsert name (arity, converted) cs else cs
    have bodyBound := inlineExp_codeLabels.1 cs body
    have cacheBound : cacheCodeLabels updated ⊆ getCodeLabels body ∪ cacheCodeLabels cs := by
      dsimp [updated]
      split
      · exact Set.Subset.trans (cacheCodeLabels_insert name arity converted cs)
          (by
            intro label h
            rcases h with h | h
            · exact bodyBound h
            · exact Or.inr h)
      · exact Set.subset_union_right
    have restBound := ih updated
    simp only [inlineAllSource]
    change progLabels ((name, arity, converted) :: (inlineAllSource updated rest).2) ⊆
      progLabels ((name, arity, body) :: rest) ∪ cacheCodeLabels cs
    simp only [progLabels_cons, Set.subset_def, Set.mem_union] at *
    intro label member
    rcases member with inBody | inRest
    · rcases bodyBound label inBody with src | cached
      · exact Or.inl (Or.inl src)
      · exact Or.inr cached
    · rcases restBound label inRest with src | cached
      · exact Or.inl (Or.inr src)
      · rcases cacheBound label cached with src | cached
        · exact Or.inl (Or.inl src)
        · exact Or.inr cached


/-- Whole-program inlining introduces no new code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "compile_prog_code_labels"]
theorem compileProg_codeLabels (prog prog1 : List (Nat × Nat × Bvi.Exp)) (cs1 : Spt (Nat × Bvi.Exp))
    (compiled : compileProgSource prog = (cs1, prog1)) :
    (⋃₀ (getCodeLabels '' {e | e ∈ prog1.map (fun q => q.2.2)})) ⊆
      (⋃₀ (getCodeLabels '' {e | e ∈ prog.map (fun q => q.2.2)})) := by
  have h := compileInc_codeLabels .ln cs1 prog prog1 compiled
  have bound := inlineAll_codeLabels .ln prog
  rw [h]
  simpa [cacheCodeLabels, sptToList, sptToListA] using bound

end Flapjack.Compiler.Backend.BviInline.Proofs
