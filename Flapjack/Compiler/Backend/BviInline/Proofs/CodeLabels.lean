module

public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels
public import Flapjack.Compiler.Backend.BviInline.Source

@[expose] public section

/-! Code-label preservation for BVI inlining. -/
namespace Flapjack.Compiler.Backend.BviInline.Proofs
open Flapjack.Compiler.Backend.BviProps

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

end Flapjack.Compiler.Backend.BviInline.Proofs
