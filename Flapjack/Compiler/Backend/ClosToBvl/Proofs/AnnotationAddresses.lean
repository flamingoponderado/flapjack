module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IncrementalAddresses
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
public import Flapjack.Compiler.Backend.ClosAnnotate.Original
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants

@[expose] public section

/-! Closure annotation address preservation for incremental compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- Annotated program bodies all have captured-variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "annotate_compile_every_Fn_vs_SOME"]
theorem annotateCompile_everyFnVarsSome {α : Type} (es : List (α × Nat × ClosLang.Exp)) :
    everyFnVarsSome ((ClosAnnotate.compileSource es).map (fun entry => entry.2.2)) := by
  rw [ClosAnnotate.compileSource_eq]
  induction es with
  | nil => simp [everyFnVarsSome]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    have annotated : everyFnVarsSome (ClosAnnotate.annotateSource arity [body]) := by
      rw [(ClosAnnotate.annotateSource_sing_eq arity body [body]).2]
      exact ClosAnnotate.shiftList_varsSome _ 0 arity .ln
    rw [(ClosAnnotate.annotateSource_sing_eq arity body []).1] at annotated
    simpa [everyFnVarsSome] using And.intro annotated ih

private theorem annotateCompile_codeLocations_sublist {α : Type}
    (xs : List (α × Nat × ClosLang.Exp)) :
    (codeLocations ((ClosAnnotate.compileSource xs).map (fun t => t.2.2))).Sublist
      (codeLocations (xs.map (fun t => t.2.2))) := by
  induction xs with
  | nil => simp [ClosAnnotate.compileSource, codeLocations]
  | cons x xs ih =>
    obtain ⟨name, arity, body⟩ := x
    have head := ClosAnnotate.annotateList_codeLocations_sublist arity [body]
    have eq := ClosAnnotate.annotateSource_sing_eq arity body [body]
    rw [← eq.2, eq.1] at head
    simp only [codeLocations, List.append_nil] at head
    simpa [ClosAnnotate.compileSource_eq, codeLocations] using head.append ih

/-- Annotation preserves the number of source expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "LENGTH_annotate"]
theorem length_annotate (arity : Nat) (xs : List ClosLang.Exp) :
    (ClosAnnotate.annotateSource arity xs).length = xs.length := by
  rw [(ClosAnnotate.annotateSource_sing_eq arity (.var .none 0) xs).2]
  exact ClosAnnotate.annotateList_length arity xs

/-- Annotation leaves a leading integer constant unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "annotate_Op_Const"]
theorem annotate_opConst (arity : Nat) (tr : BackendCommon.Tra) (n : Int)
    (xs : List ClosLang.Exp) :
    ClosAnnotate.annotateSource arity (.op tr (.intOp (.const n)) [] :: xs) =
      .op tr (.intOp (.const n)) [] :: ClosAnnotate.annotateSource arity xs := by
  rw [(ClosAnnotate.annotateSource_sing_eq arity (.var .none 0) _).2,
      (ClosAnnotate.annotateSource_sing_eq arity (.var .none 0) xs).2]
  simp [ClosAnnotate.annotateList, ClosAnnotate.altFreeList, ClosAnnotate.altFreeSing,
    ClosAnnotate.shiftList, ClosAnnotate.shiftSing]

/-- Annotation cannot introduce closure locations or duplicate existing ones
in the bodies of a labelled program. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "annotate_compile_code_locs"]
theorem annotateCompile_codeLocations {α : Type} (xs : List (α × Nat × ClosLang.Exp)) :
    {x | x ∈ codeLocations ((ClosAnnotate.compileSource xs).map (fun t => t.2.2))} ⊆
      {x | x ∈ codeLocations (xs.map (fun t => t.2.2))} ∧
    ((codeLocations (xs.map (fun t => t.2.2))).Nodup →
      (codeLocations ((ClosAnnotate.compileSource xs).map (fun t => t.2.2))).Nodup) := by
  have sub := annotateCompile_codeLocations_sublist xs
  exact ⟨fun _ h => sub.subset h, fun h => sub.nodup h⟩

private theorem extracted_annotate (xs : List ClosLang.Exp) (h : canExtract xs) :
    extractedAddrs (ClosAnnotate.annotateSource 0 xs) = extractedAddrs xs := by
  obtain ⟨tr, n, rest, rfl⟩ := h
  cases rest with
  | nil =>
    have empty : ClosAnnotate.annotateSource 0 [] = [] := by
      rw [(ClosAnnotate.annotateSource_sing_eq 0 (.var .none 0) []).2]
      rfl
    simp [annotate_opConst, extractedAddrs, extractNameSource_eq_extractName, extractName, empty]
  | cons e es =>
    have nonempty : ClosAnnotate.annotateSource 0 (e :: es) ≠ [] := by
      intro empty
      have length := length_annotate 0 (e :: es)
      rw [empty] at length
      simp at length
    simp [annotate_opConst, extractedAddrs, extractNameSource_eq_extractName,
      extractName, length_annotate, nonempty]

/-- Incremental annotation preserves address distinctness and extractability,
and does not introduce required addresses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "annotate_compile_inc_req"]
theorem annotateCompileInc_req (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    canExtract program.1 →
      ((reqCompileIncAddrs [] program).Nodup →
        (reqCompileIncAddrs [] (ClosAnnotate.compileIncSource program)).Nodup) ∧
      canExtract (ClosAnnotate.compileIncSource program).1 ∧
      {x | x ∈ reqCompileIncAddrs [] (ClosAnnotate.compileIncSource program)} ⊆
        {x | x ∈ reqCompileIncAddrs [] program} := by
  obtain ⟨exps, code⟩ := program
  intro extractable
  have exprSub := ClosAnnotate.annotateList_codeLocations_sublist 0 exps
  rw [← (ClosAnnotate.annotateSource_sing_eq 0 (.var .none 0) exps).2] at exprSub
  have codeSub := annotateCompile_codeLocations_sublist code
  have names : (ClosAnnotate.compileSource code).map Prod.fst = code.map Prod.fst := by
    simp [ClosAnnotate.compileSource_eq, List.map_map, Function.comp_def]
  have reqSub : (reqCompileIncAddrs [] (ClosAnnotate.compileIncSource (exps, code))).Sublist
      (reqCompileIncAddrs [] (exps, code)) := by
    simp only [ClosAnnotate.compileIncSource, reqCompileIncAddrs, List.map_nil, List.flatten_nil,
      List.append_nil, extracted_annotate exps extractable, names]
    exact (((List.Sublist.refl _).append exprSub).append (List.Sublist.refl _)).append codeSub
  constructor
  · exact fun distinct => reqSub.nodup distinct
  · constructor
    · obtain ⟨tr, n, rest, rfl⟩ := extractable
      exact ⟨tr, n, ClosAnnotate.annotateSource 0 rest, by
        simp [ClosAnnotate.compileIncSource, annotate_opConst]⟩
    · exact showSubset _ _ (fun _ mem => reqSub.subset mem)

end Flapjack.Compiler.Backend.ClosToBvl
