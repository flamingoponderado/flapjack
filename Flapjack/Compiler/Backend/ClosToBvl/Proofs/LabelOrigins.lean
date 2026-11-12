module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Accumulator
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RecursiveInstalled
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! Origins of labels in closure-to-BVL program conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Recursive-group construction prepends the reserved labels in reverse
order, while leaving the input accumulator suffix intact. -/
theorem buildAux_label_list (entries : List (Nat × Bvl.Exp)) (start : Nat) (aux : List (Nat × Nat × Bvl.Exp)) :
    (buildAux start entries aux).2.map Prod.fst =
      ((List.range entries.length).map (fun index => start + 2 * index)).reverse ++ aux.map Prod.fst := by
  induction entries generalizing start aux with
  | nil => simp [buildAux]
  | cons first rest ih =>
    obtain ⟨arity, body⟩ := first
    simp only [buildAux, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.reverse_cons, Nat.mul_zero, Nat.add_zero, List.append_assoc,
      List.singleton_append]
    congr 2
    apply List.map_congr_left
    intro index member
    simp only [Function.comp_def]
    omega

mutual

/-- Compiling an expression prepends its closure labels, shifted by the stub
prefix and in reverse traversal order, to the auxiliary accumulator. -/
theorem compileExp_aux_labels (maxApp : Nat) (expression : ClosLang.Exp) (aux : List (Nat × Nat × Bvl.Exp)) :
    (compileExpHOL maxApp expression aux).2.map Prod.fst =
      ((ClosProps.codeLocationsExp expression).reverse.map (fun location => location + numStubs maxApp)) ++
        aux.map Prod.fst := by
  cases expression with
  | var trace n => simp [compileExpHOL, ClosProps.codeLocationsExp]
  | ifThenElse trace condition yes no =>
    simp [compileExpHOL, ClosProps.codeLocationsExp, compileExp_aux_labels maxApp condition,
      compileExp_aux_labels maxApp yes, compileExp_aux_labels maxApp no, List.reverse_append,
      List.map_append, List.append_assoc]
  | «let» trace bindings body =>
    simp [compileExpHOL, ClosProps.codeLocationsExp, compileExpList_aux_labels maxApp bindings,
      compileExp_aux_labels maxApp body, List.reverse_append, List.map_append, List.append_assoc]
  | raise trace body | tick trace body =>
    simpa [compileExpHOL, ClosProps.codeLocationsExp] using compileExp_aux_labels maxApp body aux
  | handle trace body handler =>
    simp [compileExpHOL, ClosProps.codeLocationsExp, compileExp_aux_labels maxApp body,
      compileExp_aux_labels maxApp handler, List.reverse_append, List.map_append, List.append_assoc]
  | call trace ticks dest args | op trace _ args =>
    simpa [compileExpHOL, ClosProps.codeLocationsExp] using compileExpList_aux_labels maxApp args aux
  | app trace dest function args =>
    simp [compileExpHOL, ClosProps.codeLocationsExp, compileExp_aux_labels maxApp function,
      compileExpList_aux_labels maxApp args, List.reverse_append, List.map_append, List.append_assoc]
  | fn name dest vars arity body =>
    simp [compileExpHOL, ClosProps.codeLocationsExp, compileExp_aux_labels maxApp body,
      List.reverse_append, List.append_assoc]
  | letrec names dest vars functions body =>
    cases functions with
    | nil =>
      simpa [compileExpHOL, ClosProps.codeLocationsExp, ClosProps.codeLocationsFuns] using
        compileExp_aux_labels maxApp body aux
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨arity, function⟩ := first
        simp [compileExpHOL, ClosProps.codeLocationsExp, ClosProps.codeLocationsFuns,
          compileExp_aux_labels maxApp function, compileExp_aux_labels maxApp body,
          List.reverse_append, List.map_append, List.append_assoc]
      | cons second tail =>
        have length : (compileExpFunsHOL maxApp (first :: second :: tail) aux).1.length =
            (first :: second :: tail).length := by
          exact compileExpFuns_length maxApp (first :: second :: tail) aux _ _ (Prod.eta _).symm
        simp [compileExpHOL, ClosProps.codeLocationsExp, compileExpFuns_aux_labels maxApp (first :: second :: tail),
          compileExp_aux_labels maxApp body, buildAux_label_list, List.reverse_append,
          List.map_append, List.append_assoc, length]
        intro index member
        omega
termination_by sizeOf expression
decreasing_by all_goals subst_vars; simp_wf <;> omega

/-- Expression-list compilation emits the same auxiliary labels. -/
theorem compileExpList_aux_labels (maxApp : Nat) (expressions : List ClosLang.Exp) (aux : List (Nat × Nat × Bvl.Exp)) :
    (compileExpListHOL maxApp expressions aux).2.map Prod.fst =
      ((ClosProps.codeLocations expressions).reverse.map (fun location => location + numStubs maxApp)) ++
        aux.map Prod.fst := by
  cases expressions with
  | nil => simp [compileExpListHOL, ClosProps.codeLocations]
  | cons first rest =>
    simp [compileExpListHOL, ClosProps.codeLocations, compileExp_aux_labels maxApp first,
      compileExpList_aux_labels maxApp rest, List.reverse_append, List.map_append, List.append_assoc]
termination_by sizeOf expressions
decreasing_by all_goals (simp_wf; omega)

/-- Recursive bodies emit the same auxiliary labels. -/
theorem compileExpFuns_aux_labels (maxApp : Nat) (functions : List (Nat × ClosLang.Exp)) (aux : List (Nat × Nat × Bvl.Exp)) :
    (compileExpFunsHOL maxApp functions aux).2.map Prod.fst =
      ((ClosProps.codeLocationsFuns functions).reverse.map (fun location => location + numStubs maxApp)) ++
        aux.map Prod.fst := by
  cases functions with
  | nil => simp [compileExpFunsHOL, ClosProps.codeLocationsFuns]
  | cons first rest =>
    obtain ⟨arity, body⟩ := first
    simp [compileExpFunsHOL, ClosProps.codeLocationsFuns, compileExp_aux_labels maxApp body,
      compileExpFuns_aux_labels maxApp rest, List.reverse_append, List.map_append, List.append_assoc]
termination_by sizeOf functions
decreasing_by all_goals (simp_wf; omega)

end

/-- The newly emitted auxiliary labels are the shifted, reversed source
closure locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_code_locs"]
theorem compileExps_codeLocs (maxApp : Nat) (expressions : List ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp) (emitted : List (Nat × Nat × Bvl.Exp)) :
    compileExpsHOL maxApp expressions aux = (compiled, emitted ++ aux) →
      emitted.map Prod.fst =
        (ClosProps.codeLocations expressions).reverse.map (fun location => numStubs maxApp + location) := by
  intro run
  have labels := compileExpList_aux_labels maxApp expressions aux
  rw [← compileExps_eq_list, run, List.map_append] at labels
  simp only [List.append_cancel_right_eq] at labels
  simpa [Nat.add_comm] using labels

/-- Program conversion emits shifted entry labels followed by the shifted,
reversed closure locations of the source bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_prog_code_locs"]
theorem compileProg_codeLocs (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp)) :
    (compileProgExpsHOL maxApp program).map Prod.fst =
      program.map (fun entry => numStubs maxApp + entry.1) ++
        ((ClosProps.codeLocations (program.map (fun (_, _, body) => body))).reverse.map
          (fun location => numStubs maxApp + location)) := by
  cases run : compileExpsHOL maxApp (program.map (fun (_, _, body) => body)) [] with
  | mk compiled emitted =>
    have lengthEq := compileExps_length maxApp (program.map (fun (_, _, body) => body)) [] compiled emitted run
    have labels := compileExps_codeLocs maxApp (program.map (fun (_, _, body) => body)) [] compiled emitted
      (by simpa using run)
    simp only [List.length_map] at lengthEq
    simp only [compileProgExpsHOL, run, List.map_append]
    have zipped := congrArg (List.map (fun entry : Nat × Nat × ClosLang.Exp => entry.1 + numStubs maxApp))
      (List.map_fst_zip (l₁ := program) (l₂ := compiled) (Nat.le_of_eq lengthEq.symm))
    simp only [List.map_map, Function.comp_def] at zipped ⊢
    rw [zipped, labels]
    simp [Nat.add_comm]

/-- Program conversion labels are the shifted source entry and closure labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "MAP_FST_compile_prog"]
theorem map_fst_compileProg (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp)) :
    (compileProgExpsHOL maxApp program).map Prod.fst =
      (program.map Prod.fst ++
        (ClosProps.codeLocations (program.map (fun entry => entry.2.2))).reverse).map
          (fun label => numStubs maxApp + label) := by
  simpa [List.map_append, List.map_map, Function.comp_def] using compileProg_codeLocs maxApp program

/-- Shifting a set bounded by a difference stays below the original bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "IMAGE_ADD_SUBSET_count"]
theorem image_add_subset_count (A : Set Nat) (n m : Nat)
    (h : A ⊆ {x | x < n - m}) :
    Set.image (fun x => m + x) A ⊆ {x | x < n} := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have bound := h hy
  change y < n - m at bound
  change m + y < n
  omega

end Flapjack.Compiler.Backend.ClosToBvl
