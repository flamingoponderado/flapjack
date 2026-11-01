import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Accumulator
import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RecursiveInstalled
import Mathlib.Data.List.Nodup

/-! Origins of labels in closure-to-BVL program conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private abbrev Aux := List (Nat × Nat × Bvl.Exp)

/-- Recursive-group construction prepends the reserved labels in reverse
order, while leaving the input accumulator suffix intact. -/
theorem buildAux_label_list (entries : List (Nat × Bvl.Exp)) (start : Nat) (aux : Aux) :
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

/-- Recursive-group construction emits exactly the old labels and the
evenly spaced labels reserved for the group. -/
theorem buildAux_label_iff (entries : List (Nat × Bvl.Exp)) (start : Nat)
    (aux : Aux) (label : Nat) :
    label ∈ (buildAux start entries aux).2.map Prod.fst ↔
      label ∈ aux.map Prod.fst ∨ ∃ index, index < entries.length ∧ label = start + 2 * index := by
  constructor
  · exact buildAux_label_mem entries start aux label
  · intro origin
    cases origin with
    | inl previous =>
      obtain ⟨entry, entryMem, entryLabel⟩ := List.mem_map.mp previous
      obtain ⟨added, equal⟩ := buildAux_acc entries start aux
      apply List.mem_map.mpr
      exact ⟨entry, by rw [equal]; exact List.mem_append_right added entryMem, entryLabel⟩
    | inr generated =>
      obtain ⟨index, bound, rfl⟩ := generated
      have built : buildAux start entries aux =
          ((buildAux start entries aux).1, (buildAux start entries aux).2) := by
        cases buildAux start entries aux
        rfl
      obtain ⟨item, member⟩ := buildAux_mem entries start aux _ _ built index bound
      exact List.mem_map.mpr ⟨(start + 2 * index, item), member, rfl⟩

mutual

/-- Compiling an expression prepends its closure labels, shifted by the stub
prefix and in reverse traversal order, to the auxiliary accumulator. -/
theorem compileExp_aux_labels (maxApp : Nat) (expression : ClosLang.Exp) (aux : Aux) :
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
          cases run : compileExpFunsHOL maxApp (first :: second :: tail) aux with
          | mk compiled finalAux =>
            simpa only [run] using compileExpFuns_length maxApp (first :: second :: tail) aux finalAux compiled run
        simp [compileExpHOL, ClosProps.codeLocationsExp, compileExpFuns_aux_labels maxApp (first :: second :: tail),
          compileExp_aux_labels maxApp body, buildAux_label_list, List.reverse_append,
          List.map_append, List.append_assoc, length]
        intro index member
        omega
termination_by sizeOf expression
decreasing_by all_goals subst_vars; simp_wf <;> omega

/-- Expression-list compilation emits the same auxiliary labels. -/
theorem compileExpList_aux_labels (maxApp : Nat) (expressions : List ClosLang.Exp) (aux : Aux) :
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
theorem compileExpFuns_aux_labels (maxApp : Nat) (functions : List (Nat × ClosLang.Exp)) (aux : Aux) :
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

/-- Zipping one compiled expression per source entry retains exactly the
source entry labels, shifted by the runtime-stub prefix. -/
private theorem zip_entry_labels (offset : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : List Bvl.Exp) (lengthEq : compiled.length = program.length) :
    (((program.zip compiled).map (fun ((loc, arity, _), body) => (loc + offset, arity, body))).map Prod.fst) =
      program.map (fun entry => entry.1 + offset) := by
  induction program generalizing compiled with
  | nil => simp
  | cons first rest ih =>
    cases compiled with
    | nil => simp at lengthEq
    | cons body remaining =>
      obtain ⟨name, arity, expression⟩ := first
      simp only [List.length_cons, Nat.succ.injEq] at lengthEq
      simp [ih remaining lengthEq]

/-- Program conversion's entry labels are precisely its shifted input labels;
all other labels are those generated in its auxiliary accumulator. -/
theorem compileProgHOL_label_origins (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp)) :
    (compileProgHOL maxApp program).map Prod.fst =
      program.map (fun entry => entry.1 + numStubs maxApp) ++
        ((compileExpListHOL maxApp (program.map (fun (_, _, body) => body)) []).2.map Prod.fst) := by
  have lengthEq := compileExpList_length maxApp (program.map (fun (_, _, body) => body)) []
  simp only [List.length_map] at lengthEq
  simp only [compileProgHOL, List.map_append]
  rw [zip_entry_labels (numStubs maxApp) program _ lengthEq]

/-- The same label decomposition holds for the checked converter actually
used by preprocessing. -/
theorem compileProg_checked_label_origins (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : Aux) (run : compileProg? maxApp program = some compiled) :
    compiled.map Prod.fst =
      program.map (fun entry => entry.1 + numStubs maxApp) ++
        ((compileExpListHOL maxApp (program.map (fun (_, _, body) => body)) []).2.map Prod.fst) := by
  have exactRun := compileProg_checked_eq maxApp program
  have equal : compiled = compileProgHOL maxApp program := Option.some.inj (run.symm.trans exactRun)
  rw [equal]
  exact compileProgHOL_label_origins maxApp program

/-- The executed checked converter's complete label list consists of shifted
entry labels followed by shifted, reversed source closure locations. This is
source-shaped proof infrastructure pending HOL carrier and statement review. -/
theorem compileProg_checked_codeLocations (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : Aux) (run : compileProg? maxApp program = some compiled) :
    compiled.map Prod.fst =
      program.map (fun entry => entry.1 + numStubs maxApp) ++
        ((ClosProps.codeLocations (program.map (fun (_, _, body) => body))).reverse.map
          (fun location => location + numStubs maxApp)) := by
  rw [compileProg_checked_label_origins maxApp program compiled run]
  simp [compileExpList_aux_labels]

/-- Every checked program label is at or above the application-stub prefix. -/
theorem compileProg_checked_label_lower (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : Aux) (run : compileProg? maxApp program = some compiled)
    (label : Nat) (member : label ∈ compiled.map Prod.fst) :
    numStubs maxApp ≤ label := by
  rw [compileProg_checked_codeLocations maxApp program compiled run] at member
  simp only [List.mem_append, List.mem_map] at member
  rcases member with ⟨entry, _, equal⟩ | ⟨location, _, equal⟩ <;> omega

/-- Source entry labels and nested locations that are jointly distinct remain
distinct in the checked BVL program. -/
theorem compileProg_checked_nodup_of_source (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : Aux) (run : compileProg? maxApp program = some compiled)
    (sourceDistinct : ((program.map Prod.fst) ++
      ClosProps.codeLocations (program.map (fun (_, _, body) => body))).Nodup) :
    (compiled.map Prod.fst).Nodup := by
  rw [compileProg_checked_codeLocations maxApp program compiled run]
  apply List.Nodup.append
  · have entries := sourceDistinct.of_append_left
    have shifted : ((program.map Prod.fst).map (fun label => label + numStubs maxApp)).Nodup :=
      entries.map (fun _ _ equal => Nat.add_right_cancel equal)
    simpa [List.map_map, Function.comp_def] using shifted
  · have nested := sourceDistinct.of_append_right
    apply List.Nodup.map (fun _ _ equal => Nat.add_right_cancel equal)
    exact List.nodup_reverse.mpr nested
  · intro label entryMember nestedMember
    obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp entryMember
    obtain ⟨location, locationMem, locationEq⟩ := List.mem_map.mp nestedMember
    have sourceEntry : entry.1 ∈ program.map Prod.fst := List.mem_map.mpr ⟨entry, entryMem, rfl⟩
    have sourceNested : location ∈ ClosProps.codeLocations (program.map (fun (_, _, body) => body)) := by
      simpa using locationMem
    have equal : entry.1 = location := by omega
    exact sourceDistinct.disjoint sourceEntry (equal ▸ sourceNested)

end Flapjack.Compiler.Backend.ClosToBvl
