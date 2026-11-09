module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IncrementalAddresses
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
public import Flapjack.Compiler.Backend.ClosAnnotate.Original

@[expose] public section

/-! Closure annotation address preservation for incremental compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

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

end Flapjack.Compiler.Backend.ClosToBvl
