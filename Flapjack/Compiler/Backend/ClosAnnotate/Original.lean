module

public import Flapjack.Compiler.Backend.ClosAnnotate.Free.OriginalEquivalence
public import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence

@[expose] public section

/-! Original annotation entry points and their executable equivalents. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang

/-- The original list-shaped annotation. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "annotate_def"]
noncomputable def annotateSource (arity : Nat) (xs : List Exp) : List Exp :=
  shiftSource (altFreeSource xs).1 0 arity .ln

/-- The original annotation of labelled closure functions. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "compile_def"]
noncomputable def compileSource {α : Type} (prog : List (α × Nat × Exp)) : List (α × Nat × Exp) :=
  prog.map fun (n, args, exp) =>
    (n, args, @Flapjack.holHd Exp ⟨.var .none 0⟩ (annotateSource args [exp]))

/-- The original incremental annotation entry point. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "compile_inc_def"]
noncomputable def compileIncSource {α : Type} (p : List Exp × List (α × Nat × Exp)) :
    List Exp × List (α × Nat × Exp) :=
  (annotateSource 0 p.1, compileSource p.2)

/-- Singleton and list annotation agree with the executable traversals. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "annotate_sing_eq"]
theorem annotateSource_sing_eq (arity : Nat) (e : Exp) (es : List Exp) :
    annotateSource arity [e] = [annotateSing arity e] ∧
    annotateSource arity es = annotateList arity es := by
  constructor
  · simp [annotateSource, annotateSing, altFreeSource_sing_eq.1, shiftSource_sing_eq.1]
  · simp [annotateSource, annotateList, altFreeSource_sing_eq.2.1, shiftSource_sing_eq.2.1]

/-- Original compilation is the executable singleton annotation map. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "compile_eq"]
theorem compileSource_eq {α : Type} (prog : List (α × Nat × Exp)) :
    compileSource prog = prog.map (fun (n, args, exp) => (n, args, annotateSing args exp)) := by
  simp [compileSource, (annotateSource_sing_eq _ _ []).1, Flapjack.holHd]

/-- Original incremental compilation uses the executable list traversal. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "compile_inc_eq"]
theorem compileIncSource_eq {α : Type} (e : List Exp) (aux : List (α × Nat × Exp)) :
    compileIncSource (e, aux) = (annotateList 0 e, compileSource aux) := by
  simp [compileIncSource, (annotateSource_sing_eq 0 (.var .none 0) e).2]

/-- The original and executed compilation entry points agree. This connects
the source theorem to the optimized production implementation. -/
theorem compileSource_eq_compile {α : Type} (prog : List (α × Nat × Exp)) :
    compileSource prog = compile prog := by
  simpa [compile] using compileSource_eq prog

/-- The original and executed incremental entry points agree. -/
theorem compileIncSource_eq_compileInc {α : Type} (p : List Exp × List (α × Nat × Exp)) :
    compileIncSource p = compileInc p := by
  cases p with
  | mk e aux => simpa [compileInc, compileSource_eq_compile] using compileIncSource_eq e aux

end Flapjack.Compiler.Backend.ClosAnnotate
