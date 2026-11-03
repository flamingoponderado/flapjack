import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationCodeSemantics
import Flapjack.FiniteMap.AlistExact

/-! Annotation semantics with installed source code. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.ClosToBvl

/-- The installed-code helper is the canonical right-folded source map.
This is Flapjack infrastructure with no separate HOL declaration. -/
theorem initialSourceCode_eq_alist (program : List (Nat × Nat × ClosLang.Exp)) :
    initialSourceCode program = HolFiniteMapExact.alistToFmap program := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp [initialSourceCode, HolFiniteMapExact.alistToFmap, FUPDATE_LIST_HOL_eq_FUPDATE_LIST]

/-- Every member of a safe list is safe on its own. This is a proof helper
without a separate HOL declaration. -/
theorem everyFnVarsNone_member (expressions : List ClosLang.Exp)
    (safe : everyFnVarsNone expressions) (body : ClosLang.Exp) (member : body ∈ expressions) :
    everyFnVarsNone [body] := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [everyFnVarsNone] at safe
    rcases List.mem_cons.mp member with rfl | member
    · simpa [everyFnVarsNone] using safe.1
    · exact ih safe.2 member

/-- Annotation preserves whole-program observations with installed code. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "semantics_annotate"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem semanticsAnnotate_sourceShape {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : List (Nat × Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (program : List ClosLang.Exp)
    (notFail : semantics ffi maxApp (Flapjack.HolFiniteMapExact.alistToFmap code)
      oracle (pureCc compileInc compiler) program ≠ .fail)
    (safe : everyFnVarsNone program ∧
      everyFnVarsNone (code.map (fun (_, _, body) => body)) ∧
      ∀ n, everyFnVarsNone (oracle n).2.1 ∧
        everyFnVarsNone ((oracle n).2.2.map (fun (_, _, body) => body))) :
    semantics ffi maxApp (Flapjack.HolFiniteMapExact.alistToFmap (compile code))
      (pureCo compileInc ∘ oracle) compiler (annotateList 0 program) =
    semantics ffi maxApp (Flapjack.HolFiniteMapExact.alistToFmap code)
      oracle (pureCc compileInc compiler) program := by
  have codeSafe : ∀ name arity body, (name, arity, body) ∈ code → everyFnVarsNone [body] := by
    intro name arity body member
    apply everyFnVarsNone_member _ safe.2.1 body
    exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
  have result := annotation_installed_semantics ffi maxApp code oracle compiler program
    safe.1 codeSafe safe.2.2 (by simpa [initialSourceCode_eq_alist] using notFail)
  simpa [initialSourceCode_eq_alist] using result.symm

end Flapjack.Compiler.Backend.ClosAnnotate
