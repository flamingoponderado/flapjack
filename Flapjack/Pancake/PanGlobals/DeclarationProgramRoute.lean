import Flapjack.Pancake.PanGlobals.ProgramExactRoute

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Executable Flapjack declaration wrapper: function bodies run the reviewed
HOL program compiler directly. Declaration metadata and context threading
retain the production representation. This wrapper has no separate HOL
original; it does not claim to port the entire compile_decs definition. -/
def compileDecsCakeViaProgramHOL [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) :
    List (Decl (BitVec width)) → CakeCompileDecsResult width
  | [] =>
      { initializers := [], functions := [], exceptions := []
        context := cakeContextOfPass context }
  | .function declaration :: declarations =>
      let rest := compileDecsCakeViaProgramHOL context declarations
      { initializers := rest.initializers
        functions := .function { declaration with
            body := progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
              (progToHOL declaration.body)) } :: rest.functions
        exceptions := rest.exceptions
        context := rest.context }
  | .exnDecl exception shape :: declarations =>
      let rest := compileDecsCakeViaProgramHOL context declarations
      { rest with exceptions := .exnDecl exception shape :: rest.exceptions }
  | .name _ _ :: declarations => compileDecsCakeViaProgramHOL context declarations
  | .decl shape name value :: declarations =>
      let address := cakeAddress (cakeContextOfPass context) shape
      let nextContext := { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      let rest := compileDecsCakeViaProgramHOL nextContext declarations
      { initializers :=
          .store (.op .sub [.topAddr, .const address])
            (compileExpRouteCake context value) :: rest.initializers
        functions := rest.functions
        exceptions := rest.exceptions
        context := rest.context }

/-- Flapjack routing equality, with no HOL original. Parser byte-range facts
and the actual context shape invariant discharge the program codec boundary. -/
theorem compileDecsCakeViaProgramHOL_eq [LawfulBEq String]
    {width : Nat} [NeZero width] (declarations : List (Decl (BitVec width))) :
    ∀ context : GlobalPassContext (BitVec width),
      GlobalContextListShapesByteRanged context →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      compileDecsCakeViaProgramHOL context declarations =
        compileDecsCakeOfExact context declarations := by
  induction declarations with
  | nil => intros; rfl
  | cons declaration declarations ih =>
      intro context hshapes hdecl
      have htail : ∀ d ∈ declarations, DeclByteRanged d :=
        fun d hd => hdecl d (by simp [hd])
      cases declaration with
      | function function =>
          have hbody := (hdecl (.function function) (by simp)).2.2.1
          simp only [compileDecsCakeViaProgramHOL, compileDecsCakeOfExact]
          rw [ih context hshapes htail,
            ← compileProgCakeOfExact_eq_exact context hshapes function.body hbody]
      | exnDecl exception shape =>
          simp only [compileDecsCakeViaProgramHOL, compileDecsCakeOfExact]
          rw [ih context hshapes htail]
      | name name fields =>
          exact ih context hshapes htail
      | decl shape name value =>
          have hshape := (hdecl (.decl shape name value) (by simp)).1
          have hnext := globalContextListShapesByteRanged_update context name shape
            (cakeAddress (cakeContextOfPass context) shape) hshapes hshape
          simp only [compileDecsCakeViaProgramHOL, compileDecsCakeOfExact]
          rw [ih _ hnext htail]

end Flapjack
