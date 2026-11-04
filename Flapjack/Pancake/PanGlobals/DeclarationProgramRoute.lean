import Flapjack.Pancake.PanGlobals.ProgramExactRoute

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Complete HOL-observable context correspondence. HOL names are `MlS`, so
the production map is observed at decoded HOL keys. Equality on arbitrary
Unicode String keys would be false: `ofString` truncates character codes to
bytes. This Flapjack cross-carrier relation has no separate HOL original. -/
def GlobalDeclarationContextRel {width : Nat} [NeZero width]
    (production : CakeContext width) (exactContext : PanGlobalsContextExact width) : Prop :=
  production.globalsSize = exactContext.globalsSize ∧
  production.maxGlobalsSize = exactContext.maxGlobalsSize ∧
  ∀ key : MlS,
    production.globals (Flapjack.Basis.Pure.MlString.toStringOfBytes key) =
      (exactContext.globals.lookup key).map (fun value => (shapeOfHOL value.1, value.2))

/-- Local proof-irrelevance factoring for the context codec; no HOL original. -/
private theorem contextCodecMapExt {α β : Type} {left right : HolFiniteMapExact α β}
    (h : left.lookup = right.lookup) : left = right := by
  cases left
  cases right
  cases h
  rfl

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

/-- The complete declaration result under the two carriers: all output lists
agree, and the final context agrees at every HOL name and both layout sizes.
This relation is Flapjack codec infrastructure with no HOL original. -/
def CompileDecsResultRel {width : Nat} [NeZero width]
    (production : CakeCompileDecsResult width)
    (exactResult : List (ProgHOL width) × List (DeclHOL width) ×
      List (DeclHOL width) × PanGlobalsContextExact width) : Prop :=
  production.initializers = exactResult.1.map progOfHOL ∧
  production.functions = exactResult.2.1.map declOfHOL ∧
  production.exceptions = exactResult.2.2.1.map declOfHOL ∧
  GlobalDeclarationContextRel production.context exactResult.2.2.2

end Flapjack
