import Flapjack.Pancake.PanGlobals.ProgramExactRoute

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Local proof-irrelevance factoring for the context codec; no HOL original. -/
private theorem contextCodecMapExt {α β : Type} {left right : HolFiniteMapExact α β}
    (h : left.lookup = right.lookup) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-- Production declaration insertion commutes with the exact finite-map
context codec. The inserted name is byte-ranged by the parser; existing keys
and shapes need no extra premise, and duplicate keys use first-match lookup.
This paired-carrier law has no independent HOL original and remains untagged.
It supplies the context step of a future full `compile_decs` routing proof. -/
theorem PanGlobalsContextExact.ofPass_globalUpdate [LawfulBEq String]
    {width : Nat} [NeZero width] (context : GlobalPassContext (BitVec width))
    (name : String) (shape : Shape) (address : BitVec width)
    (hname : NameRanged name) :
    ofPass { context with
      globals := (name, (shape, address)) :: context.globals
      globalsSize := address } =
      { ofPass context with
        globals := (ofPass context).globals.updateEq
          (Flapjack.Basis.Pure.MlString.ofString name, (shapeToHOL shape, address))
        globalsSize := address } := by
  apply congrArg (fun globals => PanGlobalsContextExact.mk globals address context.maxGlobalsSize)
  apply contextCodecMapExt
  funext key
  have hdecoded :
      Flapjack.Basis.Pure.MlString.toStringOfBytes key = name ↔
        key = Flapjack.Basis.Pure.MlString.ofString name := by
    constructor
    · intro h
      simpa [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes] using
        congrArg Flapjack.Basis.Pure.MlString.ofString h
    · intro h
      rw [h]
      exact Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname
  by_cases h : key = Flapjack.Basis.Pure.MlString.ofString name
  · have hround :=
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname
    simp [ofPass, lookupInfo, HolFiniteMapExact.updateEq, FUPDATE_HOL, h, hround]
  · have hne : name ≠ Flapjack.Basis.Pure.MlString.toStringOfBytes key := by
      intro heq
      exact h (hdecoded.mp heq.symm)
    simp [ofPass, lookupInfo, HolFiniteMapExact.updateEq, FUPDATE_HOL, h, hne]

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
