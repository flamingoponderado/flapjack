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

/-- Encoding a production context preserves every HOL key observation and
both layout sizes. Only payload shapes require a byte-range premise; all
queries in the relation are exact HOL names. Untagged codec infrastructure. -/
theorem globalDeclarationContextRel_ofPass [LawfulBEq String]
    {width : Nat} [NeZero width] (context : GlobalPassContext (BitVec width))
    (hshapes : GlobalContextListShapesByteRanged context) :
    GlobalDeclarationContextRel (cakeContextOfPass context)
      (PanGlobalsContextExact.ofPass context) := by
  refine ⟨rfl, rfl, ?_⟩
  intro key
  change lookupInfo (Flapjack.Basis.Pure.MlString.toStringOfBytes key) context.globals =
    ((lookupInfo (Flapjack.Basis.Pure.MlString.toStringOfBytes key) context.globals).map
      (fun entry => (shapeToHOL entry.1, entry.2))).map
      (fun entry => (shapeOfHOL entry.1, entry.2))
  rw [Option.map_map]
  exact (lookupInfo_decode_shape_eq _ _ hshapes).symm

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

/-- Complete recursive declaration compiler correspondence, including the
final context's entire HOL-observable map. Input range facts are supplied by
the parser/context invariant; no successful evaluation or target result is
assumed. This paired-carrier theorem has no separate HOL original. -/
theorem compileDecsCakeViaProgramHOL_exact [LawfulBEq String]
    {width : Nat} [NeZero width] (declarations : List (Decl (BitVec width))) :
    ∀ (context : GlobalPassContext (BitVec width)),
      GlobalContextListShapesByteRanged context →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      CompileDecsResultRel (compileDecsCakeViaProgramHOL context declarations)
        (compileDecsExactHOL (PanGlobalsContextExact.ofPass context)
          (declarations.map declToHOL)) := by
  induction declarations with
  | nil =>
      intro context hshapes _
      simpa [CompileDecsResultRel, compileDecsCakeViaProgramHOL, compileDecsExactHOL]
        using globalDeclarationContextRel_ofPass context hshapes
  | cons declaration declarations ih =>
      intro context hshapes hdecl
      have htail : ∀ d ∈ declarations, DeclByteRanged d :=
        fun d hd => hdecl d (by simp [hd])
      cases declaration with
      | function function =>
          have hfunction := hdecl (.function function) (by simp)
          have hdecoded :
              declOfHOL (.function { funDeclToHOL function with
                body := compileProgExactHOL (PanGlobalsContextExact.ofPass context)
                  (progToHOL function.body) }) =
                .function { function with
                  body := progOfHOL (compileProgExactHOL
                    (PanGlobalsContextExact.ofPass context) (progToHOL function.body)) } := by
            change Decl.function { funDeclOfHOL (funDeclToHOL function) with
              body := progOfHOL (compileProgExactHOL
                (PanGlobalsContextExact.ofPass context) (progToHOL function.body)) } = _
            rw [funDeclOfHOL_funDeclToHOL function hfunction]
          simp only [funDeclToHOL] at hdecoded
          rcases ih context hshapes htail with ⟨hi, hf, he, hc⟩
          simpa only [CompileDecsResultRel, compileDecsCakeViaProgramHOL,
            compileDecsExactHOL, List.map_cons, declToHOL, funDeclToHOL,
            hdecoded, hi, hf, he, and_self, true_and] using hc
      | exnDecl name shape =>
          have hentry := hdecl (.exnDecl name shape) (by simp)
          rcases ih context hshapes htail with ⟨hi, hf, he, hc⟩
          simpa [CompileDecsResultRel, compileDecsCakeViaProgramHOL,
            compileDecsExactHOL, declToHOL, declOfHOL, hi, hf, he,
            Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hentry.1,
            shapeOfHOL_shapeToHOL shape hentry.2] using hc
      | name name fields =>
          simpa only [CompileDecsResultRel, compileDecsCakeViaProgramHOL,
            compileDecsExactHOL, List.map_cons, declToHOL] using
              ih context hshapes htail
      | decl shape name value =>
          have hentry := hdecl (.decl shape name value) (by simp)
          let address := cakeAddress (cakeContextOfPass context) shape
          let next := { context with
            globals := (name, (shape, address)) :: context.globals
            globalsSize := address }
          have hnext := globalContextListShapesByteRanged_update context name shape
            address hshapes hentry.1
          have hcodec := PanGlobalsContextExact.ofPass_globalUpdate
            context name shape address hentry.2.1
          have haddress :
              (PanGlobalsContextExact.ofPass context).globalsSize +
                cakeBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL (shapeToHOL shape)) =
                  address := by
            simp [address, cakeAddress, cakeContextOfPass, PanGlobalsContextExact.ofPass,
              sizeOfShapeHOL_shapeToHOL]
          rcases ih next hnext htail with ⟨hi, hf, he, hc⟩
          simp only [CompileDecsResultRel, compileDecsCakeViaProgramHOL,
            compileDecsExactHOL, List.map_cons, declToHOL, compileDecsGlobalAddressExact_eq]
          rw [haddress, ← hcodec]
          simpa [next, address, compileExpRouteCake, progOfHOL, expOfHOL,
            hi, hf, he] using hc

end Flapjack
