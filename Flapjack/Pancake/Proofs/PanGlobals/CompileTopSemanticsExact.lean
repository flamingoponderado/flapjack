import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopShapeWf
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanGlobalsCompileTopSemanticsExact

/-- Same-module canonical witness for the exact state finite-map carrier used
by the declaration evaluator theorem below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width]
    : (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
      (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

private theorem updateListCons {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β)
    (entries : List (α × β)) :
    (map.update entry).updateList entries = map.updateList (entry :: entries) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateList, FUPDATE_LIST_cons]
  rfl

/-- Same-module canonical multi-carrier witness for the PanSem state used by
the compile-top semantics theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module canonical multi-carrier witness for the compiler context used
by the compile-top semantics theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Exact PanGlobals source lemma `evaluate_decls_only_functions_SOME`
(`pan_globalsProofScript.sml:2390`). Every source declaration is a function,
and the source's nested well-formed-shape premise is preserved literally.
`Classical.propDecidable` supplies the evaluator's implementation-only
decision procedure without adding a theorem hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_only_functions_SOME"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOnlyFunctionsSOMEHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (panCode : List (DeclHOL width))
    (hfunctions : ∀ declaration ∈ panCode, isFunctionHOL declaration = true)
    (hshapes : ∀ declaration ∈ panCode, ∀ function,
      declaration = .function function →
        function.params.all (fun parameter =>
          isWfShapeExactHOL state.structs parameter.2) = true ∧
          isWfShapeExactHOL state.structs function.returnShape = true) :
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ (by exact inferInstance) state
      (fun address => Classical.propDecidable (state.memaddrs address)) panCode =
      some { state with code := state.code.updateList (functionsHOL panCode) } := by
  classical
  induction panCode generalizing state with
  | nil =>
      cases state
      rfl
  | cons declaration declarations ih =>
      cases declaration with
      | name name fields =>
          have hbad := hfunctions (.name name fields) (by simp)
          simp [isFunctionHOL] at hbad
      | decl shape name expression =>
          have hbad := hfunctions (.decl shape name expression) (by simp)
          simp [isFunctionHOL] at hbad
      | exnDecl exceptionName shape =>
          have hbad := hfunctions (.exnDecl exceptionName shape) (by simp)
          simp [isFunctionHOL] at hbad
      | function function =>
          have hshape := hshapes (.function function) (by simp) function rfl
          have hparam : function.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) = true :=
            hshape.1
          have hreturn : isWfShapeExactHOL state.structs function.returnShape = true :=
            hshape.2
          let updated : PanSemStateFiniteExact width σ :=
            { state with code := state.code.update (function.name,
                (function.params, function.body, function.returnShape)) }
          have hrestFunctions : ∀ declaration ∈ declarations,
              isFunctionHOL declaration = true := by
            intro declaration hmem
            exact hfunctions declaration (by simp [hmem])
          have hrestShapes : ∀ declaration ∈ declarations, ∀ function',
              declaration = .function function' →
                function'.params.all (fun parameter =>
                  isWfShapeExactHOL updated.structs parameter.2) = true ∧
                  isWfShapeExactHOL updated.structs function'.returnShape = true := by
            intro declaration hmem function' heq
            have h := hshapes declaration (by simp [hmem]) function' heq
            simpa [updated] using h
          have hrec := ih updated hrestFunctions hrestShapes
          simpa [PanSemStateFiniteExact.evaluateDeclsHOLFinite, hparam, hreturn,
            updated, functionsHOL, updateListCons]
            using hrec

/-- Exact PanGlobals source lemma `evaluate_decls_only_functions_and_exns_SOME`
(`pan_globalsProofScript.sml:2404`). It retains the HOL requirements that
exception identifiers are distinct and fresh in the starting exception map;
those facts permit each `FUPDATE_LIST` in the exact finite-support state. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"
  "evaluate_decls_only_functions_and_exns_SOME"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOnlyFunctionsAndExnsSOMEHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (panCode : List (DeclHOL width))
    (hkind : ∀ declaration ∈ panCode,
      isFunctionHOL declaration = true ∨ isExnDeclHOL declaration = true)
    (hfunctions : ∀ declaration ∈ panCode, ∀ function,
      declaration = .function function →
        function.params.all (fun parameter =>
          isWfShapeExactHOL state.structs parameter.2) = true ∧
          isWfShapeExactHOL state.structs function.returnShape = true)
    (hdistinct : ((exceptionsHOL panCode).map Prod.fst).Nodup)
    (hfresh : ∀ entry ∈ exceptionsHOL panCode,
      (state.eshapes.lookup entry.1).isNone = true)
    (hshapes : ∀ entry ∈ exceptionsHOL panCode,
      isWfShapeExactHOL state.structs entry.2 = true) :
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ (by exact inferInstance) state
      (fun address => Classical.propDecidable (state.memaddrs address)) panCode =
      some { state with
        code := state.code.updateList (functionsHOL panCode)
        eshapes := state.eshapes.updateList (exceptionsHOL panCode) } := by
  classical
  induction panCode generalizing state with
  | nil =>
      cases state
      rfl
  | cons declaration declarations ih =>
      cases declaration with
      | name name fields =>
          have hbad := hkind (.name name fields) (by simp)
          simp [isFunctionHOL, isExnDeclHOL] at hbad
      | decl shape name expression =>
          have hbad := hkind (.decl shape name expression) (by simp)
          simp [isFunctionHOL, isExnDeclHOL] at hbad
      | function function =>
          have hfunction := hfunctions (.function function) (by simp) function rfl
          have hparam : function.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) = true :=
            hfunction.1
          have hreturn : isWfShapeExactHOL state.structs function.returnShape = true :=
            hfunction.2
          let updated : PanSemStateFiniteExact width σ :=
            { state with code := state.code.update (function.name,
                (function.params, function.body, function.returnShape)) }
          have hrestKind : ∀ declaration ∈ declarations,
              isFunctionHOL declaration = true ∨ isExnDeclHOL declaration = true := by
            intro declaration hmem
            exact hkind declaration (by simp [hmem])
          have hrestFunctions : ∀ declaration ∈ declarations, ∀ function',
              declaration = .function function' →
                function'.params.all (fun parameter =>
                  isWfShapeExactHOL updated.structs parameter.2) = true ∧
                  isWfShapeExactHOL updated.structs function'.returnShape = true := by
            intro declaration hmem function' heq
            have h := hfunctions declaration (by simp [hmem]) function' heq
            simpa [updated] using h
          have hrestDistinct : ((exceptionsHOL declarations).map Prod.fst).Nodup := by
            simpa [exceptionsHOL] using hdistinct
          have hrestFresh : ∀ entry ∈ exceptionsHOL declarations,
              (updated.eshapes.lookup entry.1).isNone = true := by
            intro entry hmem
            have h := hfresh entry (by simpa [exceptionsHOL] using hmem)
            simpa [updated] using h
          have hrestShapes : ∀ entry ∈ exceptionsHOL declarations,
              isWfShapeExactHOL updated.structs entry.2 = true := by
            intro entry hmem
            have h := hshapes entry (by simpa [exceptionsHOL] using hmem)
            simpa [updated] using h
          have hrec := ih updated hrestKind hrestFunctions hrestDistinct hrestFresh hrestShapes
          simpa [PanSemStateFiniteExact.evaluateDeclsHOLFinite, hparam, hreturn,
            updated, functionsHOL, exceptionsHOL, updateListCons]
            using hrec
      | exnDecl exceptionName shape =>
          have hallowed := hkind (.exnDecl exceptionName shape) (by simp)
          simp [isFunctionHOL, isExnDeclHOL] at hallowed
          have hshape : isWfShapeExactHOL state.structs shape = true :=
            hshapes ((exceptionName, shape) : MlS × ShapeHOL) (by simp [exceptionsHOL])
          have hfreshHead : (state.eshapes.lookup exceptionName).isNone = true :=
            hfresh ((exceptionName, shape) : MlS × ShapeHOL) (by simp [exceptionsHOL])
          have hdistinctRest : exceptionName ∉
              (exceptionsHOL declarations).map Prod.fst := by
            have hcons : List.Nodup
                (exceptionName :: (exceptionsHOL declarations).map Prod.fst) := by
              simpa [exceptionsHOL] using hdistinct
            exact (List.nodup_cons.mp hcons).1
          have hrestDistinct : ((exceptionsHOL declarations).map Prod.fst).Nodup := by
            have hcons : List.Nodup
                (exceptionName :: (exceptionsHOL declarations).map Prod.fst) := by
              simpa [exceptionsHOL] using hdistinct
            exact (List.nodup_cons.mp hcons).2
          let updated : PanSemStateFiniteExact width σ :=
            { state with eshapes := state.eshapes.update (exceptionName, shape) }
          have hrestKind : ∀ declaration ∈ declarations,
              isFunctionHOL declaration = true ∨ isExnDeclHOL declaration = true := by
            intro declaration hmem
            exact hkind declaration (by simp [hmem])
          have hrestFunctions : ∀ declaration ∈ declarations, ∀ function,
              declaration = .function function →
                function.params.all (fun parameter =>
                  isWfShapeExactHOL updated.structs parameter.2) = true ∧
                  isWfShapeExactHOL updated.structs function.returnShape = true := by
            intro declaration hmem function heq
            have h := hfunctions declaration (by simp [hmem]) function heq
            simpa [updated] using h
          have hrestFresh : ∀ entry ∈ exceptionsHOL declarations,
              (updated.eshapes.lookup entry.1).isNone = true := by
            intro entry hmem
            have hlookup := hfresh entry (by simp [exceptionsHOL, hmem])
            have hkey : exceptionName ≠ entry.1 := by
              intro heq
              subst exceptionName
              apply hdistinctRest
              exact List.mem_map.mpr ⟨entry, hmem, rfl⟩
            simpa [updated, HolFiniteMapExact.lookup_update, FUPDATE, hkey] using hlookup
          have hrestShapes : ∀ entry ∈ exceptionsHOL declarations,
              isWfShapeExactHOL updated.structs entry.2 = true := by
            intro entry hmem
            have h := hshapes entry (by simp [exceptionsHOL, hmem])
            simpa [updated] using h
          have hrec := ih updated hrestKind hrestFunctions hrestDistinct hrestFresh hrestShapes
          simpa [PanSemStateFiniteExact.evaluateDeclsHOLFinite, hshape, hfreshHead,
            updated, functionsHOL, exceptionsHOL, updateListCons]
            using hrec

end PanGlobalsCompileTopSemanticsExact

end Flapjack
