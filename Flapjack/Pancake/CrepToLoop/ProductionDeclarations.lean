import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
import Flapjack.Pancake.PanToCrep.CompileProgCorrespondence

namespace Flapjack.CrepToLoopProduction
open Basis.Pure.MlString Pancake.PanLang

/-- Metadata is reattached in the same order as the original function table;
its projection retains every original name, parameter and compiled body.
This is Flapjack codec algebra, not a separately named HOL theorem. -/
theorem compatibilityMetadata_payload {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) :
    (compileProgTopHOLWithMetadata declarations).map
      (fun f => (f.name, f.params, f.body)) = compileProgTopHOL declarations := by
  simp only [compileProgTopHOLWithMetadata, compileToCrepHOLWithMetadata,
    compileProgTopHOL, compileToCrepHOL, compileInlTopHOL,
    List.zipWith_map_right, List.zipWith_map_left, List.zipWith_self,
    List.map_map, Function.comp_def]

/-- Raw native Pan-to-Crep metadata has exactly the complete decoded original
payload. No successful compilation or output-equality premise is supplied. -/
theorem nativeMetadata_payloadDecoded {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    (compileProgNativeWithMetadata declarations source).map
      (fun f => (f.name, f.params, f.body)) =
    (compileProgDeclsHOLW (declarations.map declToHOL)).map
      (fun t => (toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)) := by
  rw [compileProgNativeWithMetadata_eq, compatibilityMetadata_payload,
    compileProgTopHOL_decode_eq declarations source]

/-- All source names and nested body names are derived from the decoded
original table, not supplied as separate compiler-output premises. -/
theorem nativeMetadata_names {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ function ∈ compileProgNativeWithMetadata declarations source,
      CrepNameRanged function.name ∧ CrepProgNameRanged function.body := by
  intro function member
  have payloadMember : (function.name, function.params, function.body) ∈
      (compileProgNativeWithMetadata declarations source).map
        (fun f => (f.name, f.params, f.body)) := List.mem_map_of_mem member
  rw [nativeMetadata_payloadDecoded declarations source] at payloadMember
  obtain ⟨row, _, same⟩ := List.mem_map.mp payloadMember
  have nameSame := congrArg Prod.fst same
  have bodySame := congrArg (fun t => t.2.2) same
  change toStringOfBytes row.1 = function.name at nameSame
  change crepProgOfHOL row.2.2 = function.body at bodySame
  constructor
  · rw [← nameSame]
    exact nameRanged_toStringOfBytes row.1
  · rw [← bodySame]
    exact CrepInlineRoute.crepProgOfHOL_nameRanged row.2.2

/-- Re-encoding the entire raw metadata table recovers the original native
Pan-to-Crep result. Names, parameter slots, order and all body fields agree. -/
theorem nativeMetadata_sourcePrograms {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    sourcePrograms (compileProgNativeWithMetadata declarations source) =
      compileProgDeclsHOLW (declarations.map declToHOL) := by
  have payload := congrArg (List.map (fun t : FunName × List Nat × CrepProg (BitVec width) =>
    (ofString t.1, t.2.1, crepProgToHOL t.2.2)))
    (nativeMetadata_payloadDecoded declarations source)
  simpa only [sourcePrograms, List.map_map, Function.comp_def,
    ofString_toStringOfBytes, crepProgToHOL_crepProgOfHOL, Prod.eta,
    List.map_id_fun', id_eq] using payload

/-- Original declaration-to-Loop composition through raw native metadata.
Crep arithmetic simplification runs only inside original compile_prog. This
callable producer does not relabel, apply generic crepSimpFunctions, or assume
successful compiled output. Actual CLI/downstream wiring remains separate. -/
def compileDeclarationsToLoopNative? {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    Option (List (Nat × List Nat × HolLoopProg width)) :=
  compileProgFromProduction? (compileProgNativeWithMetadata declarations source)

/-- The real source declaration boundary discharges the entire producer guard
and gives both complete original compiler passes. No target execution, output
relation, idempotence or label-rebase premise is introduced. -/
theorem compileDeclarationsToLoopNative_original {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileDeclarationsToLoopNative? declarations source =
      some (compileProgHOLExact .riscv
        (compileProgDeclsHOLW (declarations.map declToHOL))) := by
  unfold compileDeclarationsToLoopNative?
  rw [compileProgFromProduction_supported _
    (fun f hf => (nativeMetadata_names declarations source f hf).1)
    (fun f hf => (nativeMetadata_names declarations source f hf).2),
    nativeMetadata_sourcePrograms declarations source]

end Flapjack.CrepToLoopProduction
