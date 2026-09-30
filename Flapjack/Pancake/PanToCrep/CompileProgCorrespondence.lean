import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
import Flapjack.Pancake.CrepInline.InlineRouteNames

/-! Whole declaration-level compiler output correspondence. These are
Flapjack carrier-codec obligations with no independent HOL declaration;
`DeclByteRanged` is supplied by the parser-backed executed path. -/

namespace Flapjack
open Pancake.PanLang Basis.Pure.MlString

/-- Compiling byte-ranged declarations produces byte-ranged table names and
bodies. The existing per-function exact compiler bridge supplies body range;
no successful-compilation premise is added. -/
theorem compileToCrepHOL_nameRanged {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ function ∈ compileToCrepHOL declarations,
      CrepNameRanged function.1 ∧ CrepProgNameRanged function.2.2 := by
  intro function hfunction
  simp only [compileToCrepHOL, ← functionInfosHOL_eq_makeFuncsHOL] at hfunction
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hfunction
  refine ⟨(functionEntries_byteRanged declarations hdecls entry hentry).1, ?_⟩
  rw [← compileFunctionExactProductionBridge declarations entry hdecls hentry]
  exact CrepInlineRoute.crepProgOfHOL_nameRanged _

/-- The production declaration-only table is the decode of the reviewed exact
`compile_to_crep` table. This is codec infrastructure, not a HOL theorem port. -/
theorem compileToCrepHOL_decode_eq {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileToCrepHOL declarations =
      (compileToCrepExactHOLW (declarations.map declToHOL)).map
        (fun t => (toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)) := by
  have h := congrArg
    (List.map (fun t : MlS × List Nat × CrepProgHOL width =>
      (toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)))
    (compileToCrepHOL_map_declToHOL declarations hdecls)
  rw [List.map_map] at h
  have hleft :
      (compileToCrepHOL declarations).map
        ((fun t => (toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)) ∘
          fun t => (ofString t.1, t.2.1, crepProgToHOL t.2.2)) =
      compileToCrepHOL declarations := by
    calc
      _ = (compileToCrepHOL declarations).map id := by
        apply List.map_congr_left
        intro t ht
        have hrange := compileToCrepHOL_nameRanged declarations hdecls t ht
        simp only [Function.comp_apply]
        rw [toStringOfBytes_ofString_of_bytes _ hrange.1,
          crepProgOfHOL_crepProgToHOL _ hrange.2]
        rcases t with ⟨name, params, body⟩
        rfl
      _ = _ := by simp
  rw [hleft] at h
  exact h

/-- Whole byte-ranged production `compile_prog` output equals the decode of the
reviewed exact HOL declaration-level compiler. The input byte condition is the
parser's carrier boundary, with no evaluation or successful-pass assumption.
This is Flapjack codec infrastructure, so it has no HOL tag. -/
theorem compileProgTopHOL_decode_eq {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileProgTopHOL declarations =
      (compileProgDeclsHOLW (declarations.map declToHOL)).map
        (fun t => (toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)) := by
  unfold compileProgTopHOL compileProgDeclsHOLW
  rw [compileProgInlineNames_bridge declarations hdecls,
    compileToCrepHOL_decode_eq declarations hdecls]
  simpa only [List.map_map, Function.comp_def] using
    CrepInlineRoute.compileInlTopHOL_decode_eq (width := width)
      ((functionsHOL ((declarations.map declToHOL).filter inlinableHOL)).map Prod.fst)
      (compileToCrepExactHOLW (declarations.map declToHOL))

/-- The parser-backed executed body route has the same complete decoded exact
compiler output. The only premise is its parser-supplied declaration codec
condition; no independent HOL declaration exists for this production adapter. -/
theorem compileProgTopHOLProductionExact_decode_eq {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileProgTopHOLProductionExact declarations hdecls =
      (compileProgDeclsHOLW (declarations.map declToHOL)).map
        (fun t => (toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)) := by
  rw [compileProgTopHOLProductionExact_eq]
  exact compileProgTopHOL_decode_eq declarations hdecls

/-- Executed parser-backed adapter: compile the complete declaration list with
HOL's reviewed `compile_prog`, then decode its ordered table and retain the
production metadata. The byte premise is proof-only codec infrastructure. -/
def compileProgNativeWithMetadata {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (_hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (CompiledFunction (BitVec width)) :=
  (compileToCrepHOLWithMetadata declarations).zipWith
    (fun original (_, _, body) => { original with body })
    ((compileProgDeclsHOLW (declarations.map declToHOL)).map
      (fun t => (toStringOfBytes t.1, t.2.1, crepProgOfHOL t.2.2)))

/-- Complete metadata output agreement at the parser's byte boundary. This
codec theorem has no separate HOL original or extra execution premise. -/
theorem compileProgNativeWithMetadata_eq {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileProgNativeWithMetadata declarations hdecls =
      compileProgTopHOLWithMetadata declarations := by
  unfold compileProgNativeWithMetadata compileProgTopHOLWithMetadata
  rw [← compileProgTopHOL_decode_eq declarations hdecls]

/-- Preserve the generic pipeline API for custom literal dictionaries. Standard
BitVec literals select the native whole compiler; custom literals retain the
compatibility inliner because its inserted zero/one words observe them. -/
def compileProgNativeWithMetadataRouted {width : Nat} [NeZero width]
    [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (CompiledFunction (BitVec width)) :=
  if (0 : BitVec width) = BitVec.ofNat width 0 ∧
      (1 : BitVec width) = BitVec.ofNat width 1 then
    compileProgNativeWithMetadata declarations hdecls
  else compileProgTopHOLWithMetadata declarations

/-- The actual CLI's standard BitVec dictionaries unconditionally select the
reviewed native whole compiler, rather than the compatibility fallback. -/
theorem compileProgNativeWithMetadataRouted_native {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileProgNativeWithMetadataRouted declarations hdecls =
      compileProgNativeWithMetadata declarations hdecls := by
  unfold compileProgNativeWithMetadataRouted
  rw [if_pos ⟨rfl, rfl⟩]

/-- Native routing preserves the generic pipeline, including custom literals.
This is a compatibility codec theorem, not a HOL declaration port. -/
theorem compileProgNativeWithMetadataRouted_eq {width : Nat} [NeZero width]
    [instZero : OfNat (BitVec width) 0] [instOne : OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileProgNativeWithMetadataRouted declarations hdecls =
      compileProgTopHOLWithMetadata declarations := by
  unfold compileProgNativeWithMetadataRouted
  split
  · rename_i h
    have hz : instZero = (⟨BitVec.ofNat width 0⟩ : OfNat (BitVec width) 0) := by
      cases instZero
      congr
      exact h.1
    have ho : instOne = (⟨BitVec.ofNat width 1⟩ : OfNat (BitVec width) 1) := by
      cases instOne
      congr
      exact h.2
    cases hz
    cases ho
    exact compileProgNativeWithMetadata_eq declarations hdecls
  · rfl

end Flapjack
