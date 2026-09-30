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

end Flapjack
