import Flapjack.Pancake.PanStructs.CompileExpProduction
import Flapjack.Pancake.PanStructs.CompileProgExact

/-! Flapjack program codec correspondence, with no HOL theorem original.
Only genuine input name/shape invariants are premises. -/
namespace Flapjack
open Pancake.PanLang Pancake.PanStructs.CompileShapeExact

private theorem productionExp_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (expression : Exp (BitVec width)) (he : ExpByteRanged expression) :
    expToHOL (structCompileExpExactProduction context expression) =
      compileExpExact (structPassContextToExact context) (expToHOL expression) := by
  rw [structCompileExpExactProduction_eq_legacy context hc hl hg expression he]
  exact (compileExpExact_encode context hc hl hg expression he).symm

private theorem productionShape_encode (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    shapeToHOL (structCompileShapeExactProduction context shape) =
      compileShapeExact (structContextToCompileShapeExact context) (shapeToHOL shape) := by
  rw [structCompileShapeExactProduction_eq_legacy context shape hc hs]
  exact (compileShapeExact_encode context shape hc hs).symm

/-- Full production program compilation commutes with the exact program codec.
All recursive IHs are derived internally. Dec and DecCall extend the body
context with the original source shape; optional Call handlers retain the
original context. This is Flapjack codec infrastructure, not a HOL evaluator
simulation theorem, so it carries no HOL tag. -/
theorem structCompileProgExactProduction_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      progToHOL (structCompileProgExactProduction context program) =
        compileProgExact (structPassContextToExact context) (progToHOL program)
  | .skip, _ => by simp [structCompileProgExactProduction, progToHOL, compileProgExact]
  | .break, _ => by simp [structCompileProgExactProduction, progToHOL, compileProgExact]
  | .continue, _ => by simp [structCompileProgExactProduction, progToHOL, compileProgExact]
  | .tick, _ => by simp [structCompileProgExactProduction, progToHOL, compileProgExact]
  | .annot tag text, _ => by simp [structCompileProgExactProduction, progToHOL, compileProgExact]
  | .dec name shape value body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hs, hv, hb⟩
      have hl' : ListParamByteRanged ((name, shape) :: context.locals) := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · cases hp; exact ⟨hn, hs⟩
        · exact hl p hp
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionShape_encode context.structs shape hc hs, productionExp_encode context hc hl hg value hv]
      have ih := structCompileProgExactProduction_encode
        { context with locals := (name, shape) :: context.locals } hc hl' hg body hb
      simpa only [structPassContextToExact, List.map_cons] using congrArg
        (fun compiled => ProgHOL.dec (Flapjack.Basis.Pure.MlString.ofString name)
          (compileShapeExact (structContextToCompileShapeExact context.structs) (shapeToHOL shape))
          (compileExpExact (structPassContextToExact context) (expToHOL value)) compiled) ih
  | .assign kind name value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg value h.2]
  | .primitive name operator arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [structCompileProgExactProduction_exps_encode context hc hl hg arguments h.2]
  | .store address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg address h.1, productionExp_encode context hc hl hg value h.2]
  | .store32 address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg address h.1, productionExp_encode context hc hl hg value h.2]
  | .storeByte address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg address h.1, productionExp_encode context hc hl hg value h.2]
  | .seq first second, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [structCompileProgExactProduction_encode context hc hl hg first h.1, structCompileProgExactProduction_encode context hc hl hg second h.2]
  | .ite condition first second, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg condition h.1, structCompileProgExactProduction_encode context hc hl hg first h.2.1, structCompileProgExactProduction_encode context hc hl hg second h.2.2]
  | .while condition body, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg condition h.1, structCompileProgExactProduction_encode context hc hl hg body h.2]
  | .call none function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [structCompileProgExactProduction_exps_encode context hc hl hg arguments h.2.1]
  | .call (some (returns, none)) function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [structCompileProgExactProduction_exps_encode context hc hl hg arguments h.2.1]
  | .call (some (returns, some (exception, handlerVar, handler))) function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [structCompileProgExactProduction_exps_encode context hc hl hg arguments h.2.1]
      rw [structCompileProgExactProduction_encode context hc hl hg handler h.2.2.2.2.2]
  | .decCall name shape function arguments body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hs, _, ha, hb⟩
      have hl' : ListParamByteRanged ((name, shape) :: context.locals) := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · cases hp; exact ⟨hn, hs⟩
        · exact hl p hp
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionShape_encode context.structs shape hc hs,
        structCompileProgExactProduction_exps_encode context hc hl hg arguments ha]
      have ih := structCompileProgExactProduction_encode
        { context with locals := (name, shape) :: context.locals } hc hl' hg body hb
      simpa only [structPassContextToExact, List.map_cons] using congrArg
        (fun compiled => ProgHOL.decCall (Flapjack.Basis.Pure.MlString.ofString name)
          (compileShapeExact (structContextToCompileShapeExact context.structs) (shapeToHOL shape))
          (Flapjack.Basis.Pure.MlString.ofString function)
          (compileExpsExact (structPassContextToExact context) (arguments.map expToHOL)) compiled) ih
  | .extCall function configuration configurationLength array arrayLength, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg configuration h.2.1, productionExp_encode context hc hl hg configurationLength h.2.2.1,
        productionExp_encode context hc hl hg array h.2.2.2.1, productionExp_encode context hc hl hg arrayLength h.2.2.2.2]
  | .return value, h => by
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg value h]
  | .raise exception value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg value h.2]
  | .shMemLoad size kind name address, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg address h.2]
  | .shMemStore size address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, progToHOL, compileProgExact]
      rw [productionExp_encode context hc hl hg address h.1, productionExp_encode context hc hl hg value h.2]
termination_by program _ => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | (simp_wf; omega) | omega

end Flapjack

