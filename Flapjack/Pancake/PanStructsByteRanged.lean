module

public import Flapjack.Pancake.PanStructs
public import Flapjack.Pancake.PanLang.Decl
public import Flapjack.Pancake.PanLang.Prog
public import Flapjack.Pancake.PanStructs.CompileShapeExact
public import Flapjack.Pancake.PanStructs.OldExpShapeExact

@[expose] public section

/-! Byte-range facts for lookups in the production structure context. -/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Byte-rangedness of the production struct context used by the struct pass. -/
def CtxBR (c : StructContext) : Prop :=
  ∀ p ∈ c, NameRanged p.1 ∧ ListParamByteRanged p.2.fields

theorem lookupInfoWithRest_exists_mem [BEq String] {name : String} {context : StructContext}
    {info : StructInfo} {suffix : StructContext}
    (h : lookupInfoWithRest name context = some (info, suffix)) :
    ∃ k, (k, info) ∈ context := by
  induction context with
  | nil => simp only [lookupInfoWithRest] at h; cases h
  | cons entry rest ih =>
      by_cases hc : entry.1 == name
      · simp only [lookupInfoWithRest, hc] at h
        injection h with hp
        injection hp with h1 _
        exact ⟨entry.1, by simp only [List.mem_cons]; left; cases entry; simp_all⟩
      · simp only [lookupInfoWithRest, hc] at h
        obtain ⟨k, hk⟩ := ih h
        exact ⟨k, by simp [hk]⟩

theorem lookupInfoWithRest_ctxBR [BEq String] {name : String} {context : StructContext}
    {info : StructInfo} {suffix : StructContext}
    (h : lookupInfoWithRest name context = some (info, suffix)) (hc : CtxBR context) :
    CtxBR suffix := by
  induction context with
  | nil => simp only [lookupInfoWithRest] at h; cases h
  | cons entry rest ih =>
      by_cases hmatch : entry.1 == name
      · simp only [lookupInfoWithRest, hmatch] at h
        injection h with hp
        injection hp with _ h2
        subst h2
        exact fun p hp => hc p (by simp [hp])
      · simp only [lookupInfoWithRest, hmatch] at h
        exact ih h (fun p hp => hc p (by simp [hp]))

end Flapjack
