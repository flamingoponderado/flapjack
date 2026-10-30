import Flapjack.Compiler.Backend.BvlInline.Proofs.ExpRel
import Flapjack.Compiler.Backend.BvlInline.TickInline

/-! Inlining produces expressions related to their source expressions. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Bvl

/-- The cache premise factored out of the inlining proof; it has no standalone
HOL declaration. Each cached body corresponds to its original source code. -/
def CacheRelated (cache source : Spt (Nat × Exp)) : Prop :=
  ∀ name arity body, sptLookup name cache = some (arity, body) →
    ∃ original, sptLookup name source = some (arity, original) ∧
      ExpRel source [original] [body]

mutual
private theorem tickInlineSing_related (cache source : Spt (Nat × Exp))
    (compatible : CacheRelated cache source) (e : Exp) :
    ExpRel source [e] [tickInlineSing cache e] := by
  cases e with
  | var v => simpa only [tickInlineSing] using ExpRel.var (code := source) v
  | force loc n => simpa only [tickInlineSing] using ExpRel.force (code := source) loc n
  | ifThenElse x y z =>
    simpa only [tickInlineSing] using ExpRel.ifThenElse (tickInlineSing_related cache source compatible x)
      (tickInlineSing_related cache source compatible y) (tickInlineSing_related cache source compatible z)
  | «let» xs body =>
    simpa only [tickInlineSing] using ExpRel.letExp (tickInlineList_related cache source compatible xs)
      (tickInlineSing_related cache source compatible body)
  | raise x => simpa only [tickInlineSing] using ExpRel.raise (tickInlineSing_related cache source compatible x)
  | handle x y =>
    simpa only [tickInlineSing] using ExpRel.handle (tickInlineSing_related cache source compatible x)
      (tickInlineSing_related cache source compatible y)
  | tick x => simpa only [tickInlineSing] using ExpRel.tick (tickInlineSing_related cache source compatible x)
  | op op xs => simpa only [tickInlineSing] using ExpRel.op (op := op) (tickInlineList_related cache source compatible xs)
  | call ticks dest xs =>
    cases dest with
    | none =>
      simpa only [tickInlineSing] using ExpRel.call (ticks := ticks) (dest := none)
        (tickInlineList_related cache source compatible xs)
    | some name =>
      cases found : sptLookup name cache with
      | none =>
        simpa [tickInlineSing, found] using ExpRel.call (ticks := ticks) (dest := some name)
          (tickInlineList_related cache source compatible xs)
      | some entry =>
        obtain ⟨arity, body⟩ := entry
        obtain ⟨original, sourceFound, bodyRel⟩ := compatible name arity body found
        simpa [tickInlineSing, found] using ExpRel.inlineCall (ticks := ticks)
          (tickInlineList_related cache source compatible xs) sourceFound bodyRel
termination_by sizeOf e
decreasing_by all_goals simp_wf <;> omega

private theorem tickInlineList_related (cache source : Spt (Nat × Exp))
    (compatible : CacheRelated cache source) (xs : List Exp) :
    ExpRel source xs (tickInlineList cache xs) := by
  cases xs with
  | nil => simpa only [tickInlineList] using ExpRel.nil (code := source)
  | cons x xs =>
    cases xs with
    | nil => simpa only [tickInlineList] using tickInlineSing_related cache source compatible x
    | cons y ys =>
      have rest := tickInlineList_related cache source compatible (y :: ys)
      simp only [tickInlineList] at rest
      simpa only [tickInlineList] using ExpRel.cons (tickInlineSing_related cache source compatible x)
        rest
termination_by sizeOf xs
decreasing_by all_goals (simp_wf; omega)
end

/-- Source code and its tick-inlined version satisfy the inlining relation
when each cached body corresponds to its original. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "exp_rel_tick_inline"]
theorem expRelTickInline (cache : Spt (Nat × Exp)) (xs : List Exp) (source : Spt (Nat × Exp))
    (compatible : CacheRelated cache source) : ExpRel source xs (tickInline cache xs) :=
  tickInlineList_related cache source compatible xs

/-- The production inliner produces the same related expression. This
fuel-bounded executable correspondence has no standalone HOL declaration. -/
theorem inlineExpBounded_related (fuel : Nat) (cache source : Spt (Nat × Exp))
    (compatible : CacheRelated cache source) (e : Exp) :
    ∃ result, inlineExpBounded fuel cache e = some result ∧ ExpRel source [e] [result] := by
  exact ⟨tickInlineSing cache e, inlineExpBounded_eq fuel cache e,
    tickInlineSing_related cache source compatible e⟩

end Flapjack.Compiler.Backend.BvlInline.Proofs
