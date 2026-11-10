module

public import Flapjack.Compiler.Backend.WordSimp
public import Flapjack.RiscV.WordExpressionFlatten
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
public import Mathlib.Data.List.Defs
public import Flapjack.Misc.SptreeLookup
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec

@[expose] public section

/-! Executed `wordConstFpLoop` against the reviewed native `constFpLoop`.
Flapjack carrier infrastructure with no HOL original: the executed pass keeps
its knowledge in an association list, the native pass in an `Spt`. The
relation `ConstRel` says the list has distinct keys and the same lookups. From
an encoded input and related knowledge, the executed output encodes to the
native output and the final knowledge stays related. Only input encoding is
assumed; no output encoding or evaluation result is. -/
namespace Flapjack.Compiler.Backend.WordSimp

open RiscV

/-- Executed constant knowledge represents native knowledge: distinct keys and
equal lookups. Flapjack carrier relation, no HOL original. -/
def ConstRel {width : Nat} (m : NatInfoMap (BitVec width)) (s : Spt (BitVec width)) : Prop :=
  (m.map Prod.fst).Nodup ∧ ∀ k, lookupNatInfo k m = sptLookup k s

private theorem lookup_none_of_not_mem {α : Type} (k : Nat) :
    ∀ m : NatInfoMap α, k ∉ m.map Prod.fst → lookupNatInfo k m = none
  | [] , _ => rfl
  | (c, v) :: rest, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      have hne : (c == k) = false := by simpa using Ne.symm h.1
      simp only [lookupNatInfo, hne]
      exact lookup_none_of_not_mem k rest h.2

private theorem lookup_filter {α : Type} (k : Nat) (p : Nat × α → Bool) :
    ∀ m : NatInfoMap α, (m.map Prod.fst).Nodup →
      lookupNatInfo k (m.filter p) =
        match lookupNatInfo k m with
        | some v => if p (k, v) then some v else none
        | none => none
  | [], _ => rfl
  | (c, v) :: rest, nodup => by
      simp only [List.map_cons, List.nodup_cons] at nodup
      have ih := lookup_filter k p rest nodup.2
      by_cases hck : c = k
      · subst hck
        have hrest : lookupNatInfo c (rest.filter p) = none :=
          lookup_none_of_not_mem c _ (fun hm => nodup.1 (by
            simp only [List.mem_map] at hm ⊢
            obtain ⟨e, he, rfl⟩ := hm
            exact ⟨e, (List.mem_filter.mp he).1, rfl⟩))
        by_cases hp : p (c, v) <;> simp [List.filter, hp, lookupNatInfo, hrest]
      · have hne : (c == k) = false := by simpa using hck
        by_cases hp : p (c, v) <;> simp [List.filter, hp, lookupNatInfo, hne, ih]

theorem constRel_empty {width : Nat} : ConstRel ([] : NatInfoMap (BitVec width)) .ln :=
  ⟨List.nodup_nil, fun k => by simp [lookupNatInfo]⟩

theorem constRel_congr {width : Nat} {m : NatInfoMap (BitVec width)} {s s' : Spt (BitVec width)}
    (rel : ConstRel m s) (same : ∀ k, sptLookup k s = sptLookup k s') : ConstRel m s' :=
  ⟨rel.1, fun k => (rel.2 k).trans (same k)⟩

private theorem sptLookup_deleteAll {width : Nat} (k : Nat) :
    ∀ (names : List Nat) (s : Spt (BitVec width)),
      sptLookup k (deleteAll names s) = if k ∈ names then none else sptLookup k s
  | [], s => by simp [deleteAll]
  | n :: ns, s => by
      have ih := sptLookup_deleteAll k ns s
      simp only [deleteAll, List.foldr_cons] at ih ⊢
      rw [sptLookup_sptDelete, ih]
      by_cases h : k = n <;> simp [h]

end Flapjack.Compiler.Backend.WordSimp
