module

public import Flapjack.Pancake.Proofs.PanToCrep
public import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
public import Flapjack.Pancake.Semantics.CrepProps

@[expose] public section

/-!
# `MEM_compile_exp_vmax` over the exact compiler

Exact port of HOL `MEM_compile_exp_vmax`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:410-436`) over the reviewed
exact carriers: `compile_exp` is `compileExpExactHOLW`, `var_cexp` is the
tagged `crepExpVarsHOL`, `ctxt_max` is `ctxtMaxFiniteExact`, and the context is
the finite-support `PanToCrepContextExact`.

HOL proves the statement by `recInduct compile_exp_ind`, using
`mem_comp_field_lem` (tagged `memCompFieldHOLExact_or_zero`),
`var_exp_load_shape` (tagged `crepExpVarsHOL_of_mem_loadShapeBytesHOLW`), and
`cexp_heads_eq`/`cexp_heads_simp_def` for the `Op`/`Crepop` head selection.

The module name carries a `Bound` suffix because
`Flapjack/Pancake/Proofs/PanToCrep/CompileExpVmax.lean` is the retired path of
an earlier, non-faithful vmax analogue that
`scripts/tests/test_check_hol_theorem_map.py` keeps out of the inventory. The
port below is the tagged faithful statement and does not reuse that path.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Flapjack-only: every head `cexpHeads` returns occurs in one of the source
    entry lists. HOL uses `cexp_heads_eq`/`cexp_heads_simp_def` plus
    `MEM_MAP` for this step; no standalone HOL declaration. -/
theorem cexpHeads_mem_entry {α : Type} (entries : List (List α)) (heads : List α)
    (hheads : cexpHeads entries = some heads) :
    ∀ head ∈ heads, ∃ entry ∈ entries, head ∈ entry := by
  induction entries generalizing heads with
  | nil =>
      simp only [cexpHeads, Option.some.injEq] at hheads
      subst heads
      intro head hmem
      simp at hmem
  | cons entry entries ih =>
      cases entry with
      | nil => simp [cexpHeads] at hheads
      | cons head0 tail =>
          cases hrest : cexpHeads entries with
          | none => simp [cexpHeads, hrest] at hheads
          | some restHeads =>
              simp only [cexpHeads, hrest, Option.some.injEq] at hheads
              subst heads
              intro head hmem
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact ⟨head0 :: tail, List.mem_cons_self, by
                  rw [hhead]
                  exact List.mem_cons_self⟩
              · obtain ⟨entry, hentry, hmemEntry⟩ := ih restHeads hrest head htail
                exact ⟨entry, List.mem_cons_of_mem _ hentry, hmemEntry⟩

/-- Flapjack-only induction invariant for `MEM_compile_exp_vmax`: every variable
    of every emitted expression is bounded by the context maximum. HOL folds the
    list motive into `compile_exp_ind`; this theorem states both motives. -/
theorem compileExpExactHOLW_vars_below {width ctxtWidth : Nat} [NeZero width]
    [NeZero ctxtWidth] (ctxt : PanToCrepContextExact ctxtWidth)
    (hmax : ctxtMaxFiniteExact ctxt.vmax ctxt.vars) (exp : ExpHOL width) :
    ∀ (n : Nat) (e : CrepExpHOL width),
      n ∈ crepExpVarsHOL e → e ∈ (compileExpExactHOLW ctxt exp).1 → n ≤ ctxt.vmax := by
  apply compileExpExactHOLW.induct (context := ctxt)
    (motive1 := fun exp => ∀ (n : Nat) (e : CrepExpHOL width),
      n ∈ crepExpVarsHOL e → e ∈ (compileExpExactHOLW ctxt exp).1 → n ≤ ctxt.vmax)
    (motive2 := fun expressions => ∀ (n : Nat) (e : CrepExpHOL width),
      n ∈ crepExpVarsHOL e →
        e ∈ (compileExpExactHOLWList ctxt expressions).flatMap Prod.fst → n ≤ ctxt.vmax)
  case case1 =>
    intro value n e hvars hmem
    simp only [compileExpExactHOLW, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case2 =>
    intro name shape names hlookup n e hvars hmem
    simp only [compileExpExactHOLW, hlookup] at hmem
    rcases List.mem_map.mp hmem with ⟨slot, hslot, he⟩
    subst e
    simp only [crepExpVarsHOL, List.mem_singleton] at hvars
    subst n
    exact hmax.2 name shape names hlookup slot hslot
  case case3 =>
    intro name hlookup n e hvars hmem
    simp only [compileExpExactHOLW, hlookup, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case4 =>
    intro name n e hvars hmem
    simp only [compileExpExactHOLW, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case5 =>
    intro expressions ih n e hvars hmem
    simp only [compileExpExactHOLW] at hmem
    exact ih n e hvars hmem
  case case6 =>
    intro index expression
    dsimp only
    intro shapes hcompiled ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hcompiled] at hmem
    rcases memCompFieldHOLExact_or_zero index shapes
        (compileExpExactHOLW ctxt expression).1 e hmem with hin | hzero
    · exact ih n e hvars hin
    · subst e
      simp [crepExpVarsHOL] at hvars
  case case7 =>
    intro index expression
    dsimp only
    intro hnotcomb ih
    intro n e hvars hmem
    cases h : compileExpExactHOLW ctxt expression with
    | mk compiledExpressions compiledShape =>
        cases compiledShape with
        | comb shapes => exact absurd (congrArg Prod.snd h) (hnotcomb shapes)
        | one =>
            simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
            subst e
            simp [crepExpVarsHOL] at hvars
        | named name =>
            simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
            subst e
            simp [crepExpVarsHOL] at hvars
  case case8 =>
    intro name fields n e hvars hmem
    simp only [compileExpExactHOLW, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case9 =>
    intro name value n e hvars hmem
    simp only [compileExpExactHOLW, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case10 =>
    intro shape expression address tail snd hcompiled ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hcompiled] at hmem
    have hshape := crepExpVarsHOL_of_mem_loadShapeBytesHOLW
      (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape) (0 : BitVec width) address e hmem
    rw [hshape] at hvars
    exact ih n address hvars (by
      rw [hcompiled]
      exact List.mem_cons_self)
  case case11 =>
    intro shape expression snd hcompiled ih n e hvars hmem
    cases h : compileExpExactHOLW ctxt expression with
    | mk compiledExpressions compiledShape =>
        cases compiledExpressions with
        | nil =>
            simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
            subst e
            simp [crepExpVarsHOL] at hvars
        | cons address tail =>
            rw [hcompiled] at h
            simp at h
  case case12 =>
    intro expression address tail hcompiled ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hcompiled, List.mem_singleton] at hmem
    subst e
    simp only [crepExpVarsHOL] at hvars
    exact ih n address hvars (by
      rw [hcompiled]
      exact List.mem_cons_self)
  case case13 =>
    intro expression hnotcons ih
    intro n e hvars hmem
    cases h : compileExpExactHOLW ctxt expression with
    | mk compiledExpressions compiledShape =>
        cases compiledExpressions with
        | nil =>
            simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
            subst e
            simp [crepExpVarsHOL] at hvars
        | cons address tail =>
            cases compiledShape with
            | one => exact absurd h (hnotcons address tail)
            | comb shapes =>
                simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
                subst e
                simp [crepExpVarsHOL] at hvars
            | named name =>
                simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
                subst e
                simp [crepExpVarsHOL] at hvars
  case case14 =>
    intro expression address tail hcompiled ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hcompiled, List.mem_singleton] at hmem
    subst e
    simp only [crepExpVarsHOL] at hvars
    exact ih n address hvars (by
      rw [hcompiled]
      exact List.mem_cons_self)
  case case15 =>
    intro expression hnotcons ih
    intro n e hvars hmem
    cases h : compileExpExactHOLW ctxt expression with
    | mk compiledExpressions compiledShape =>
        cases compiledExpressions with
        | nil =>
            simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
            subst e
            simp [crepExpVarsHOL] at hvars
        | cons address tail =>
            cases compiledShape with
            | one => exact absurd h (hnotcons address tail)
            | comb shapes =>
                simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
                subst e
                simp [crepExpVarsHOL] at hvars
            | named name =>
                simp only [compileExpExactHOLW, h, List.mem_singleton] at hmem
                subst e
                simp [crepExpVarsHOL] at hvars
  case case16 =>
    intro operator expressions heads hheads ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hheads, List.mem_singleton] at hmem
    subst e
    simp only [crepExpVarsHOL, crepExpVarsHOLList_eq_flatMap] at hvars
    obtain ⟨head, hhead, hn⟩ := List.mem_flatMap.mp hvars
    obtain ⟨entry, hentry, hmemEntry⟩ :=
      cexpHeads_mem_entry _ heads hheads head hhead
    obtain ⟨compiled, hcompiledMem, hentryEq⟩ := List.mem_map.mp hentry
    have hmemHead : head ∈ (compileExpExactHOLWList ctxt expressions).flatMap Prod.fst :=
      List.mem_flatMap.mpr ⟨compiled, hcompiledMem, by
        rw [hentryEq]
        exact hmemEntry⟩
    exact ih n head hn hmemHead
  case case17 =>
    intro operator expressions hheads ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hheads, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case18 =>
    intro operator expressions heads hheads ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hheads, List.mem_singleton] at hmem
    subst e
    simp only [crepExpVarsHOL, crepExpVarsHOLList_eq_flatMap] at hvars
    obtain ⟨head, hhead, hn⟩ := List.mem_flatMap.mp hvars
    obtain ⟨entry, hentry, hmemEntry⟩ :=
      cexpHeads_mem_entry _ heads hheads head hhead
    obtain ⟨compiled, hcompiledMem, hentryEq⟩ := List.mem_map.mp hentry
    have hmemHead : head ∈ (compileExpExactHOLWList ctxt expressions).flatMap Prod.fst :=
      List.mem_flatMap.mpr ⟨compiled, hcompiledMem, by
        rw [hentryEq]
        exact hmemEntry⟩
    exact ih n head hn hmemHead
  case case19 =>
    intro operator expressions hheads ih
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hheads, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case20 =>
    intro operator left right leftHead leftTail leftShape rightHead rightTail rightShape
      hright hleft ihLeft ihRight
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hleft, hright, List.mem_singleton] at hmem
    subst e
    simp only [crepExpVarsHOL, List.mem_append] at hvars
    rcases hvars with hvars | hvars
    · exact ihLeft n leftHead hvars (by
        rw [hleft]
        exact List.mem_cons_self)
    · exact ihRight n rightHead hvars (by
        rw [hright]
        exact List.mem_cons_self)
  case case21 =>
    intro operator left right hnotcons ihLeft ihRight
    intro n e hvars hmem
    cases hLeft : compileExpExactHOLW ctxt left with
    | mk leftExpressions leftShape =>
        cases hRight : compileExpExactHOLW ctxt right with
        | mk rightExpressions rightShape =>
            cases leftExpressions with
            | nil =>
                simp only [compileExpExactHOLW, hLeft, List.mem_singleton] at hmem
                subst e
                simp [crepExpVarsHOL] at hvars
            | cons leftHead leftTail =>
                cases rightExpressions with
                | nil =>
                    simp only [compileExpExactHOLW, hLeft, hRight,
                      List.mem_singleton] at hmem
                    subst e
                    simp [crepExpVarsHOL] at hvars
                | cons rightHead rightTail =>
                    exact absurd hRight (hnotcons leftHead leftTail leftShape
                      rightHead rightTail rightShape hLeft)
  case case22 =>
    intro operator left right leftHead leftTail leftShape rightHead rightTail rightShape
      hright hleft ihLeft ihRight
    intro n e hvars hmem
    simp only [compileExpExactHOLW, hleft, hright, List.mem_singleton] at hmem
    subst e
    simp only [crepExpVarsHOL, List.mem_append] at hvars
    rcases hvars with hvars | hvars
    · exact ihLeft n leftHead hvars (by
        rw [hleft]
        exact List.mem_cons_self)
    · exact ihRight n rightHead hvars (by
        rw [hright]
        exact List.mem_cons_self)
  case case23 =>
    intro operator left right hnotcons ihLeft ihRight
    intro n e hvars hmem
    cases hLeft : compileExpExactHOLW ctxt left with
    | mk leftExpressions leftShape =>
        cases hRight : compileExpExactHOLW ctxt right with
        | mk rightExpressions rightShape =>
            cases leftExpressions with
            | nil =>
                simp only [compileExpExactHOLW, hLeft, List.mem_singleton] at hmem
                subst e
                simp [crepExpVarsHOL] at hvars
            | cons leftHead leftTail =>
                cases rightExpressions with
                | nil =>
                    simp only [compileExpExactHOLW, hLeft, hRight,
                      List.mem_singleton] at hmem
                    subst e
                    simp [crepExpVarsHOL] at hvars
                | cons rightHead rightTail =>
                    exact absurd hRight (hnotcons leftHead leftTail leftShape
                      rightHead rightTail rightShape hLeft)
  case case24 =>
    intro n e hvars hmem
    simp only [compileExpExactHOLW, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case25 =>
    intro n e hvars hmem
    simp only [compileExpExactHOLW, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case26 =>
    intro n e hvars hmem
    simp only [compileExpExactHOLW, List.mem_singleton] at hmem
    subst e
    simp [crepExpVarsHOL] at hvars
  case case27 =>
    intro n e hvars hmem
    simp [compileExpExactHOLWList] at hmem
  case case28 =>
    intro expression expressions ihExpression ihExpressions
    intro n e hvars hmem
    simp only [compileExpExactHOLWList, List.flatMap_cons, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact ihExpression n e hvars hmem
    · exact ihExpressions n e hvars hmem

/-! Same-module canonical carrier witness for the
    `fmap_as_finite_support_relation` qualifier on `memCompileExpVmaxHOL`. -/
namespace CompileExpVmaxBoundWitnesses

theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact {width : Nat}
    [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

end CompileExpVmaxBoundWitnesses

/-- Exact port of HOL `MEM_compile_exp_vmax`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:410-436`). The typed
    capture `MEM_compile_exp_vmax_typed`
    (`scripts/hol-probes/pan_to_crep_proof_typed_probe.out:58`) binds
    `ctxt exp n e` and gives ONE three-conjunct premise
    (`ctxt_max`, `MEM n (var_cexp e)`, `MEM e (FST (compile_exp ctxt exp))`),
    right-associated, with conclusion `n ≤ ctxt.vmax`. `ctxt_max` is
    `ctxtMaxFiniteExact`, `var_cexp` is `crepExpVarsHOL`, `compile_exp` is
    `compileExpExactHOLW`, and `FST` stays the projection `.1`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MEM_compile_exp_vmax"
  (fmap_as_finite_support_relation := [PanToCrepContextExact.vars])
  (words_as_type_indexed_bitvec)]
theorem memCompileExpVmaxHOL {width ctxtWidth : Nat} [NeZero width] [NeZero ctxtWidth] :
    ∀ (ctxt : PanToCrepContextExact ctxtWidth) (exp : ExpHOL width) (n : Nat)
      (e : CrepExpHOL width),
      ctxtMaxFiniteExact ctxt.vmax ctxt.vars ∧ n ∈ crepExpVarsHOL e ∧
        e ∈ (compileExpExactHOLW ctxt exp).1 →
      n ≤ ctxt.vmax := by
  rintro ctxt exp n e ⟨hmax, hvars, hmem⟩
  exact compileExpExactHOLW_vars_below ctxt hmax exp n e hvars hmem

end Flapjack
