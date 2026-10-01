import Flapjack.Compiler.Backend.Parmove.PmovMapInj
import Flapjack.Compiler.Backend.Parmove.PmovFinal

namespace Flapjack.Compiler.Backend.Parmove

set_option maxHeartbeats 1600000 in
/-- The top-level parallel-move compiler commutes with a renaming that is
injective on all endpoints of the input list and whose underlying temporary
`NONE` is preserved and reflected. The source premises are used exactly as in
HOL: injectivity on the flattened endpoint list from the given hypothesis, and
`windmill ls`; the well-formedness of the lifted initial scheduler state and the
injectivity of the lifted renaming are derived internally. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_MAP_INJ"]
theorem parmoveMapInj {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (ls : List (α × α)) :
    (let ls1 := ls.map Prod.fst ++ ls.map Prod.snd;
      (∀ x y, x ∈ ls1 → y ∈ ls1 → f x = f y → x = y)) ∧ windmill ls →
    parmove (ls.map (Prod.map f f)) =
      (parmove ls).map (Prod.map (Option.map f) (Option.map f)) := by
  intro h
  obtain ⟨hinjraw, hwind⟩ := h
  let f0 : Option α → Option β := Option.map f
  let g : Move α → Move β := Prod.map f0 f0
  let liftA : List (Move α) := ls.map (fun m => (some m.1, some m.2))
  let pState : State α := (liftA, [], [])
  let pB : List (Move β) := (ls.map (Prod.map f f)).map (fun m => (some m.1, some m.2))
  let mpState : State β := (pB, [], [])
  have hmapA : pB = liftA.map (Prod.map f0 f0) := by
    simp only [pB, liftA, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro m _
    simp only [Prod.map, f0, Option.map_some]
  have hmp : mapState f0 pState = mpState := by
    simp only [mpState, pState, mapState, Prod.map, List.map_nil, hmapA]
  have hwind' : windmill liftA := by
    change List.Pairwise (· ≠ ·) (liftA.map Prod.fst)
    simpa only [liftA, List.map_map, Function.comp_def] using
      hwind.map (f := Option.some) (by intro a b distinct equal; exact distinct (Option.some.inj equal))
  have hdest : ∀ move ∈ liftA, move.1.isSome = true := by
    intro move member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    rfl
  have hsrc : ∀ move ∈ liftA, move.2.isSome = true := by
    intro move member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    rfl
  have hvalid : wf pState := wf_init liftA ⟨hwind', hdest, hsrc⟩
  have hinj : injOnState f0 pState := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨hx, hy, heq⟩ := hxy
      have hendpoints : (stateToList pState).map Prod.fst ++
          (stateToList pState).map Prod.snd =
          (ls.map Prod.fst ++ ls.map Prod.snd).map Option.some := by
        simp only [pState, stateToList, liftA, List.append_nil,
          List.map_append, List.map_map, Function.comp_def]
      rw [hendpoints] at hx hy
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      have hfab : f a = f b := by
        simpa only [f0, Option.map_some, Option.some.injEq] using heq
      rw [hinjraw a b ha hb hfab]
    · intro x
      simp only [f0, Option.map_eq_none_iff]
  have hcomm := pmovMapInj f0 pState hvalid hinj
  obtain ⟨τ, hτ⟩ := pmov_final pState
  have hpmov_mp : pmov mpState = ([], [], τ.map g) := by
    rw [← hmp, hcomm, hτ]
    rfl
  have hL : parmove (ls.map (Prod.map f f)) = (τ.map g).reverse := by
    have h2 : parmove (ls.map (Prod.map f f)) = (pmov mpState).2.2.reverse := by
      simp only [parmove, mpState, pB]
    rw [h2, hpmov_mp]
  have hR : parmove ls = τ.reverse := by
    rw [parmove, hτ]
  rw [hL, hR, List.map_reverse]

end Flapjack.Compiler.Backend.Parmove
