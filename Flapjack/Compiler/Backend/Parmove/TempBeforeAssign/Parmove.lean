import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Pmov
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.FirstIndex
import Flapjack.Compiler.Backend.Parmove.PmovFinal
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.Parmove
open Flapjack.Misc

/-- Full HOL wrapper result: if a scheduled move reads the scratch register,
its first write exists and precedes the first read. Only the original windmill
premise is required; actual scheduler safety and terminal shape are derived. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml"
  "parmove_not_use_temp_before_assign"]
theorem parmoveNotUseTempBeforeAssign {α : Type} [DecidableEq α]
    (moves : List (α × α)) :
    windmill moves →
      match findIndex none ((parmove moves).map Prod.snd) 0 with
      | none => True
      | some i =>
        match findIndex none ((parmove moves).map Prod.fst) 0 with
        | none => False
        | some j => ¬ i ≤ j := by
  intro initial
  let lifted : List (Move α) := moves.map (fun move => (some move.1, some move.2))
  have liftedDistinct : (lifted.map Prod.fst).Nodup := by
    simpa [lifted, List.map_map, Function.comp_def] using
      (List.Nodup.map (f := Option.some) (by intro a b h; exact Option.some.inj h) initial)
  have valid : wf (lifted, [], ([] : List (Move α))) := by
    apply wf_init
    refine ⟨liftedDistinct, ?_, ?_⟩
    · intro move member
      obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp member
      rfl
    · intro move member
      obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp member
      rfl
  have safe := pmovNotUseTempBeforeAssign (lifted, [], ([] : List (Move α))) (0 : Nat)
    ⟨valid, rfl⟩
  obtain ⟨emitted, finished⟩ := pmov_final (lifted, [], ([] : List (Move α)))
  have outputSafe : notUseTempBeforeAssign (parmove moves) = true := by
    simpa [parmove, lifted, finished] using safe
  have ordering : ∀ i, findIndex none ((parmove moves).map Prod.snd) 0 = some i →
      ∃ j, findIndex none ((parmove moves).map Prod.fst) 0 = some j ∧ j < i := by
    convert (notUseTempBeforeAssignFirstIndex (parmove moves)).mp outputSafe using 1
    rename_i i
    apply Iff.of_eq
    let scheduled := parmove moves
    let statement (d : DecidableEq α) : Prop :=
      @findIndex (Option α) (@Option.instDecidableEq α d) none
          (scheduled.map Prod.snd) 0 = some i →
        ∃ j, @findIndex (Option α) (@Option.instDecidableEq α d) none
          (scheduled.map Prod.fst) 0 = some j ∧ j < i
    exact congrArg statement (Subsingleton.elim (inferInstance : DecidableEq α) instDecidableEq_flapjack)
  cases read : findIndex none ((parmove moves).map Prod.snd) 0 with
  | none => trivial
  | some i =>
    obtain ⟨j, write, earlier⟩ := ordering i read
    simp only [write]
    omega

end Flapjack.Compiler.Backend.Parmove
