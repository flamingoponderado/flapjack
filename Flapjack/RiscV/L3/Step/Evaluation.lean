import Flapjack.RiscV.L3.Step.Next

/-! Exact original step evaluation rules. Their Fetch/DecodeAny/Run premises
are the original HOL premises; no Next result or pass simulation is assumed.
Full native Run inherits the IEEE rational-cut assumption (SOUNDNESS item 8). -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

attribute [local irreducible] Run Fetch DecodeAny update_pc NextRISCV

/-- Original normal-control rule: the five conjuncts are exactly the source
Fetch, decode, Run, exception and empty-control premises; no Next result is assumed. -/
theorem nextRISCV (s : riscv_state) (w : rawInstType) (fetched : riscv_state)
    (i : instruction) (nxt : riscv_state)
    (h : Fetch s = (w, fetched) ∧ DecodeAny w = i ∧ Run i fetched = nxt ∧
      nxt.exception = exception.NoException ∧ nxt.c_NextFetch nxt.procID = none) :
    NextRISCV s = update_pc (nxt.c_PC nxt.procID + Skip nxt) nxt := by
  rcases h with ⟨hfetch, hdecode, hrun, hexception, hcontrol⟩
  simp [NextRISCV_equation, hfetch, hdecode, hrun, hexception, NextFetch, hcontrol, PC]

/-- Original direct-branch rule over the full native state: clear the function
entry at the unrestricted core key, then update PC to the original word64 target. -/
theorem nextRISCV_branch (s : riscv_state) (w : rawInstType) (fetched : riscv_state)
    (i : instruction) (nxt : riscv_state) (a : BitVec 64)
    (h : Fetch s = (w, fetched) ∧ DecodeAny w = i ∧ Run i fetched = nxt ∧
      nxt.exception = exception.NoException ∧
      nxt.c_NextFetch nxt.procID = some (.BranchTo a)) :
    NextRISCV s = update_pc a
      { nxt with c_NextFetch := holUpdate nxt.procID none nxt.c_NextFetch } := by
  rcases h with ⟨hfetch, hdecode, hrun, hexception, hcontrol⟩
  simp [NextRISCV_equation, hfetch, hdecode, hrun, hexception, NextFetch, hcontrol,
    «write'NextFetch»]

/-- Original conditional rule: keep the cleared-control record in both outcomes.
Its identity in the false case is proved from the original NONE premise. -/
theorem nextRISCV_cond_branch (s : riscv_state) (w : rawInstType) (fetched : riscv_state)
    (i : instruction) (nxt : riscv_state) (a : BitVec 64) (b : Bool)
    (h : Fetch s = (w, fetched) ∧ DecodeAny w = i ∧ Run i fetched = nxt ∧
      nxt.exception = exception.NoException ∧
      nxt.c_NextFetch nxt.procID = if b then some (.BranchTo a) else none) :
    NextRISCV s = update_pc (if b then a else nxt.c_PC nxt.procID + Skip nxt)
      { nxt with c_NextFetch := holUpdate nxt.procID none nxt.c_NextFetch } := by
  rcases h with ⟨hfetch, hdecode, hrun, hexception, hcontrol⟩
  cases b with
  | true =>
    simp_all [NextRISCV_equation, NextFetch, «write'NextFetch»]
  | false =>
    have hunchanged : holUpdate nxt.procID none nxt.c_NextFetch = nxt.c_NextFetch := by
      funext key
      simp only [holUpdate]
      split
      · rename_i heq
        subst key
        simpa using hcontrol.symm
      · rfl
    have hstate :
        { nxt with c_NextFetch := holUpdate nxt.procID none nxt.c_NextFetch } = nxt := by
      rw [hunchanged]
    rw [hstate]
    simp [NextRISCV_equation, hfetch, hdecode, hrun, hexception, NextFetch, hcontrol, PC]

end Flapjack.RiscV.L3.Step
