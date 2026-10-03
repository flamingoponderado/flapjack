import Flapjack.Compiler.Backend.Semantics.WordSem.Props.GcFunOk

namespace Flapjack.Test.WordGcFunOkParity

-- Original always_fail_gc row, at every positive word width.
example {width : Nat} [NeZero width] :
    wordGcFunOk (width := width) (fun _ => none) := by
  intro wl m d s wl1 m1 s1 h
  cases h.2

-- A callback that always leaves Handler in its returned store violates the
-- original contract, even with a successful result and unchanged roots.
def keepsHandler {width : Nat} [NeZero width] : WordSemGcFun width :=
  fun (wl, m, _, s) => some (wl, m, s.updateEq (.handler, .word 0))

example {width : Nat} [NeZero width] : ¬ wordGcFunOk (keepsHandler (width := width)) := by
  intro h
  let s : HolFiniteMapExact WordStoreHOL (WordLocW width) :=
    HolFiniteMapExact.empty.updateEq (.handler, .loc 17 19)
  let m : BitVec width → WordLocW width := fun _ => .word 0
  have domain : s.lookup .handler ≠ none := by
    simp [s, HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have result := h [] m (fun _ => false) s [] m
    ((s.eraseEq .handler).updateEq (.handler, .word 0)) ⟨domain, rfl⟩
  simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using result.2.1

-- The existing Handler can be a location: no word-only premise is introduced.
example {width : Nat} [NeZero width] :
    ∀ fallback : WordLocW width,
      (((HolFiniteMapExact.empty : HolFiniteMapExact WordStoreHOL (WordLocW width)).updateEq (.handler, (.loc 17 19 : WordLocW width))).lookup
        .handler).getD fallback = .loc 17 19 := by
  intro fallback
  simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]

end Flapjack.Test.WordGcFunOkParity
