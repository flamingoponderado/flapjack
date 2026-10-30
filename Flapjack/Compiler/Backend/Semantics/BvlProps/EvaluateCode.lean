import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyCode
import Flapjack.Misc.Sptree.Subspt

/-! Code-growth prerequisites for the BVL evaluator. -/
namespace Flapjack.Compiler.Backend.BvlProps
open BvlSem Flapjack.SemanticPrimitivesHOL

/-- Successful primitive application preserves every existing code entry.
This is an auxiliary consequence of the BVL primitive definitions, not a
standalone HOL declaration. -/
theorem doApp_code_mono {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state next : State C F) (value : BvlSem.Value)
    (run : doApp op args state = .val (value, next)) : sptSubspt state.code next.code := by
  by_cases install : op = .install
  · subst op
    have code := (doInstall_code (R := BvlSem.Value) args state next value (by simpa [doApp] using run)).1
    rw [code]
    exact sptSubsptUnion _ _
  · have code := (doApp_code op args state next value install run).1
    rw [code]
    intro key member
    exact ⟨member, rfl⟩

end Flapjack.Compiler.Backend.BvlProps
