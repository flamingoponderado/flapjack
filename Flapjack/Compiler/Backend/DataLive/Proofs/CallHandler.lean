import Flapjack.Compiler.Backend.DataLive.Proofs.CallNonTail

/-! Exception-handler entry for data liveness. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Once matching callees raise to their fresh handler frames, the handler
simulation applies using the restored live locals and exception context.
This is auxiliary infrastructure, not the complete HOL call case. -/
theorem handlerSimulation_afterRaise {C F : Type}
    (source target sourceLast targetLast sourceNext : State C F)
    (args : List DataSem.Value) (size : Option Nat) (sourceEnv targetEnv : Spt DataSem.Value)
    (body handler : DataLang.Prog) (name : Nat) (value : DataSem.Value) (live : NumSet)
    (result : Option (Result (List DataSem.Value) DataSem.Value))
    (savedRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv }
      (sptDelete name (compile handler live).2))
    (lastRel : stateRel sourceLast targetLast .ln) (exception : exceptionRel source target)
    (sourceRun : DataSem.evaluate body (DataSem.callEnv args size (pushEnv sourceEnv true (decClock source))) =
      (some (.err (.raise value)), sourceLast))
    (targetRun : DataSem.evaluate body (DataSem.callEnv args size (pushEnv targetEnv true (decClock target))) =
      (some (.err (.raise value)), targetLast))
    (handlerRun : DataSem.evaluate handler (setVar name value sourceLast) = (result, sourceNext))
    (notType : result ≠ some (.err (.abort .typeError)))
    (handlerIH : simulationFor (C := C) (F := F) handler live) :
    ∃ targetNext, DataSem.evaluate (compile handler live).1 (setVar name value targetLast) = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  obtain ⟨restored, restoredException⟩ :=
    handlerEntry_afterRaise source target sourceLast targetLast args size sourceEnv targetEnv
      (sptDelete name (compile handler live).2) body value savedRel lastRel exception sourceRun targetRun
  have handlerRel := stateRel_setVar sourceLast targetLast (compile handler live).2 name value restored
  have handlerException : exceptionRel (setVar name value sourceLast) (setVar name value targetLast) := by
    apply exceptionRel_after sourceLast targetLast _ _ _ handlerRel restoredException <;> rfl
  exact handlerIH _ _ result sourceNext handlerRun handlerRel notType handlerException

end Flapjack.Compiler.Backend.DataLive
