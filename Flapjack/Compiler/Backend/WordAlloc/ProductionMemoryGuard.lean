module

public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

@[expose] public section

namespace Flapjack.WordAlloc

/-- Native-carrier rendering of the additional production memory guard.
This predicate has no HOL original and is not an allocation correctness
hypothesis: it records the present runtime domain that must be discharged
separately when connecting the executed caller to the full HOL statement. -/
def nativeMemorySupported {α : Type u} : WordLangProgHOL α → Bool
  | .inst (.mem .load16 _ _) | .inst (.mem .store16 _ _) => false
  | .seq first second => nativeMemorySupported first && nativeMemorySupported second
  | .ite _ _ _ first second => nativeMemorySupported first && nativeMemorySupported second
  | .loop _ body _ | .mustTerminate body => nativeMemorySupported body
  | .call returns _ _ handler =>
      (match returns with
       | none => true
       | some (_, _, body, _, _) => nativeMemorySupported body) &&
      (match handler with
       | none => true
       | some (_, body, _, _) => nativeMemorySupported body)
  | _ => true
termination_by program => sizeOf program

end Flapjack.WordAlloc
