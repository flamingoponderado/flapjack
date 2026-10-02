import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Compiler

namespace Flapjack.Test.WordToStackAllocCompilerParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.AllocArgs

/- Thirty-five nested-program original theorem applications, matched by the full
Lean theorem at the same inputs. These are not direct EVAL observations or a
cross-language equivalence proof. Arbitrary assembler configurations remain. -/

-- aac_1_must
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.mustTerminate (.seq (.alloc 999 (.ln,.ln)) .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_1_loop
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.loop (.bn .ln .ln) (.alloc 999 (.ln,.ln)) (.bs .ln () .ln))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_1_seq
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.seq (.mustTerminate .tick) (.alloc 999 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_1_if
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.ite .equal 999 (.imm 7) (.alloc 999 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_1_tail
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.call none none [2,4,6] (some (999,.alloc 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_1_ret
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 999 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_1_handler
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (999,.alloc 999 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_2_must
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.mustTerminate (.seq (.alloc 999 (.ln,.ln)) .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_2_loop
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.loop (.bn .ln .ln) (.alloc 999 (.ln,.ln)) (.bs .ln () .ln))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_2_seq
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.seq (.mustTerminate .tick) (.alloc 999 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_2_if
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.ite .equal 999 (.imm 7) (.alloc 999 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_2_tail
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.call none none [2,4,6] (some (999,.alloc 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_2_ret
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 999 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_2_handler
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (999,.alloc 999 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_8_must
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.mustTerminate (.seq (.alloc 999 (.ln,.ln)) .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_8_loop
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.loop (.bn .ln .ln) (.alloc 999 (.ln,.ln)) (.bs .ln () .ln))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_8_seq
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.seq (.mustTerminate .tick) (.alloc 999 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_8_if
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.ite .equal 999 (.imm 7) (.alloc 999 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_8_tail
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.call none none [2,4,6] (some (999,.alloc 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_8_ret
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 999 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_8_handler
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (999,.alloc 999 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_64_must
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.mustTerminate (.seq (.alloc 999 (.ln,.ln)) .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_64_loop
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.loop (.bn .ln .ln) (.alloc 999 (.ln,.ln)) (.bs .ln () .ln))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_64_seq
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.seq (.mustTerminate .tick) (.alloc 999 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_64_if
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.ite .equal 999 (.imm 7) (.alloc 999 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_64_tail
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.call none none [2,4,6] (some (999,.alloc 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_64_ret
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 999 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_64_handler
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (999,.alloc 999 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_80_must
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.mustTerminate (.seq (.alloc 999 (.ln,.ln)) .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_80_loop
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.loop (.bn .ln .ln) (.alloc 999 (.ln,.ln)) (.bs .ln () .ln))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_80_seq
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.seq (.mustTerminate .tick) (.alloc 999 (.ln,.ln)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_80_if
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.ite .equal 999 (.imm 7) (.alloc 999 (.ln,.ln)) (.mustTerminate .tick))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_80_tail
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.call none none [2,4,6] (some (999,.alloc 999 (.ln,.ln),7,8)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_80_ret
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.call (some ([2,4,6],(.ln,.ln),.alloc 999 (.ln,.ln),7,8)) (some 17) [2,4] none)
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

-- aac_80_handler
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.call (some ([],(.ln,.ln),.mustTerminate .tick,7,8)) none [] (some (999,.alloc 999 (.ln,.ln),9,10)))
    (.append (.list [4]) (.list [7]),17) (2,7,9)).1 :=
  wordToStackAllocArg conf false _ _ _ rfl

#print axioms Flapjack.WordToStackProofs.AllocArgs.wordToStackAllocArg
end Flapjack.Test.WordToStackAllocCompilerParity
