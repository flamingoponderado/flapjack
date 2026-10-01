import Flapjack.Compiler.Backend.WordToStack.NativeConfig

namespace Flapjack.Test.WordToStackNativeConfigParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native

example : ({ bitmapsLength := 0, stackFrameSize := .ln } : Config).bitmapsLength = 0 := rfl
example : ({ bitmapsLength := 0, stackFrameSize := .ln } : Config).stackFrameSize = .ln := rfl
example : ({ bitmapsLength := 17, stackFrameSize := .ls 19 } : Config).stackFrameSize = .ls 19 := rfl
example : ({ bitmapsLength := 3, stackFrameSize := .bn .ln .ln } : Config).stackFrameSize = .bn .ln .ln := rfl
example : ({ bitmapsLength := 5, stackFrameSize := .bs .ln 7 (.ls 9) } : Config).stackFrameSize = .bs .ln 7 (.ls 9) := rfl
example : ({ ({ bitmapsLength := 5, stackFrameSize := .ls 9 } : Config) with
    bitmapsLength := 11 }).stackFrameSize = .ls 9 := rfl
example : ({ ({ bitmapsLength := 5, stackFrameSize := .ls 9 } : Config) with
    stackFrameSize := .bn (.ls 13) .ln }).bitmapsLength = 5 := rfl

end Flapjack.Test.WordToStackNativeConfigParity
