module

public import Flapjack.Compiler.Backend.BviToData.CompileSource

@[expose] public section

/-! The agreement theorem `compileSource_agrees` now lives beside
`compileSource` in `Flapjack/Compiler/Backend/BviToData/CompileSource.lean`:
the `@[csimp]` executable replacement for the noncomputable source definition
must be declared before the `compileExp`/`compilePart`/`compileProg` wrappers,
and it uses that theorem. This module stays as the stable import path for its
consumers. -/
