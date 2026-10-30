import Flapjack.Compiler.Backend.FlatToClos.Proofs.CompileSafety
import Flapjack.Compiler.Backend.FlatToClos.Proofs.NoMti
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.CompileFlatGlobals
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.NoMat

/-! Composition of source-to-flat and flat-to-closure invariants. -/
namespace Flapjack.Compiler.Backend.FlatToClos

/-- Flapjack composition: source compilation produces pre-MTI closure code,
including the interpreter initializer. This follows from the flat-to-closure
invariant and is not a port of a single HOL theorem. -/
theorem sourceCompileProg_noMti (cfg : SourceToFlat.Config) (ds : List AstHOL.Dec) :
    ∀ e ∈ compileProg (SourceToFlat.compileTotal cfg ds).2, ClosProps.noMti e :=
  compileProg_noMti _

/-- Flapjack composition: the normal source-to-closure path always produces
closure-safe code, including the attached interpreter. This follows from the
separate HOL pass invariants and is not a port of a single HOL theorem. -/
theorem sourceCompileProg_esgcFree (cfg : SourceToFlat.Config) (ds : List AstHOL.Dec) :
    ∀ e ∈ compileProg (SourceToFlat.compileTotal cfg ds).2, ClosProps.esgcFree e :=
  compileProg_esgcFree _ ⟨SourceToFlat.compile_esgcFree cfg ds, SourceToFlat.noMat_compileTotal cfg ds⟩

/-- Flapjack composition: the normal source-to-closure output writes slot zero
once in addition to the shifted source-to-flat writes. This combines pass
invariants and has no single HOL counterpart. -/
theorem sourceCompileProg_setGlobals (cfg : SourceToFlat.Config) (ds : List AstHOL.Dec) :
    ClosProps.elistGlobals (compileProg (SourceToFlat.compileTotal cfg ds).2) =
      FlatProps.unionGlobalBag (fun key => if key = 0 then 1 else 0)
        (shiftGlobalBag (FlatProps.elistGlobals (SourceToFlat.compileTotal cfg ds).2)) :=
  compileProg_setGlobals _ (SourceToFlat.noMat_compileTotal cfg ds)

/-- Flapjack composition: incremental source-to-closure compilation also
preserves closure safety. This combines pass invariants rather than porting a
single HOL theorem. -/
theorem sourceIncCompile_esgcFree {α : Type} (envId : Nat × Nat)
    (cfg : SourceToFlat.Config) (ds : List AstHOL.Dec) :
    ∀ e ∈ (incCompileDecs (α := α) (SourceToFlat.incCompile envId cfg ds).2).1,
      ClosProps.esgcFree e :=
  incCompileDecs_esgcFree _
    ⟨SourceToFlat.incCompile_esgcFree envId cfg ds, SourceToFlat.noMat_incCompile envId cfg ds⟩

/-- Flapjack composition of incremental global-write preservation with the
source-to-flat match-free guarantee; this is not a single HOL theorem. -/
theorem sourceIncCompile_setGlobals {α : Type} (envId : Nat × Nat)
    (cfg : SourceToFlat.Config) (ds : List AstHOL.Dec) :
    ClosProps.elistGlobals (incCompileDecs (α := α) (SourceToFlat.incCompile envId cfg ds).2).1 =
      shiftGlobalBag (FlatProps.elistGlobals (SourceToFlat.incCompile envId cfg ds).2) :=
  incCompileDecs_setGlobals _ (SourceToFlat.noMat_incCompile envId cfg ds)

end Flapjack.Compiler.Backend.FlatToClos
