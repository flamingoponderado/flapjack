module

public import Flapjack.Compiler.Backend.DataToWord.CompleteStubs
public import Flapjack.Compiler.Backend.DataToWord.Total

@[expose] public section

/-! Code-table relation needed by the data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The target code contains exactly the source labels and stub labels; it
contains each stub and the compiled body of each source function. This has
the shape of HOL's `code_rel_def`, but is untagged until the executed `stubs`
and `compileControl` have been source-reviewed against HOL. -/
def codeRel {width : Nat} [NeZero width] (conf : Config)
    (source : Spt (Nat × DataLang.Prog))
    (target : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  sptDomain target = (fun label =>
    sptDomain source label ∨ label ∈ (DataToWord.stubs (width := width) conf).map Prod.fst) ∧
  (∀ entry ∈ DataToWord.stubs (width := width) conf, sptLookup entry.1 target = some entry.2) ∧
  ∀ label arity body, sptLookup label source = some (arity, body) →
    sptLookup label target = some (arity + 1, (compileControl conf label 2 body).1)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
