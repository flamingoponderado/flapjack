module

public import Flapjack.Compiler.Backend.WordBignum.GeneratedMini
public import Flapjack.Compiler.Backend.WordBignum.Compile

@[expose] public section

/-! Generate word stubs from the captured mini-program and executable
mini-compiler. This is not yet the original shallow-to-deep generator. -/
namespace Flapjack.Compiler.Backend.WordBignum

/-- Compile the captured mini-program and assemble its generated entries.
This executable definition has the shape of HOL's generated_bignum_stubs;
it remains untagged until the generated mini-program is source-reviewed. -/
def generatedBignumStubs (width : Nat) [NeZero width] (location : Nat) :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let (body, _, _, (_, installed)) :=
    compile location 2 1 (location + 1, []) (mcIopCode width)
  (location, 1, .seq body (.return 0 [0])) ::
    installed.map fun (_, index, code) => (index, 1, .seq code (.return 0 [0]))

end Flapjack.Compiler.Backend.WordBignum
