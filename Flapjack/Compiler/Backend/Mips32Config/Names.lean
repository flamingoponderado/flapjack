import Flapjack.Misc.Sptree
import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.Mips32Config

/-- CakeML's MIPS register names: stack-language register `k` is machine register
`mips32NameLookup k`. Source registers 1-4 are the argument registers `$a0`-`$a3`, source 0
is `$ra`, and the encoder temporaries `$at`/`$fp`, `$zero`, `$sp`, `$gp`, `$k0`/`$k1` and
`$t9` are avoided. The MIPS32 backend reuses the map unchanged: the MIPS32 calling registers
are the same as MIPS64's. -/
@[hol "cakeml/compiler/backend/mips/mips_configScript.sml" "mips_names_def" 10]
def mipsNames : Flapjack.Spt Nat :=
  Flapjack.sptInsert 0 31 (Flapjack.sptInsert 1 4 (Flapjack.sptInsert 2 5
    (Flapjack.sptInsert 3 6 (Flapjack.sptInsert 4 7 (Flapjack.sptInsert 7 2
    (Flapjack.sptInsert 5 24 (Flapjack.sptInsert 6 3 (Flapjack.sptInsert 24 0
    (Flapjack.sptInsert 31 1 .ln)))))))))

/-- Identity-default lookup in `mipsNames` (Flapjack infrastructure). -/
def mips32NameLookup (register : Nat) : Nat :=
  (Flapjack.sptLookup register mipsNames).getD register

end Flapjack.Compiler.Backend.Mips32Config
