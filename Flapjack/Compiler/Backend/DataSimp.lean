import Flapjack.Compiler.Backend.DataLang.Syntax

/-! Simplify sequencing in data-language programs. -/
namespace Flapjack.Compiler.Backend.DataSimp
open DataLang

/-- Sequence a command with a continuation, dropping a trailing skip. -/
@[hol "cakeml/compiler/backend/data_simpScript.sml" "pSeq_def"]
def pSeq (p : Prog) : Prog → Prog
  | .skip => p
  | q => .seq p q

/-- Distribute a continuation through sequences and discard unreachable code. -/
@[hol "cakeml/compiler/backend/data_simpScript.sml" "simp_def"]
def simp : Prog → Prog → Prog
  | .skip, c => c
  | .return vs, _ => .return vs
  | .raise v, _ => .raise v
  | .seq p q, c => simp p (simp q c)
  | .ifThenElse n p q, c => pSeq (.ifThenElse n (simp p .skip) (simp q .skip)) c
  | .call ret dest args (some (v, handler)), c =>
      pSeq (.call ret dest args (some (v, simp handler .skip))) c
  | p, c => pSeq p c

end Flapjack.Compiler.Backend.DataSimp
