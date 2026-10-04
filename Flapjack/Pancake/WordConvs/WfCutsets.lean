import Flapjack.HolRef
import Flapjack.Pancake.WordLang

/-!
# wordConvs well-formed cut sets

Counterpart of `wordConvsScript.sml:347-375` (`wf_names_def`,
`wf_cutsets_def`) on the exact `WordLangProgHOL` carrier. HOL `sptree$wf` is
the reviewed `sptWf`; HOL booleans are rendered as propositions.
-/

namespace Flapjack

/-- Exact HOL `wf_names_def` (`wordConvsScript.sml:347-350`): both components
are `sptree$wf`, for arbitrary payload types as in HOL (`t : 'a spt # 'b spt`). -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "wf_names_def"]
def wfNames {α β : Type} (t : Spt α × Spt β) : Prop :=
  sptWf t.1 = true ∧ sptWf t.2 = true

/-- Exact HOL `wf_cutsets_def` (`wordConvsScript.sml:352-375`), clause by
clause: the cut sets of `Alloc`, `Install`, a returning `Call` (with its return
handler and optional exception handler program) and `FFI` are well formed,
`MustTerminate`, `Seq` and `If` recurse into their sub-programs, `Loop` also
requires both live sets to be `wf`, and every other statement is `T`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wfCutsets {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | .alloc _ s => wfNames s
  | .install _ _ _ _ s => wfNames s
  | .call none _ _ _ => True
  | .call (some (_v, cutset, retHandler, _l1, _l2)) _dest _args h =>
      wfNames cutset ∧ wfCutsets retHandler ∧
        (match h with
          | none => True
          | some (_v, prog, _l1, _l2) => wfCutsets prog)
  | .ffi _ _ _ _ _ args => wfNames args
  | .mustTerminate s => wfCutsets s
  | .seq s1 s2 => wfCutsets s1 ∧ wfCutsets s2
  | .loop names p exitNames => sptWf names = true ∧ sptWf exitNames = true ∧ wfCutsets p
  | .ite _ _ _ e2 e3 => wfCutsets e2 ∧ wfCutsets e3
  | _ => True

end Flapjack
