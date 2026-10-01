import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvLemma

/-!
Kernel-only instantiation of the exact HOL `cut_env_lemma`
(`cakeml/compiler/backend/proofs/word_allocProofScript.sml:340-378`) at a
concrete two-key source cut and the identity colour.  The theorem is
conditional and has no direct HOL `EVAL` oracle, so this module only applies
the reviewed Lean statement to concrete data and checks the resulting renamed
target cut, image domain, relation payload and domain equality.  No generated
HOL row is claimed.
-/

namespace Flapjack.Test.WordAllocCutEnvLemmaParity

open Flapjack
open Flapjack.WordAlloc

private def sloc : Spt Nat :=
  sptInsert 1 10 (sptInsert 2 20 Spt.ln)

private def n1 : NumSet := sptInsert 1 () Spt.ln
private def n2 : NumSet := sptInsert 2 () Spt.ln

private def x : Spt Nat :=
  sptUnion (sptInsert 2 20 Spt.ln) (sptInsert 1 10 Spt.ln)

private def f : Nat → Nat := fun n => n

private theorem hcut : wordSemCutEnv (n1, n2) sloc = some x := by decide +kernel

private theorem hf : applyNummapsKey f (n1, n2) = (n1, n2) := by decide +kernel

/-- Applying the reviewed conditional theorem yields a target cut whose result
    is the source cut itself (identity colour) and whose full image domain is
    the identity image of the source-cut domain. -/
example : ∃ y : Spt Nat,
    wordSemCutEnv (applyNummapsKey f (n1, n2)) sloc = some y ∧
    sptDomain y = (fun key => ∃ source, sptDomain x source ∧ f source = key) ∧
    strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key) x y ∧
    sptDomain y = sptDomain x := by
  obtain ⟨y, hy, hdom, hrel, _⟩ := cutEnvLemma n1 n2 sloc sloc x f
    ⟨(fun a b _ _ h => h), hcut, (fun n v hn => hn.2)⟩
  refine ⟨y, hy, hdom, hrel, ?_⟩
  have h1 : wordSemCutEnv (n1, n2) sloc = some y := by rw [hf] at hy; exact hy
  have hyx : y = x := Option.some.inj (h1 ▸ hcut)
  rw [hyx]

/-- Concrete evaluation of the same source cut: the `union e2 e1` payload keeps
    both keys, in ascending association order. -/
private def cutEnvRow : Bool :=
  match wordSemCutEnv (n1, n2) sloc with
  | some y => (sptToAList y).map Prod.fst == [1, 2]
  | none => false

#guard cutEnvRow

def runChecks : IO Bool := do
  if cutEnvRow then
    IO.println "PASS word_alloc cut_env_lemma conditional instantiation"
  else
    IO.println "FAIL word_alloc cut_env_lemma conditional instantiation"
  pure cutEnvRow

end Flapjack.Test.WordAllocCutEnvLemmaParity
