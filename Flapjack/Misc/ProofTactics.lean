module

public import Lean

/-!
# Shared proof tactics

Flapjack proof infrastructure with no HOL declaration: tactic macros that
several backend proof modules share. They live here rather than in
`Flapjack/HolRef.lean`, which carries only the `@[hol]` cross-reference
attribute and its audit commands.
-/

/- Unfold a definition in the `run` hypothesis, split every match in it, and
close all resulting branches with `simp_all`. Generic proof support shared by
the backend semantics proofs (Flapjack-specific, with no HOL declaration).

Hygiene is disabled on purpose: the hypothesis is the conventional `run` of
the surrounding proof. -/
set_option hygiene false in
macro "unfoldSplit" f:ident : tactic =>
  `(tactic| (
    unfold $f at run
    repeat' split at run
    all_goals simp_all))
