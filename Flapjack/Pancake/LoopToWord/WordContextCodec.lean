import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.LoopToWord
import Flapjack.Misc.Sptree

/-!
# Executed/exact loop-to-word context bridge

The executed `WordContext` stores a list-backed `NatInfoMap`; HOL's
`comp_exp_def` reads an exact `Spt Nat` context. `sptFromAList` preserves the
first-match behavior of the production list for duplicate names. Production
and HOL both map a missing name to register zero, so the context lookup bridge
is unconditional. This does not alone establish expression/compiler
equivalence.
-/

namespace Flapjack

/-- Render the executed association-list context as the exact Spt carrier used
by the reviewed `findVarHOL`/`compExpHOL` definitions. -/
def wordContextToHOLContext (context : WordContext) : Spt Nat :=
  sptFromAList context.vars

private theorem sptAListLookup_eq_lookupNatInfo (name : Nat)
    (entries : NatInfoMap Nat) :
    sptAListLookup name entries = lookupNatInfo name entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨key, value⟩ := entry
      by_cases hkey : name = key
      · subst key
        simp [sptAListLookup, lookupNatInfo]
      · have hkey' : key ≠ name := Ne.symm hkey
        have hbeq : (key == name) = false := by simp [hkey']
        simp [sptAListLookup, lookupNatInfo, hkey, hbeq, ih]

/-- Exact HOL `find_var` and production `wordFindVar` agree for every context
and name, including absent keys. First-match list lookup agrees with
`sptFromAList`, and both definitions use zero for a missing key. -/
theorem findVarHOL_wordFindVar
    (context : WordContext) (name : Nat) :
    LoopToWord.findVarHOL (wordContextToHOLContext context) name =
      wordFindVar context name := by
  simp only [LoopToWord.findVarHOL, wordContextToHOLContext,
    sptLookup_sptFromAList, sptAListLookup_eq_lookupNatInfo]
  cases hlookup : lookupNatInfo name context.vars <;>
    simp [wordFindVar, hlookup]

/-- Successful-key form retained for callers whose proof already supplies the
lookup result. -/
theorem findVarHOL_wordFindVar_of_lookup
    (context : WordContext) (name value : Nat)
    (_hlookup : lookupNatInfo name context.vars = some value) :
    LoopToWord.findVarHOL (wordContextToHOLContext context) name =
      wordFindVar context name :=
  findVarHOL_wordFindVar context name

/-- On a missing key, both the exact HOL definition and production select
register zero. -/
theorem findVarHOL_wordFindVar_of_missing
    (context : WordContext) (name : Nat)
    (hlookup : lookupNatInfo name context.vars = none) :
    LoopToWord.findVarHOL (wordContextToHOLContext context) name = 0 ∧
      wordFindVar context name = 0 := by
  constructor
  · simp [LoopToWord.findVarHOL, wordContextToHOLContext,
      sptLookup_sptFromAList, sptAListLookup_eq_lookupNatInfo, hlookup]
  · simp [wordFindVar, hlookup]

end Flapjack
