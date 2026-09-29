import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.LoopToWord
import Flapjack.Misc.Sptree

/-!
# Executed/exact loop-to-word context bridge

The executed `WordContext` stores a list-backed `NatInfoMap`; HOL's
`comp_exp_def` reads an exact `Spt Nat` context. `sptFromAList` preserves the
first-match behavior of the production list for duplicate names. A successful
lookup therefore agrees exactly. The missing-key defaults differ (production
keeps the source name, HOL returns register zero), so the bridge deliberately
does not claim unconditional lookup equality or compiler equivalence.
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

/-- On any name present in the executed context, exact HOL `find_var` and
production `wordFindVar` choose the same register. This is the premise needed
before using `compExpHOL` as an executed replacement. -/
theorem findVarHOL_wordFindVar_of_lookup
    (context : WordContext) (name value : Nat)
    (hlookup : lookupNatInfo name context.vars = some value) :
    LoopToWord.findVarHOL (wordContextToHOLContext context) name =
      wordFindVar context name := by
  simp [LoopToWord.findVarHOL, wordContextToHOLContext, wordFindVar,
    sptLookup_sptFromAList, sptAListLookup_eq_lookupNatInfo, hlookup]

/-- On a missing name, the two actual context carriers expose their different
default behaviors: production leaves the name unchanged, HOL selects zero. -/
theorem findVarHOL_wordFindVar_of_missing
    (context : WordContext) (name : Nat)
    (hlookup : lookupNatInfo name context.vars = none) :
    LoopToWord.findVarHOL (wordContextToHOLContext context) name = 0 ∧
      wordFindVar context name = name := by
  constructor
  · simp [LoopToWord.findVarHOL, wordContextToHOLContext,
      sptLookup_sptFromAList, sptAListLookup_eq_lookupNatInfo, hlookup]
  · simp [wordFindVar, hlookup]

/-- The missing-name behavior is a concrete obstacle to unconditional routing:
for a nonzero absent name, exact HOL compilation and production context lookup
are observably different. -/
theorem findVarHOL_wordFindVar_mismatch_of_missing
    (context : WordContext) (name : Nat) (hname : name ≠ 0)
    (hlookup : lookupNatInfo name context.vars = none) :
    LoopToWord.findVarHOL (wordContextToHOLContext context) name ≠
      wordFindVar context name := by
  obtain ⟨hhol, hprod⟩ := findVarHOL_wordFindVar_of_missing context name hlookup
  rw [hhol, hprod]
  exact hname.symm

end Flapjack
