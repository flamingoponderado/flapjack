import Flapjack.Pancake.LoopToWord.WordContextCodec

/-!
# Coverage of the executed comp_func variable context

These are Flapjack-specific bridge lemmas, not ports of an individual HOL
declaration. They establish that the context built by the executed
`loopToWordCompContext` contains every source name collected by
`loopReferencedVars`; this is the successful-lookup premise needed by
`findVarHOL_wordFindVar_of_lookup` when routing expression compilation through
the exact `compExpHOL` definition. They do not establish expression/compiler
equivalence. Both the HOL and production find_var return zero for a missing
name; coverage is needed to establish the intended mapped name, not to hide
a difference in missing-name behavior.
-/

namespace Flapjack

open LoopToWord

private theorem foldlMaxGeStart : ∀ (names : List Nat) (acc : Nat),
    acc ≤ names.foldl max acc
  | [], acc => by simp
  | head :: names, acc => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _)
        (foldlMaxGeStart names (max acc head))

private theorem foldlMaxMonotoneStart : ∀ (names : List Nat) (left right : Nat),
    left ≤ right → names.foldl max left ≤ names.foldl max right
  | [], _, _, h => h
  | head :: names, left, right, h => by
      simp only [List.foldl_cons]
      apply foldlMaxMonotoneStart names (max left head) (max right head)
      omega

private theorem memLeFoldlMax : ∀ (names : List Nat) (name : Nat),
    name ∈ names → name ≤ names.foldl max 0
  | [], _, h => by simp at h
  | head :: tail, name, h => by
      simp only [List.mem_cons] at h
      simp only [List.foldl_cons]
      rcases h with hEq | htail
      · rw [hEq]
        exact Nat.le_trans (Nat.le_max_right _ _)
          (foldlMaxGeStart tail (max 0 head))
      · exact Nat.le_trans (memLeFoldlMax tail name htail)
          (foldlMaxMonotoneStart tail 0 (max 0 head) (Nat.zero_le _))

private theorem lookupFallbackSomeZero {names : List Nat} {name : Nat}
    (hname : name ∈ names) :
    lookupNatInfo name (sourceFallbackContext names) = some 0 := by
  induction names with
  | nil => simp at hname
  | cons head tail ih =>
      simp only [List.mem_cons] at hname
      by_cases hkey : head = name
      · subst name
        simp [sourceFallbackContext, lookupNatInfo]
      · have htail : name ∈ tail := hname.resolve_left (Ne.symm hkey)
        have hbeq : (head == name) = false := by simp [hkey]
        simp [sourceFallbackContext, lookupNatInfo, hbeq, ih htail]

private theorem lookupNatInfo_insertVar_ne_none {name key register : Nat}
    {context : NatInfoMap Nat}
    (hlookup : lookupNatInfo name context ≠ none) :
    lookupNatInfo name (insertVar key register context) ≠ none := by
  by_cases hkey : key == name <;>
    simp [insertVar, lookupNatInfo, hkey, hlookup]

private theorem lookupNatInfo_makeCtxt_ne_none
    (name next : Nat) (names : List Nat) (context : NatInfoMap Nat)
    (hlookup : lookupNatInfo name context ≠ none) :
    lookupNatInfo name (makeCtxt next names context) ≠ none := by
  induction names generalizing next context with
  | nil => simpa [makeCtxt] using hlookup
  | cons key names ih =>
      simp only [makeCtxt]
      apply ih
      exact lookupNatInfo_insertVar_ne_none hlookup

private theorem lookupNatInfo_fallback_range {name maximum : Nat}
    (hname : name ≤ maximum) :
    lookupNatInfo name (sourceFallbackContext (List.range (maximum + 1))) =
      some 0 := by
  apply lookupFallbackSomeZero
  apply List.mem_range.mpr
  omega

/-- Every source name collected by `loopReferencedVars` has a successful
lookup in the executed `comp_func` context. The fallback prefix is deliberately
wide enough to contain those source names; explicit parameter/local bindings
may shadow it but cannot turn a successful lookup into a miss. -/
theorem loopToWordCompContext_lookup_of_referenced
    (params : List Nat) (body : LoopProg α) (name : Nat)
    (hname : name ∈ loopReferencedVars body) :
    (lookupNatInfo name (loopToWordCompContext params body)).isSome := by
  have hnames : name ∈ params ++ loopAccVars body [] ++ loopReferencedVars body :=
    by simp [hname]
  have hbound := memLeFoldlMax
    (params ++ loopAccVars body [] ++ loopReferencedVars body) name hnames
  have hfallback := lookupNatInfo_fallback_range hbound
  have hfallback' :
      lookupNatInfo name
        (sourceFallbackContext
          (List.range ((params ++ loopAccVars body [] ++ loopReferencedVars body).foldl
            max 0 + 1))) ≠ none := by
    rw [hfallback]
    simp
  unfold loopToWordCompContext
  exact Option.isSome_iff_ne_none.mpr
    (lookupNatInfo_makeCtxt_ne_none name 2 _ _ hfallback')

/-- On every name the executed source analysis includes in the compiled body,
the exact Spt context and list-backed production context choose the same
register. The remaining production-route obligation is expression/compiler
correspondence, not context coverage. -/
theorem findVarHOL_wordFindVar_of_loopToWordCompContext_referenced
    (params : List Nat) (body : LoopProg α) (name : Nat)
    (hname : name ∈ loopReferencedVars body) :
    LoopToWord.findVarHOL
        (wordContextToHOLContext
          { vars := loopToWordCompContext params body }) name =
      wordFindVar { vars := loopToWordCompContext params body } name := by
  obtain ⟨value, hlookup⟩ := Option.isSome_iff_exists.mp
    (loopToWordCompContext_lookup_of_referenced params body name hname)
  exact findVarHOL_wordFindVar_of_lookup
    { vars := loopToWordCompContext params body } name value hlookup

end Flapjack
