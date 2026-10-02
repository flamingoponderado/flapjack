import Flapjack.Misc.Sptree

namespace Flapjack

private def leftTree {α : Type} : Spt α → Spt α
  | .bn left _ => left
  | .bs left _ _ => left
  | _ => .ln

private def rightTree {α : Type} : Spt α → Spt α
  | .bn _ right => right
  | .bs _ _ right => right
  | _ => .ln

private theorem lookupLeft {α : Type} (tree : Spt α) (key : Nat) :
    sptLookup (2*key+2) tree = sptLookup key (leftTree tree) := by
  have nonzero : 2*key+2 ≠ 0 := by omega
  have parity : (2*key+2)%2 = 0 := by omega
  have half : (2*key+1)/2 = key := by omega
  cases tree <;> simp [sptLookup,leftTree,parity,half]

private theorem lookupRight {α : Type} (tree : Spt α) (key : Nat) :
    sptLookup (2*key+1) tree = sptLookup key (rightTree tree) := by
  have nonzero : 2*key+1 ≠ 0 := by omega
  have parity : (2*key+1)%2 ≠ 0 := by omega
  have half : (2*key+1-1)/2 = key := by omega
  cases tree <;> simp [sptLookup,rightTree]

private theorem foldEmpty {α : Type} (tree : Spt α)
    (empty : ∀ key, sptLookup key tree = none)
    (index : Nat) (accumulator : List (Nat × α)) :
    sptFoldi (fun key value entries => (key,value)::entries) index accumulator tree = accumulator := by
  induction tree generalizing index accumulator with
  | ln => rfl
  | ls value => simpa [sptLookup] using empty 0
  | bn left right leftIH rightIH =>
    have leftEmpty : ∀ key, sptLookup key left = none := by
      intro key; simpa only [lookupLeft,leftTree] using empty (2*key+2)
    have rightEmpty : ∀ key, sptLookup key right = none := by
      intro key; simpa only [lookupRight,rightTree] using empty (2*key+1)
    simp only [sptFoldi,leftIH leftEmpty,rightIH rightEmpty]
  | bs left value right leftIH rightIH => simpa [sptLookup] using empty 0

/-- Flapjack codec infrastructure: native ordered enumeration is determined by
all key lookups even for unrestricted trees with empty internal branches. This
is not HOL's wf-guarded `fromAList_toAList` tree equality and has no independent
HOL original. It establishes order, not merely entry-set equivalence. -/
theorem sptFoldiEnumerationExt {α : Type} (left right : Spt α)
    (same : ∀ key, sptLookup key left = sptLookup key right)
    (index : Nat) (accumulator : List (Nat × α)) :
    sptFoldi (fun key value entries => (key,value)::entries) index accumulator left =
      sptFoldi (fun key value entries => (key,value)::entries) index accumulator right := by
  induction left generalizing right index accumulator with
  | ln =>
    symm
    apply foldEmpty
    intro key
    exact (same key).symm
  | ls value =>
    have root := same 0
    have emptyLeft : ∀ key, sptLookup key (leftTree right) = none := by
      intro key
      have h := same (2*key+2)
      rw [lookupLeft,lookupLeft] at h
      exact h.symm
    have emptyRight : ∀ key, sptLookup key (rightTree right) = none := by
      intro key
      have h := same (2*key+1)
      rw [lookupRight,lookupRight] at h
      exact h.symm
    cases right <;> simp only [sptLookup] at root
    · cases root
    · cases root; rfl
    · cases root
    · cases root
      simp only [leftTree,rightTree] at emptyLeft emptyRight
      simp only [sptFoldi,foldEmpty _ emptyLeft,foldEmpty _ emptyRight]
  | bn left rightChild leftIH rightIH =>
    have root := same 0
    have leftSame : ∀ key, sptLookup key left = sptLookup key (leftTree right) := by
      intro key; simpa only [lookupLeft,leftTree] using same (2*key+2)
    have rightSame : ∀ key, sptLookup key rightChild = sptLookup key (rightTree right) := by
      intro key; simpa only [lookupRight,rightTree] using same (2*key+1)
    cases right <;> simp only [sptLookup] at root
    · simp only [leftTree,rightTree] at leftSame rightSame
      simp only [sptFoldi,leftIH _ leftSame,rightIH _ rightSame]
    · cases root
    · simp only [leftTree,rightTree] at leftSame rightSame
      simp only [sptFoldi,leftIH _ leftSame,rightIH _ rightSame]
    · cases root
  | bs left value rightChild leftIH rightIH =>
    have root := same 0
    have leftSame : ∀ key, sptLookup key left = sptLookup key (leftTree right) := by
      intro key; simpa only [lookupLeft,leftTree] using same (2*key+2)
    have rightSame : ∀ key, sptLookup key rightChild = sptLookup key (rightTree right) := by
      intro key; simpa only [lookupRight,rightTree] using same (2*key+1)
    cases right <;> simp only [sptLookup] at root
    · cases root
    · cases root
      simp only [leftTree,rightTree] at leftSame rightSame
      simp only [sptFoldi,leftIH _ leftSame,rightIH _ rightSame]
    · cases root
    · cases root
      simp only [leftTree,rightTree] at leftSame rightSame
      simp only [sptFoldi,leftIH _ leftSame,rightIH _ rightSame]

/-- Full ordered native-map observation follows lookup equality. Flapjack
codec infrastructure, with no independent HOL declaration. -/
theorem sptToAListEnumerationExt {α : Type} (left right : Spt α)
    (same : ∀ key, sptLookup key left = sptLookup key right) :
    sptToAList left = sptToAList right := sptFoldiEnumerationExt left right same 0 []

/-- The list/tree codec roundtrip preserves the entire ordered enumeration on
arbitrary trees. Unlike HOL's tree-equality theorem, no wf premise is needed
because this conclusion observes only enumeration. -/
theorem sptToAListFromAListToAList {α : Type} (tree : Spt α) :
    sptToAList (sptFromAList (sptToAList tree)) = sptToAList tree := by
  apply sptToAListEnumerationExt
  intro key
  exact sptLookup_sptFromAList_sptToAList key tree

end Flapjack
