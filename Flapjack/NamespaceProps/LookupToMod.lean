module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! From a successful lookup to a successful module lookup. -/
namespace Flapjack.NamespaceHOL

/-- A successful lookup reaches the nested namespace at the identifier's module
path, where the remaining short-name lookup succeeds. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_to_nsLookupMod"]
theorem nsLookup_to_nsLookupMod {M N V : Type} [DecidableEq M] [DecidableEq N]
    (n : Namespace M N V) (v : Ident M N) (t : V) (found : nsLookup n v = some t) :
    ∃ m, nsLookupMod n (idToMods v) = some m ∧ nsLookup m (.short (idToN v)) = some t := by
  induction v generalizing n with
  | short name =>
    exact ⟨n, by simp [idToMods, nsLookupMod], by simpa [idToN] using found⟩
  | long mn rest ih =>
    cases n with
    | bind values modules =>
      simp only [nsLookup] at found
      cases h : modules.lookup mn with
      | none => simp [h] at found
      | some env =>
        simp only [h] at found
        obtain ⟨m, modFound, lookupFound⟩ := ih env found
        exact ⟨m, by simp [idToMods, nsLookupMod, h, modFound],
          by simpa [idToN] using lookupFound⟩

end Flapjack.NamespaceHOL
