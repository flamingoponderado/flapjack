module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.Control
public import Flapjack.Compiler.Backend.WordElim.Proofs.Analysis
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PopEnvConst

@[expose] public section

/-!
# `word_removal_lemma`: helpers for the `Call` case

Flapjack infrastructure for the `Call` case of HOL `word_removal_lemma`
(`word_elimProofScript.sml:1296-1542`): `find_code` reads only a reachable label
(the destination, or the location of the last argument), the body it returns
has its references inside the reachable set (`code_closed`), and the new
locals of `call_env` hold only reachable locations.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open Flapjack.Compiler.Backend.FlatElim

section CallSupport
variable {width : Nat} [NeZero width] {C F : Type}

/-- The label `find_code` reads. -/
def FindCodeLabel {β : Type} (dest : Option Nat) (args : List β)
    (loc : β → Option Nat) (l : Nat) : Prop :=
  dest = some l ∨ (dest = none ∧ ∃ hne : args ≠ [], loc (args.getLast hne) = some l)

/-- `find_code` reads only the code at its label. -/
theorem findCode_congr {Code SS : Type} (dest : Option Nat) (args : List (WordLocW width))
    (c1 c2 : Spt (Nat × Code)) (ss : Spt SS)
    (h : ∀ l, FindCodeLabel dest args (fun v => match v with
      | .loc l 0 => some l | _ => none) l → sptLookup l c1 = sptLookup l c2) :
    wordSemFindCode dest args c1 ss = wordSemFindCode dest args c2 ss := by
  cases dest with
  | some p => simp only [wordSemFindCode, h p (Or.inl rfl)]
  | none =>
    unfold wordSemFindCode
    by_cases hne : args = []
    · subst hne; simp
    · simp only [hne, dite_false]
      split
      · rename_i loc hl
        rw [h loc (Or.inr ⟨rfl, hne, by simp [hl]⟩)]
      · rfl

/-- What `find_code` returns: the body at its label, with `args` or their
    `FRONT`. -/
theorem findCode_some {Code SS : Type} {dest : Option Nat} {args : List (WordLocW width)}
    {code : Spt (Nat × Code)} {ss : Spt SS} {args1 : List (WordLocW width)} {prog : Code}
    {ps : Option SS} (h : wordSemFindCode dest args code ss = some (args1, prog, ps)) :
    (∃ l, FindCodeLabel dest args (fun v => match v with | .loc l 0 => some l | _ => none) l ∧
      ∃ arity, sptLookup l code = some (arity, prog)) ∧
    (args1 = args ∨ args1 = args.dropLast) := by
  cases dest with
  | some p =>
    simp only [wordSemFindCode] at h
    split at h
    · cases h
    · rename_i arity body hl
      split at h
      · cases h
        exact ⟨⟨p, Or.inl rfl, arity, hl⟩, Or.inl rfl⟩
      · cases h
  | none =>
    unfold wordSemFindCode at h
    by_cases hne : args = []
    · simp [hne] at h
    · simp only [hne, dite_false] at h
      split at h
      · rename_i loc hl
        split at h
        · cases h
        · rename_i arity body hlk
          split at h
          · cases h
            exact ⟨⟨loc, Or.inr ⟨rfl, hne, by simp [hl]⟩, arity, hlk⟩, Or.inr rfl⟩
          · cases h
      · cases h

theorem sptAListLookup_eq_holAlookup {α : Type} (key : Nat) :
    ∀ l : List (Nat × α), sptAListLookup key l = holAlookup l key
  | [] => rfl
  | (k, v) :: rest => by
    simp only [sptAListLookup, holAlookup]
    by_cases h : key = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
      exact sptAListLookup_eq_holAlookup key rest

omit [NeZero width] in
/-- A body stored at a reachable label of closed code has its references inside
    the reachable set. -/
theorem codeClosed_findWordRef {reachable : NumSet}
    {code : Spt (Nat × WordLangProgHOL (BitVec width))} (hcc : codeClosed reachable code)
    {l arity : Nat} {prog : WordLangProgHOL (BitVec width)}
    (hl : sptMem l reachable) (hlk : sptLookup l code = some (arity, prog)) :
    sptDomainSet (findWordRef prog) ⊆ sptDomainSet reachable := by
  obtain ⟨code1, rfl, hcl⟩ := hcc
  rw [sptLookup_sptFromAList, sptAListLookup_eq_holAlookup] at hlk
  have ha := lookupAnalyseWordCode code1 l arity prog hlk
  intro m hm
  have hm' : sptMem m (findWordRef prog) := hm
  obtain ⟨u, hu⟩ := (sptMem_iff_lookup m _).mp hm'
  exact hcl l m ⟨hl, Relation.ReflTransGen.single ⟨_, ha, hu⟩⟩

/-- `call_env` with reachable arguments over a state with reachable locations. -/
theorem callEnv_locsIn {R : Nat → Prop} (args : List (WordLocW width)) (ss : Option Nat)
    (s : WordSemStateFiniteExact width C F) (hs : LocsIn R s)
    (ha : ∀ v ∈ args, ∀ n o, v = .loc n o → R n) : LocsIn R (WordSemStateFiniteExact.callEnv args ss s) := by
  intro n hn
  rw [sptMem_findLocState] at hn
  rcases hn with h | h
  · obtain ⟨key, o, hk⟩ := (domainGetLocalsLookup n _).mp h
    exact ha _ (sptLookup_sptFromList2_mem args key _ hk) n o rfl
  · exact hs n ((sptMem_findLocState s n).mpr (Or.inr h))

theorem decClock_withCode (s : WordSemStateFiniteExact width C F)
    (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    decClock { s with code := c } = { decClock s with code := c } := rfl

theorem callEnv_withCode (args : List (WordLocW width)) (ss : Option Nat)
    (s : WordSemStateFiniteExact width C F) (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    WordSemStateFiniteExact.callEnv args ss { s with code := c } =
      { WordSemStateFiniteExact.callEnv args ss s with code := c } := rfl

theorem pushEnv_withCode (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    pushEnv envs h { s with code := c } = { pushEnv envs h s with code := c } := by
  rcases h with _ | ⟨_, _, _, _⟩ <;> rfl

theorem setVars_withCode (ks : List Nat) (vs : List (WordLocW width))
    (s : WordSemStateFiniteExact width C F) (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    setVars ks vs { s with code := c } = { setVars ks vs s with code := c } := rfl

theorem setVar_withCode (k : Nat) (v : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    setVar k v { s with code := c } = { setVar k v s with code := c } := rfl

theorem flushState_withCode (b : Bool)
    (s : WordSemStateFiniteExact width C F) (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    flushState b { s with code := c } = { flushState b s with code := c } := by
  cases b <;> rfl

theorem pushEnv_code_gcFun (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (pushEnv envs h s).code = s.code ∧ (pushEnv envs h s).gcFun = s.gcFun := by
  rcases h with _ | ⟨_, _, _, _⟩ <;> exact ⟨rfl, rfl⟩

/-- Flushing a state whose memory is the original's adds no location. -/
theorem locsWithin_flushState_true_memory (s y : WordSemStateFiniteExact width C F)
    (hm : y.memory = s.memory) (hd : y.mdomain = s.mdomain) :
    LocsWithin (flushState true y) s := by
  intro n hn
  rw [sptMem_findLocState] at hn
  simp only [flushState] at hn
  rcases hn with h | h | h | h
  · simp [getLocals] at h
  · obtain ⟨k, n1, hk⟩ := (domain_get_store n HolFiniteMapExact.empty).mp h
    simp [HolFiniteMapExact.empty] at hk
  · simp [getStack] at h
  · rw [hm, hd] at h
    exact (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inr h)))

theorem noInstall_call_ret' {n : List Nat} {names : WordLangCutsetsHOL}
    {r : WordLangProgHOL (BitVec width)} {l1 l2 : Nat} {dest : Option Nat} {args : List Nat}
    {h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    (hni : noInstallSubprogsHOL (.call (some (n, names, r, l1, l2)) dest args h) = true) :
    noInstallSubprogsHOL r = true := noInstall_call_ret hni

end CallSupport

end Flapjack.Compiler.Backend.WordElim
