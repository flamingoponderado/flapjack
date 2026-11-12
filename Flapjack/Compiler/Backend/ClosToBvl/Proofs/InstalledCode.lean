module

public import Flapjack.Compiler.Backend.ClosToBvl.SourceExps
public import Flapjack.Compiler.Backend.ClosToBvl.Layout.Auxiliary
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Accumulator
public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Misc.Sptree
public import Flapjack.Misc.ListEl
public import Flapjack.FiniteMap.AlistExact.Lookup

@[expose] public section

/-! Code installation conditions for the closure-to-BVL value relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

local instance : Nonempty ClosLang.Exp := ⟨.var .none 0⟩

/-- A compiled expression at an input index comes from a singleton
compilation whose generated auxiliary code occurs contiguously in the final
accumulator. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_EL"]
theorem compileExps_el (ma : Nat) :
    ∀ (ls : List ClosLang.Exp) aux l2 aux2 n,
    (compileExpsHOL ma ls aux = (l2, aux2) ∧ n < ls.length) →
      ∃ auxn aux2n,
        compileExpsHOL ma [holEl n ls] auxn = ([holEl n l2], aux2n) ∧
        aux2n <:+: aux2 := by
  intro ls
  induction ls with
  | nil =>
    intro aux l2 aux2 n h
    simp at h
  | cons e es ih =>
    intro aux l2 aux2 n h
    cases hf : compileExpHOL ma e aux with
    | mk first mid =>
      cases ht : compileExpListHOL ma es mid with
      | mk rest final =>
        have run : (first :: rest, final) = (l2, aux2) := by
          simpa [compileExps_eq_list, compileExpListHOL, hf, ht] using h.1
        cases run
        cases n with
        | zero =>
          refine ⟨aux, mid, ?_, ?_⟩
          · simp [holEl, holHd, compileExps_eq_list, compileExpListHOL, hf]
          · have suffix := compileExpList_auxSuffix ma es mid
            rw [ht] at suffix
            exact suffix.isInfix
        | succ n =>
          have bound : n < es.length := by simpa using h.2
          have tailRun : compileExpsHOL ma es mid = (rest, aux2) := by
            simpa [compileExps_eq_list] using ht
          obtain ⟨auxn, aux2n, compiled, included⟩ := ih mid rest aux2 n ⟨tailRun, bound⟩
          refine ⟨auxn, aux2n, ?_, included⟩
          simpa [holEl_cons_succ] using compiled

private theorem sptAListLookup_eq_holALookup {α : Type} (key : Nat) (entries : List (Nat × α)) :
    sptAListLookup key entries = holALookup entries key := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, value⟩ := entry
    by_cases same : key = name <;> simp [sptAListLookup, holALookup, same, ih]

/-- Distinct source labels select the corresponding paired compiled expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ALOOKUP_lemma"]
theorem alookup_lemma {α β γ : Type} [Nonempty α] [Nonempty β] [Nonempty γ] (m : Nat) :
    ∀ (l1 : List (Nat × α × β)) (l2 : List γ) n k (v : α × β),
      (holEl n l1 = (k, v) ∧ (l1.map Prod.fst).Nodup ∧
        n < l1.length ∧ l2.length = l1.length) →
      holALookup
        ((l1.zip l2).map (fun (entry, e) => (entry.1 + m, entry.2.1, e))) (k + m) =
          some (v.1, holEl n l2) := by
  simp only [← sptAListLookup_eq_holALookup]
  intro l1
  induction l1 with
  | nil =>
    intro l2 n k v h
    simp at h
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    intro l2 n k v h
    cases l2 with
    | nil => simp at h
    | cons out outs =>
      simp only [List.map_cons, List.nodup_cons, List.length_cons, Nat.succ.injEq] at h
      cases n with
      | zero =>
        simp only [holEl, holHd] at h
        obtain ⟨eq, distinct, _, _⟩ := h
        cases eq
        simp [sptAListLookup, holEl, holHd]
      | succ n =>
        have hEl : holEl n rest = (k, v) := by simpa [holEl_cons_succ] using h.1
        have bound : n < rest.length := by omega
        have tail := ih outs n k v ⟨hEl, h.2.1.2, bound, h.2.2.2⟩
        have diff : k ≠ loc := by
          intro eq
          have mem : (k, v) ∈ rest := by
            rw [holEl_eq_getElem n rest bound] at hEl
            exact hEl ▸ List.getElem_mem bound
          apply h.2.1.1
          exact List.mem_map.mpr ⟨(k, v), mem, by simpa using eq⟩
        have shiftDiff : k + m ≠ loc + m := by omega
        simpa [sptAListLookup, shiftDiff, diff, holEl_cons_succ] using tail


/-- Each auxiliary function produced by compilation is present in the code tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_installed_def"]
def codeInstalled {A B : Type} (aux : List (Nat × A × B)) (code : Spt (A × B)) : Prop :=
  ∀ entry ∈ aux, sptLookup entry.1 code = some entry.2

/-- Installed output auxiliary code also installs the input accumulator. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_IMP_code_installed"]
theorem compileExps_codeInstalled (maxApp : Nat) (expressions : List ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (code : Spt (Nat × Bvl.Exp))
    (run : compileExpsHOL maxApp expressions aux = (compiled, finalAux))
    (installed : codeInstalled finalAux code) : codeInstalled aux code := by
  have invariant := compileExps_acc maxApp expressions aux
  rw [run] at invariant
  obtain ⟨_, added, finalEq⟩ := invariant
  intro entry member
  apply installed entry
  rw [finalEq]
  exact List.mem_append_right added member

/-- Recursive closure entry points and the code generated for their bodies are installed. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "closure_code_installed_def"]
def closureCodeInstalled (maxApp : Nat) (code : Spt (Nat × Bvl.Exp))
    (entries : List ((Nat × ClosLang.Exp) × Nat)) (env : List ClosSem.Value) : Prop :=
  ∀ entry ∈ entries,
    let ((n, exp), p) := entry
    n ≤ maxApp ∧ n ≠ 0 ∧
      ∃ aux c aux1,
        compileExpsHOL maxApp [exp] aux = ([c], aux1) ∧
        sptLookup p code = some (n + 1, (codeForReccCase (env.length + entries.length) n c).2) ∧
        codeInstalled aux1 code

@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_installed_subspt"]
theorem codeInstalled_subspt {A B : Type} {aux : List (Nat × A × B)}
    {code1 code2 : Spt (A × B)}
    (installed : codeInstalled aux code1) (sub : sptSubspt code1 code2) :
    codeInstalled aux code2 := by
  intro entry member
  have found := installed entry member
  have mem : sptMem entry.1 code1 := (sptMem_iff_lookup _ _).2 ⟨entry.2, found⟩
  exact (sub entry.1 mem).2.trans found

@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "closure_code_installed_subspt"]
theorem closureCodeInstalled_subspt {maxApp : Nat} {code1 code2 : Spt (Nat × Bvl.Exp)}
    {entries : List ((Nat × ClosLang.Exp) × Nat)} {env : List ClosSem.Value}
    (installed : closureCodeInstalled maxApp code1 entries env) (sub : sptSubspt code1 code2) :
    closureCodeInstalled maxApp code2 entries env := by
  intro ⟨⟨n, exp⟩, p⟩ member
  obtain ⟨bound, positive, aux, c, aux1, compiled, lookup, rest⟩ := installed _ member
  have mem : sptMem p code1 := (sptMem_iff_lookup _ _).2 ⟨_, lookup⟩
  exact ⟨bound, positive, aux, c, aux1, compiled, (sub p mem).2.trans lookup,
    codeInstalled_subspt rest sub⟩

end Flapjack.Compiler.Backend.ClosToBvl
