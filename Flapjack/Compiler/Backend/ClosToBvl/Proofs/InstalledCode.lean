import Flapjack.Compiler.Backend.ClosToBvl.SourceExps
import Flapjack.Compiler.Backend.ClosToBvl.Layout.Auxiliary
import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Misc.Sptree

/-! Code installation conditions for the closure-to-BVL value relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Each auxiliary function produced by compilation is present in the code tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_installed_def"]
def codeInstalled (aux : List (Nat × Nat × Bvl.Exp)) (code : Spt (Nat × Bvl.Exp)) : Prop :=
  ∀ entry ∈ aux, sptLookup entry.1 code = some entry.2

/-- If generated recursive entries and their accumulator are installed,
the original accumulator is installed as well. -/
theorem codeInstalled_buildAux (entries : List (Nat × Bvl.Exp)) (i : Nat)
    (aux : List (Nat × Nat × Bvl.Exp)) (code : Spt (Nat × Bvl.Exp))
    (installed : codeInstalled (buildAux i entries aux).2 code) : codeInstalled aux code := by
  obtain ⟨added, result⟩ := buildAux_acc entries i aux
  intro entry member
  apply installed entry
  rw [result]
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
theorem codeInstalled_subspt {aux : List (Nat × Nat × Bvl.Exp)}
    {code1 code2 : Spt (Nat × Bvl.Exp)}
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
