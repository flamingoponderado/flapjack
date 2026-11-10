module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonLabelBound
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InstalledCode.Original
import Flapjack.FiniteMap.AlistExact.Lookup
import Mathlib.Data.List.Nodup

@[expose] public section

/-! Lookup of compiled closure code after whole-program preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps
local instance : Nonempty ClosLang.Exp := ⟨.var .none 0⟩

/-- A preprocessed function has compiled code and its auxiliary code is installed. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ALOOKUP_compile_common"]
theorem alookup_compileCommon (c : Config) (es : List ClosLang.Exp) (c' : Config)
    (prog : List (Nat × Nat × ClosLang.Exp)) (name arity : Nat) (exp : ClosLang.Exp)
    (h : compileCommon c es = (c', prog) ∧ holALookup prog name = some (arity, exp)) :
    ∃ aux1 exp2 aux2,
      compileExpsHOL c.maxApp [exp] aux1 = ([exp2], aux2) ∧
      holALookup (compileProgExpsHOL c.maxApp prog) (name + numStubs c.maxApp) =
        some (arity, exp2) ∧
      codeInstalled aux2 (sptFromAList (compileProgExpsHOL c.maxApp prog)) := by
  have distinct := compileCommon_distinctLocations c es c' prog h.1
  have found := holALookup_member prog name (arity, exp) h.2
  obtain ⟨n, nbound, nth⟩ := List.mem_iff_getElem.mp found
  have heq : holEl n prog = (name, arity, exp) := by
    rw [holEl_eq_getElem n prog nbound]
    exact nth
  cases hrun : compileExpsHOL c.maxApp (prog.map (fun p => p.2.2)) [] with
  | mk compiled emitted =>
    have compiledLength := compileExps_length c.maxApp (prog.map (fun p => p.2.2)) [] compiled emitted hrun
    simp only [List.length_map] at compiledLength
    have element := compileExps_el c.maxApp (prog.map (fun p => p.2.2)) [] compiled emitted n
      ⟨hrun, by simpa using nbound⟩
    have sourceEl : holEl n (prog.map (fun p => p.2.2)) = exp := by
      rw [holEl_eq_getElem n _ (by simpa using nbound), List.getElem_map, nth]
    rw [sourceEl] at element
    obtain ⟨aux1, aux2, single, included⟩ := element
    refine ⟨aux1, holEl n compiled, aux2, single, ?_, ?_⟩
    · have prefixLookup := alookup_lemma (numStubs c.maxApp) prog compiled n name (arity, exp)
        ⟨heq, (List.nodup_append.mp distinct).1, nbound, compiledLength⟩
      rw [compileProgExpsHOL, hrun, holALookup_append, prefixLookup]
    · have programDistinct : ((compileProgExpsHOL c.maxApp prog).map Prod.fst).Nodup := by
        rw [map_fst_compileProg]
        have parts := List.nodup_append.mp distinct
        have reverseNodup : (codeLocations (prog.map (fun p => p.2.2))).reverse.Nodup := by
          simpa only [List.nodup_reverse] using parts.2.1
        have base : (prog.map Prod.fst ++
            (codeLocations (prog.map (fun p => p.2.2))).reverse).Nodup := by
          apply List.Nodup.append parts.1 reverseNodup
          intro x hx hy
          exact parts.2.2 x hx x (by simpa only [List.mem_reverse] using hy) rfl
        exact base.map (fun _ _ eq => by omega)
      apply codeInstalled_fromAList_strong _ _ ⟨programDistinct, ?_⟩
      have emittedInfix : emitted <:+: compileProgExpsHOL c.maxApp prog := by
        rw [compileProgExpsHOL, hrun]
        exact List.infix_append_right
      exact included.trans emittedInfix

end Flapjack.Compiler.Backend.ClosToBvl
