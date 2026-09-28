import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
Kernel-checked replay of the direct original-HOL EVAL rows of
`scripts/hol-probes/crep_to_loop_code_rel_probe.out` against the exact Lean
port `crepToLoopCodeRelExact` (`Flapjack.Pancake.CrepToLoop.StateRel`).

The HOL probe context is
`context FEMPTY (FEMPTY |+ (strlit "f", (42,2))) 0 RISC_V`,
`s_code = FEMPTY |+ (5, ([1;2], Skip))`, and
`t_code = insert 42 ([0;1], Mark Skip) LN`. HOL `crepSem$state.code` (and hence
`code_rel`'s `s_code`) is `funname |-> _`, i.e. `mlstring`-keyed; the probe's
numeral key `5` is the HOL *name* position and EVALs under the un-annotated map
literal. To keep the Lean test type-faithful, `sCode` uses the `MlS` key
`ofString "f"` and `tCode` uses `sptInsert 42`. The critical rows are replayed
verbatim: `funcs.lookup (ofString "f") = some (42,2)`, `args = [0,1]`,
`ocompile nctxt (list_to_num_set [0,1]) .skip = .mark .skip`,
`sptLookup 42 tCode = some ([0,1], ocompile ... .skip)`, and the positive and
negative relation facts.
-/

namespace Flapjack.Test.CrepToLoopCodeRelParity

open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang (MlS)

/-- Exact HOL probe function map: `FEMPTY |+ (strlit "f", (42,2))`. -/
def funcs : HolFiniteMapExact MlS (Nat × Nat) :=
  (HolFiniteMapExact.empty).updateEq (ofString "f", (42, 2))

/-- Exact HOL probe context:
`context FEMPTY (FEMPTY |+ (strlit "f", (42,2))) 0 RISC_V`. -/
def ctxt : CrepToLoopContextExact :=
  { vars := HolFiniteMapExact.empty, funcs := funcs, vmax := 0, target := .riscv }

/-- Exact HOL probe source code map: `FEMPTY |+ (strlit "f", ([1;2], Skip))`
(the probe's un-annotated numeral key `5` is the HOL `funname` position). -/
def sCode : HolFiniteMapExact MlS (List Nat × CrepProgHOL 8) :=
  (HolFiniteMapExact.empty).updateEq (ofString "f", ([1, 2], (.skip : CrepProgHOL 8)))

/-- The per-function context built by `ctxt_fc` for `ns = [1;2]`, `args = [0;1]`. -/
def nctxt : CrepToLoopContextExact := ctxtFcExact ctxt.target funcs [1, 2] [0, 1]

/-- The compiled target body: `ocompile nctxt (list_to_num_set [0;1]) Skip`. -/
def compiledSkip : HolLoopProg 8 :=
  ocompileHOLExact nctxt (listToNumSetHOLExact [0, 1]) (.skip : CrepProgHOL 8)

/-- Exact HOL probe target code map: `insert 42 ([0;1], Mark Skip) LN`. -/
def tCode : Spt (List Nat × HolLoopProg 8) := sptInsert 42 ([0, 1], compiledSkip) Spt.ln

theorem funcsLookupFL (k : MlS) :
    FLOOKUP ctxt.funcs.lookup k = if k = ofString "f" then some (42, 2) else none := by
  simp [FLOOKUP, ctxt, funcs, FUPDATE_HOL]

theorem funcsLookup (k : MlS) :
    ctxt.funcs.lookup k = if k = ofString "f" then some (42, 2) else none := by
  simp [ctxt, funcs, FUPDATE_HOL]

theorem sCodeLookup (k : MlS) :
    sCode.lookup k = if k = ofString "f" then
      some ([1, 2], (.skip : CrepProgHOL 8)) else none := by
  simp [sCode, FUPDATE_HOL]

/-- Kernel-checked positive instance of `code_rel`: the probe's source function
`f` is compiled to `Mark Skip` at label `42` with parameter slots `[0;1]`, so the
`distinct_funcs` clause and the per-entry existential both hold. -/
theorem codeRelPositive : crepToLoopCodeRelExact ctxt sCode tCode := by
  rw [crepToLoopCodeRelExact]
  refine ⟨?_, ?_⟩
  · intro x y n m rm rm' hx hy _
    rw [funcsLookupFL x] at hx
    rw [funcsLookupFL y] at hy
    by_cases hxf : x = ofString "f"
    · by_cases hyf : y = ofString "f"
      · rw [hxf, hyf]
      · rw [if_neg hyf] at hy
        simp at hy
    · rw [if_neg hxf] at hx
      simp at hx
  · intro f ns prog h
    rw [sCodeLookup f] at h
    by_cases hf : f = ofString "f"
    · subst hf
      rw [if_pos rfl] at h
      have h' : ([1, 2], (.skip : CrepProgHOL 8)) = (ns, prog) := Option.some.inj h
      obtain ⟨hns, hprog⟩ := Prod.mk.inj h'
      subst hns
      subst hprog
      refine ⟨42, 2, ?_, ?_, ?_⟩
      · rw [funcsLookup (ofString "f"), if_pos rfl]
      · rfl
      · rw [show sptLookup 42 tCode = some ([0, 1], compiledSkip) from by
            simp [tCode, sptLookup_sptInsert]]
        rfl
    · rw [if_neg hf] at h
      simp at h

/-- Direct Lean instantiation of the tagged HOL `code_rel_intro`: recover the
`distinct_funcs` conjunct and the per-entry universal-existential conclusion
from a `crepToLoopCodeRelExact` witness. -/
theorem codeRelIntroInstantiation :
    crepToLoopDistinctFuncs ctxt.funcs.lookup ∧
      ∀ (f : MlS) (ns : List Nat) (prog : CrepProgHOL 8),
        sCode.lookup f = some (ns, prog) →
          ∃ loc len : Nat,
            ctxt.funcs.lookup f = some (loc, len) ∧
              ns.length = len ∧
                (let args := List.range len
                 let nctxt := ctxtFcExact ctxt.target ctxt.funcs ns args
                 sptLookup loc tCode =
                   some (args, ocompileHOLExact nctxt (listToNumSetHOLExact args) prog)) :=
  crepToLoopCodeRelIntro ctxt sCode tCode codeRelPositive

/-- Directly instantiate the exact HOL `code_rel_intro` port on the positive
probe relation, recovering its `distinct_funcs` clause. -/
example : crepToLoopDistinctFuncs ctxt.funcs.lookup :=
  (crepToLoopCodeRelExact_intro ctxt sCode tCode codeRelPositive).1

/-- The tagged exact `code_rel2_def` port unfolds definitionally to `code_rel`
applied to the `FMAP_MAP2` source-map transform. -/
example :
    crepToLoopCodeRel2Exact ctxt sCode tCode ↔
      crepToLoopCodeRelExact ctxt
        (sCode.map2 (fun entry => (entry.2.1, crepSimpProgHOL entry.2.2)))
        tCode :=
  Iff.rfl

/-- The `FMAP_MAP2` transform on the probe source map: `Skip` is unchanged by
`simp_prog`, so the transformed map has the same lookup as `sCode`. -/
theorem sCodeMap2Lookup (k : MlS) :
    (sCode.map2 (fun entry => (entry.2.1, crepSimpProgHOL entry.2.2))).lookup k =
      if k = ofString "f" then
        some ([1, 2], (.skip : CrepProgHOL 8)) else none := by
  rw [HolFiniteMapExact.lookup_map2, sCodeLookup k]
  by_cases hk : k = ofString "f"
  · subst hk; simp [crepSimpProgHOL]
  · simp [hk]

/-- Kernel-checked positive instance of the tagged exact `code_rel2_def` port:
the `simp_prog`-transformed source map still compiles `f` to `Mark Skip`. -/
theorem codeRel2Positive : crepToLoopCodeRel2Exact ctxt sCode tCode := by
  unfold crepToLoopCodeRel2Exact
  have hmap : sCode.map2 (fun entry => (entry.2.1, crepSimpProgHOL entry.2.2)) =
      sCode := by
    apply HolFiniteMapExact.ext
    funext k
    rw [sCodeMap2Lookup k, sCodeLookup k]
  rw [hmap]
  exact codeRelPositive

/-- The HOL probe row `code_rel_missing_funcs = F`: with an empty function map
the per-entry existential has no target label to return. -/
theorem codeRelMissingFuncs :
    ¬ crepToLoopCodeRelExact { ctxt with funcs := HolFiniteMapExact.empty } sCode tCode := by
  intro hrel
  rw [crepToLoopCodeRelExact] at hrel
  obtain ⟨_, hsecond⟩ := hrel
  obtain ⟨loc, len, hlookup, _⟩ :=
    hsecond (ofString "f") [1, 2] (.skip : CrepProgHOL 8) (by
      rw [sCodeLookup (ofString "f"), if_pos rfl])
  simp at hlookup

/-- A function map at the probe key whose recorded arity (3) disagrees with the
source parameter list length (`[1,2]` has length 2). -/
def funcs3 : HolFiniteMapExact MlS (Nat × Nat) :=
  (HolFiniteMapExact.empty).updateEq (ofString "f", (42, 3))

theorem funcs3Lookup (k : MlS) :
    funcs3.lookup k = if k = ofString "f" then some (42, 3) else none := by
  simp [funcs3, FUPDATE_HOL]

/-- The HOL probe row `code_rel_len_mismatch = F`: the recorded arity disagrees
with `LENGTH ns`, so the per-entry length conjunct fails. -/
theorem codeRelLenMismatch :
    ¬ crepToLoopCodeRelExact { ctxt with funcs := funcs3 } sCode tCode := by
  intro hrel
  rw [crepToLoopCodeRelExact] at hrel
  obtain ⟨_, hsecond⟩ := hrel
  obtain ⟨loc, len, hlookup, hlen, _⟩ :=
    hsecond (ofString "f") [1, 2] (.skip : CrepProgHOL 8) (by
      rw [sCodeLookup (ofString "f"), if_pos rfl])
  rw [funcs3Lookup (ofString "f"), if_pos rfl] at hlookup
  have h' : (42, 3) = (loc, len) := Option.some.inj hlookup
  obtain ⟨hloc, hlen'⟩ := Prod.mk.inj h'
  subst hloc
  subst hlen'
  simp at hlen

/-! ### Component rows -/

example : funcs.lookup (ofString "f") = some (42, 2) := rfl
example : (List.range 2) = [0, 1] := rfl
example : compiledSkip = .mark .skip := by
  simp only [compiledSkip, ocompileHOLExact, compileHOLExact, optimiseHOL, compHOL,
    markAllHOL, loopCallCompHOL, shrinkHOL]
example : sptLookup 42 tCode = some ([0, 1], compiledSkip) := by
  simp [tCode, sptLookup_sptInsert]

/-! ### Executable guards mirroring the probe rows -/

def funcsLookupGuard : Bool :=
  funcs.lookup (ofString "f") == some (42, 2)

def paramSlotsGuard : Bool :=
  (List.range 2) == [0, 1]

def skipCompileGuard : Bool :=
  match compiledSkip with
  | .mark .skip => true
  | _ => false

def targetLookupGuard : Bool :=
  match sptLookup 42 tCode with
  | some ([0, 1], compiled) =>
      (match compiled with
      | .mark .skip => true
      | _ => false)
  | _ => false

def codeRelParityGuard : Bool :=
  funcsLookupGuard && paramSlotsGuard && skipCompileGuard && targetLookupGuard

#guard codeRelParityGuard

def runChecks : IO Bool := do
  let checks := [
    ("HOL code_rel funcs lookup = SOME (42,2)", funcsLookupGuard),
    ("HOL code_rel args = [0; 1]", paramSlotsGuard),
    ("HOL code_rel skip compile = Mark Skip", skipCompileGuard),
    ("HOL code_rel target lookup = SOME ([0; 1], Mark Skip)", targetLookupGuard)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  IO.println "PASS crepToLoopCodeRelExact positive relation (kernel-checked)"
  IO.println "PASS crepToLoopCodeRelExact missing-funcs counterexample (kernel-checked)"
  IO.println "PASS crepToLoopCodeRelExact length-mismatch counterexample (kernel-checked)"
  IO.println "PASS HOL code_rel_intro instantiation recovers both conjuncts (kernel-checked)"
  IO.println "PASS crepToLoopCodeRel2Exact definitionally unfolds to code_rel over FMAP_MAP2 (kernel-checked)"
  IO.println "PASS crepToLoopCodeRel2Exact positive relation on probe fixture (kernel-checked)"
  pure (checks.all Prod.snd)

end Flapjack.Test.CrepToLoopCodeRelParity
