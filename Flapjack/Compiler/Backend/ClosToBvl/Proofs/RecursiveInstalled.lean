module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InstalledCode
public import Flapjack.Compiler.Backend.Semantics.BvlSem.State
public import Mathlib.Data.List.Enum

@[expose] public section

/-! Indexed installation facts for mutually recursive closure code. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Every compiled recursive function body has a corresponding singleton
compilation whose auxiliary code remains installed in the final code tree.
This is Flapjack infrastructure for the mutual-recursion simulation. -/
theorem compileExpFuns_installed_at (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Bvl.Exp))
    (code : Spt (Nat × Bvl.Exp)) (index arity : Nat) (body : ClosLang.Exp)
    (run : compileExpFunsHOL maxApp functions aux = (compiled, finalAux))
    (installed : codeInstalled finalAux code) (found : functions[index]? = some (arity, body)) :
    ∃ (targetBody : Bvl.Exp) (bodyAux bodyFinalAux : List (Nat × Nat × Bvl.Exp)),
      compiled[index]? = some (arity, targetBody) ∧
      compileExpsHOL maxApp [body] bodyAux = ([targetBody], bodyFinalAux) ∧
      codeInstalled bodyFinalAux code := by
  induction functions generalizing aux finalAux compiled index with
  | nil => simp at found
  | cons first rest ih =>
    obtain ⟨firstArity, firstBody⟩ := first
    cases headRun : compileExpHOL maxApp firstBody aux with
    | mk targetHead auxMiddle =>
      cases tailRun : compileExpFunsHOL maxApp rest auxMiddle with
      | mk targetRest auxLast =>
        have shape : (firstArity, targetHead) :: targetRest = compiled ∧ auxLast = finalAux := by
          simpa [compileExpFunsHOL, headRun, tailRun] using run
        obtain ⟨rfl, rfl⟩ := shape
        cases index with
        | zero =>
          simp at found
          obtain ⟨rfl, rfl⟩ := found
          have suffix := compileExpFuns_auxSuffix maxApp rest auxMiddle
          rw [tailRun] at suffix
          obtain ⟨added, suffixEq⟩ := suffix
          simp only at suffixEq
          have headInstalled : codeInstalled auxMiddle code := by
            intro entry member
            apply installed entry
            rw [← suffixEq]
            exact List.mem_append_right added member
          refine ⟨targetHead, aux, auxMiddle, by simp, ?_, headInstalled⟩
          rw [compileExps_eq_list]
          simp [compileExpListHOL, headRun]
        | succ index =>
          simp only [List.getElem?_cons_succ] at found ⊢
          obtain ⟨targetBody, bodyAux, bodyFinalAux, targetFound, bodyCompiled, bodyInstalled⟩ :=
            ih auxMiddle auxLast targetRest index tailRun installed found
          exact ⟨targetBody, bodyAux, bodyFinalAux, targetFound, bodyCompiled, bodyInstalled⟩

/-- Each source function in a compiled recursive group has its own installed
compiled body at the matching generated label. Its auxiliary code is also
installed. This is the indexed code-layout obligation for constructing the
mutual-recursion closure relation. -/
theorem recursiveFunctions_installed_at (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Bvl.Exp))
    (code : Spt (Nat × Bvl.Exp)) (base envLength index arity : Nat) (body : ClosLang.Exp)
    (run : compileExpFunsHOL maxApp functions aux = (compiled, finalAux))
    (installed : codeInstalled (buildAux base
      (compiled.map (fun (n, exp) => codeForReccCase envLength n exp)) finalAux).2 code)
    (found : functions[index]? = some (arity, body)) :
    ∃ (targetBody : Bvl.Exp) (bodyAux bodyFinalAux : List (Nat × Nat × Bvl.Exp)),
      compileExpsHOL maxApp [body] bodyAux = ([targetBody], bodyFinalAux) ∧
      sptLookup (base + 2 * index) code = some (arity + 1, (codeForReccCase envLength arity targetBody).2) ∧
      codeInstalled bodyFinalAux code := by
  have priorInstalled : codeInstalled finalAux code := by
    let entries := compiled.map (fun (n, exp) => codeForReccCase envLength n exp)
    let built := buildAux base entries finalAux
    obtain ⟨added, suffix⟩ := buildAux_result_suffix base entries finalAux built.1 built.2 (Prod.eta built).symm
    intro entry member
    apply installed entry
    change entry ∈ built.2
    rw [suffix]
    exact List.mem_append_right added member
  obtain ⟨targetBody, bodyAux, bodyFinalAux, targetFound, bodyCompiled, bodyInstalled⟩ :=
    compileExpFuns_installed_at maxApp functions aux finalAux compiled code index arity body run priorInstalled found
  have entryFound : (compiled.map (fun (n, exp) => codeForReccCase envLength n exp))[index]? =
      some (arity + 1, (codeForReccCase envLength arity targetBody).2) := by
    simp [List.getElem?_map, targetFound, codeForReccCase]
  exact ⟨targetBody, bodyAux, bodyFinalAux, bodyCompiled,
    installed _ (buildAux_index _ base finalAux index (arity + 1) _ entryFound), bodyInstalled⟩

local instance : Nonempty ClosLang.Exp := ⟨.var .none 0⟩
local instance : Nonempty Bvl.Exp := ⟨.var 0⟩

namespace RecursiveInstalledCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end RecursiveInstalledCarrier

/-- Each indexed recursive function body and its generated code are installed. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_LIST_IMP_compile_exps_EL"
  (fmap_as_finite_support := [refs])]
theorem compileExpsListImpCompileExpsEl {C F : Type} (exps : List (Nat × ClosLang.Exp)) (aux1 : List (Nat × Nat × Bvl.Exp))
    (c7 : List Bvl.Exp) (aux7 : List (Nat × Nat × Bvl.Exp)) (i n8 n4 : Nat) (aux5 : List (Nat × Nat × Bvl.Exp))
    (numArgs : Nat) (e : ClosLang.Exp) (maxApp k : Nat) (t1 : Flapjack.Compiler.Backend.BvlSem.State C F)
    (premises : holEl i exps = (numArgs, e) ∧
      compileExpsHOL maxApp (exps.map Prod.snd) aux1 = (c7, aux7) ∧ i < exps.length ∧
      buildAux n8 (List.zipWith (codeForReccCase k) (exps.map Prod.fst) c7) aux7 = (n4, aux5) ∧
      codeInstalled aux5 t1.code) :
    ∃ aux c aux1', compileExpsHOL maxApp [e] aux = ([c], aux1') ∧
      sptLookup (n8 + 2*i) t1.code = some (numArgs + 1, (codeForReccCase k numArgs c).2) ∧
      codeInstalled aux1' t1.code := by
  obtain ⟨found, compiled, bound, built, installed⟩ := premises
  have sourceFound : exps[i]? = some (numArgs, e) := by
    rw [List.getElem?_eq_getElem bound]
    rw [holEl_eq_getElem i exps bound] at found
    exact congrArg some found
  have lengths : c7.length = exps.length := by
    simpa using compileExps_length maxApp (exps.map Prod.snd) aux1 c7 aux7 compiled
  have prior : codeInstalled aux7 t1.code := by
    obtain ⟨added, suffix⟩ := buildAux_result_suffix n8 _ aux7 n4 aux5 built
    intro entry member
    apply installed entry
    rw [suffix]
    exact List.mem_append_right added member
  obtain ⟨aux, final, singleton, included⟩ := compileExps_el maxApp (exps.map Prod.snd) aux1 c7 aux7 i
    ⟨compiled, by simpa using bound⟩
  have sourceBody : holEl i (exps.map Prod.snd) = e := by
    rw [holEl_eq_getElem i _ (by simpa using bound)]
    have h := (List.getElem?_eq_some_iff.mp sourceFound).2
    simp [List.getElem_map, h]
  have outputBound : i < c7.length := by omega
  have targetEq : c7[i]? = some (holEl i c7) := by
    rw [List.getElem?_eq_getElem outputBound, holEl_eq_getElem i c7 outputBound]
  have arityFound : (exps.map Prod.fst)[i]? = some numArgs := by
    simp [List.getElem?_map, sourceFound]
  have entryFound : (List.zipWith (codeForReccCase k) (exps.map Prod.fst) c7)[i]? =
      some (numArgs + 1, (codeForReccCase k numArgs (holEl i c7)).2) := by
    simp [List.getElem?_zipWith, arityFound, targetEq, codeForReccCase]
  have lookup : sptLookup (n8 + 2*i) t1.code =
      some (numArgs + 1, (codeForReccCase k numArgs (holEl i c7)).2) := by
    apply installed (n8 + 2*i, numArgs + 1, (codeForReccCase k numArgs (holEl i c7)).2)
    have auxEq := congrArg Prod.snd built
    simp only at auxEq
    rw [← auxEq]
    exact buildAux_index _ n8 aux7 i (numArgs + 1) _ entryFound
  refine ⟨aux, holEl i c7, final, ?_, lookup, ?_⟩
  · simpa [sourceBody] using singleton
  · intro entry member
    exact prior entry (included.sublist.subset member)

/-- The compiler's even-spaced code layout satisfies the whole
`closureCodeInstalled` relation for a recursive group with valid arities.
This is the code-installation component of the mutual-recursion proof. -/
theorem recursiveFunctions_closureCodeInstalled (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Bvl.Exp))
    (code : Spt (Nat × Bvl.Exp)) (label : Nat) (env : List ClosSem.Value)
    (run : compileExpFunsHOL maxApp functions aux = (compiled, finalAux))
    (installed : codeInstalled (buildAux (label + numStubs maxApp)
      (compiled.map (fun (n, exp) => codeForReccCase (env.length + functions.length) n exp)) finalAux).2 code)
    (valid : ∀ n body, (n, body) ∈ functions → n ≤ maxApp ∧ n ≠ 0) :
    closureCodeInstalled maxApp code
      (functions.zipIdx.map (fun (entry, index) => (entry, label + numStubs maxApp + 2 * index))) env := by
  intro entry member
  obtain ⟨⟨⟨arity, body⟩, index⟩, zipped, rfl⟩ := List.mem_map.mp member
  have indexed := List.mem_zipIdx zipped
  simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and] at indexed
  obtain ⟨bound, equal⟩ := indexed
  have sourceFound : functions[index]? = some (arity, body) := by
    rw [List.getElem?_eq_getElem bound]
    rw [← equal]
  have validArity := valid arity body (by rw [equal]; exact List.getElem_mem _)
  obtain ⟨targetBody, bodyAux, bodyFinalAux, bodyCompiled, targetLookup, bodyInstalled⟩ :=
    recursiveFunctions_installed_at maxApp functions aux finalAux compiled code (label + numStubs maxApp)
      (env.length + functions.length) index arity body run installed sourceFound
  refine ⟨validArity.1, validArity.2, bodyAux, targetBody, bodyFinalAux, bodyCompiled, ?_, bodyInstalled⟩
  simpa using targetLookup

/-- The indexed recursive entries retain exactly the source functions and the
corresponding generated label sequence required by the closure relation. -/
theorem recursiveEntries_projections (functions : List (Nat × ClosLang.Exp)) (base : Nat) :
    let entries := functions.zipIdx.map (fun (entry, index) => (entry, base + 2 * index))
    entries.map Prod.fst = functions ∧
    entries.map Prod.snd = (List.range functions.length).map (fun index => base + 2 * index) := by
  constructor
  · simp only [List.map_map, Function.comp_def]
    exact List.zipIdx_map_fst 0 functions
  · simp only [List.map_map, Function.comp_def]
    rw [List.range_eq_range', ← List.zipIdx_map_snd 0 functions, List.map_map]
    rfl

/-- Compiling recursive function bodies preserves the group size. -/
theorem compileExpFuns_length (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Bvl.Exp))
    (run : compileExpFunsHOL maxApp functions aux = (compiled, finalAux)) :
    compiled.length = functions.length := by
  induction functions generalizing aux finalAux compiled with
  | nil => simp [compileExpFunsHOL] at run; simp [← run.1]
  | cons entry rest ih =>
    obtain ⟨arity, body⟩ := entry
    cases headRun : compileExpHOL maxApp body aux with
    | mk targetBody auxMiddle =>
      cases tailRun : compileExpFunsHOL maxApp rest auxMiddle with
      | mk targetRest auxLast =>
        have shape : (arity, targetBody) :: targetRest = compiled ∧ auxLast = finalAux := by
          simpa [compileExpFunsHOL, headRun, tailRun] using run
        obtain ⟨rfl, rfl⟩ := shape
        simpa using congrArg Nat.succ (ih auxMiddle auxLast targetRest tailRun)

end Flapjack.Compiler.Backend.ClosToBvl
