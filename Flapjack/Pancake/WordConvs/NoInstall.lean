import Flapjack.Pancake.WordConvs.NotCreated

namespace Flapjack

/-- Complete 26-clause source conjunction for the accepted no-install predicate.
Source comparisons of normalized Install with distinct constructors simplify to
true; its self-comparison simplifies to false. In particular the ShareInst
comparison is independent of every possible source ARB memory operation; no
representative or extra premise is assumed. All original constructor inputs and
shared free variables are retained. HOL Bool equality/conjunction uses Lean
Bool equality/and, with leaf propositions represented by equality to true. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_install_def"
  (words_as_type_indexed_bitvec)]
theorem noInstallDef {width : Nat} [NeZero width]
    (p p1 p2 c : WordLangProgHOL (BitVec width))
    (names exitNames : Spt Unit) (v0 : Cmp) (v1 : Nat) (v2 : WordRegImm (BitVec width))
    (r : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (v3 : Nat) (v4 : WordLangCutsetsHOL) (v5 l : Nat)
    (v6 : WordMemOp) (v7 : Nat) (v8 : WordLangExpHOL (BitVec width))
    (v9 v10 v11 v12 : Nat) (v13 : WordLangCutsetsHOL)
    (v18 : Nat) (v19 : List (Nat × Nat)) (v20 : WordLangInst (BitVec width))
    (v21 : Nat) (v22 : WordLangExpHOL (BitVec width)) (v23 : Nat) (v24 v25 : WordStoreHOL)
    (v26 v27 : WordLangExpHOL (BitVec width)) (v28 : Nat)
    (v46 v47 v48 v49 : Nat) (v50 : List (Bool × BitVec width))
    (v51 v52 : Nat) (v53 : List Nat) (v54 v55 : Nat) (v56 : BinOp) (v57 v58 : Nat)
    (v66 v67 v68 v69 : Nat) (v70 : Basis.Pure.MlString.MlString)
    (v71 v72 v73 v74 : Nat) (v75 : WordLangCutsetsHOL) :
    (noInstallSubprogsHOL (.mustTerminate p) = noInstallSubprogsHOL p) ∧
    (noInstallSubprogsHOL (.seq p1 p2) = (noInstallSubprogsHOL p1 && noInstallSubprogsHOL p2)) ∧
    (noInstallSubprogsHOL (.loop names c exitNames) = noInstallSubprogsHOL c) ∧
    (noInstallSubprogsHOL (.ite v0 v1 v2 p1 p2) = (noInstallSubprogsHOL p1 && noInstallSubprogsHOL p2)) ∧
    (noInstallSubprogsHOL (.call r dest args h) =
      ((match r with | none => true | some (_,_,body,_,_) => noInstallSubprogsHOL body) &&
       (match h with | none => true | some (_,body,_,_) => noInstallSubprogsHOL body))) ∧
    noInstallSubprogsHOL (width := width) (.alloc v3 v4) = true ∧
    noInstallSubprogsHOL (width := width) (.locValue v5 l) = true ∧
    noInstallSubprogsHOL (.shareInst v6 v7 v8) = true ∧
    noInstallSubprogsHOL (width := width) (.install v9 v10 v11 v12 v13) = false ∧
    noInstallSubprogsHOL (width := width) .skip = true ∧
    noInstallSubprogsHOL (width := width) (.move v18 v19) = true ∧
    noInstallSubprogsHOL (.inst v20) = true ∧
    noInstallSubprogsHOL (.assign v21 v22) = true ∧
    noInstallSubprogsHOL (width := width) (.get v23 v24) = true ∧
    noInstallSubprogsHOL (.set v25 v26) = true ∧
    noInstallSubprogsHOL (.store v27 v28) = true ∧
    noInstallSubprogsHOL (.storeConsts v46 v47 v48 v49 v50) = true ∧
    noInstallSubprogsHOL (width := width) (.raise v51) = true ∧
    noInstallSubprogsHOL (width := width) (.return v52 v53) = true ∧
    noInstallSubprogsHOL (width := width) (.break v54) = true ∧
    noInstallSubprogsHOL (width := width) (.continue v55) = true ∧
    noInstallSubprogsHOL (width := width) .tick = true ∧
    noInstallSubprogsHOL (width := width) (.opCurrHeap v56 v57 v58) = true ∧
    noInstallSubprogsHOL (width := width) (.codeBufferWrite v66 v67) = true ∧
    noInstallSubprogsHOL (width := width) (.dataBufferWrite v68 v69) = true ∧
    noInstallSubprogsHOL (width := width) (.ffi v70 v71 v72 v73 v74 v75) = true := by
  simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp]
  cases r <;> cases h <;> simp [notCreatedSubprogsWithMemOp]

end Flapjack
