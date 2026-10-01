import Flapjack.Pancake.WordConvs.NotCreated

namespace Flapjack

/-- Full original 26-clause conjunction with every shared constructor binder.
Normalized constructor inequalities reduce by disjointness, while the rejected
constructor compares the same normalized node with itself. No source binder,
side condition or callback body is specialized. The source ARB memory operation
is either in a distinct-constructor comparison or the same node on both sides;
no choice representative or extra premise is introduced. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_alloc_def"
  (words_as_type_indexed_bitvec)]
theorem noAllocDef {width : Nat} [NeZero width]
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
    (noAllocSubprogsHOL (.mustTerminate p) = noAllocSubprogsHOL p) ∧
    (noAllocSubprogsHOL (.seq p1 p2) = (noAllocSubprogsHOL p1 && noAllocSubprogsHOL p2)) ∧
    (noAllocSubprogsHOL (.loop names c exitNames) = noAllocSubprogsHOL c) ∧
    (noAllocSubprogsHOL (.ite v0 v1 v2 p1 p2) = (noAllocSubprogsHOL p1 && noAllocSubprogsHOL p2)) ∧
    (noAllocSubprogsHOL (.call r dest args h) =
      ((match r with | none => true | some (_,_,body,_,_) => noAllocSubprogsHOL body) &&
       (match h with | none => true | some (_,body,_,_) => noAllocSubprogsHOL body))) ∧
    noAllocSubprogsHOL (width := width) (.alloc v3 v4) = false ∧
    noAllocSubprogsHOL (width := width) (.locValue v5 l) = true ∧
    noAllocSubprogsHOL (.shareInst v6 v7 v8) = true ∧
    noAllocSubprogsHOL (width := width) (.install v9 v10 v11 v12 v13) = true ∧
    noAllocSubprogsHOL (width := width) .skip = true ∧
    noAllocSubprogsHOL (width := width) (.move v18 v19) = true ∧
    noAllocSubprogsHOL (.inst v20) = true ∧
    noAllocSubprogsHOL (.assign v21 v22) = true ∧
    noAllocSubprogsHOL (width := width) (.get v23 v24) = true ∧
    noAllocSubprogsHOL (.set v25 v26) = true ∧
    noAllocSubprogsHOL (.store v27 v28) = true ∧
    noAllocSubprogsHOL (.storeConsts v46 v47 v48 v49 v50) = true ∧
    noAllocSubprogsHOL (width := width) (.raise v51) = true ∧
    noAllocSubprogsHOL (width := width) (.return v52 v53) = true ∧
    noAllocSubprogsHOL (width := width) (.break v54) = true ∧
    noAllocSubprogsHOL (width := width) (.continue v55) = true ∧
    noAllocSubprogsHOL (width := width) .tick = true ∧
    noAllocSubprogsHOL (width := width) (.opCurrHeap v56 v57 v58) = true ∧
    noAllocSubprogsHOL (width := width) (.codeBufferWrite v66 v67) = true ∧
    noAllocSubprogsHOL (width := width) (.dataBufferWrite v68 v69) = true ∧
    noAllocSubprogsHOL (width := width) (.ffi v70 v71 v72 v73 v74 v75) = true := by
  simp [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp]
  cases r <;> cases h <;> simp [notCreatedSubprogsWithMemOp]


/-- Full original 26-clause conjunction with every shared constructor binder.
Normalized constructor inequalities reduce by disjointness, while the rejected
constructor compares the same normalized node with itself. No source binder,
side condition or callback body is specialized. The source ARB memory operation
is either in a distinct-constructor comparison or the same node on both sides;
no choice representative or extra premise is introduced. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_mt_def"
  (words_as_type_indexed_bitvec)]
theorem noMtDef {width : Nat} [NeZero width]
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
    (noMtSubprogsHOL (.mustTerminate p) = false) ∧
    (noMtSubprogsHOL (.seq p1 p2) = (noMtSubprogsHOL p1 && noMtSubprogsHOL p2)) ∧
    (noMtSubprogsHOL (.loop names c exitNames) = noMtSubprogsHOL c) ∧
    (noMtSubprogsHOL (.ite v0 v1 v2 p1 p2) = (noMtSubprogsHOL p1 && noMtSubprogsHOL p2)) ∧
    (noMtSubprogsHOL (.call r dest args h) =
      ((match r with | none => true | some (_,_,body,_,_) => noMtSubprogsHOL body) &&
       (match h with | none => true | some (_,body,_,_) => noMtSubprogsHOL body))) ∧
    noMtSubprogsHOL (width := width) (.alloc v3 v4) = true ∧
    noMtSubprogsHOL (width := width) (.locValue v5 l) = true ∧
    noMtSubprogsHOL (.shareInst v6 v7 v8) = true ∧
    noMtSubprogsHOL (width := width) (.install v9 v10 v11 v12 v13) = true ∧
    noMtSubprogsHOL (width := width) .skip = true ∧
    noMtSubprogsHOL (width := width) (.move v18 v19) = true ∧
    noMtSubprogsHOL (.inst v20) = true ∧
    noMtSubprogsHOL (.assign v21 v22) = true ∧
    noMtSubprogsHOL (width := width) (.get v23 v24) = true ∧
    noMtSubprogsHOL (.set v25 v26) = true ∧
    noMtSubprogsHOL (.store v27 v28) = true ∧
    noMtSubprogsHOL (.storeConsts v46 v47 v48 v49 v50) = true ∧
    noMtSubprogsHOL (width := width) (.raise v51) = true ∧
    noMtSubprogsHOL (width := width) (.return v52 v53) = true ∧
    noMtSubprogsHOL (width := width) (.break v54) = true ∧
    noMtSubprogsHOL (width := width) (.continue v55) = true ∧
    noMtSubprogsHOL (width := width) .tick = true ∧
    noMtSubprogsHOL (width := width) (.opCurrHeap v56 v57 v58) = true ∧
    noMtSubprogsHOL (width := width) (.codeBufferWrite v66 v67) = true ∧
    noMtSubprogsHOL (width := width) (.dataBufferWrite v68 v69) = true ∧
    noMtSubprogsHOL (width := width) (.ffi v70 v71 v72 v73 v74 v75) = true := by
  simp [noMtSubprogsHOL, notCreatedSubprogsWithMemOp]
  cases r <;> cases h <;> simp [notCreatedSubprogsWithMemOp]


/-- Full original 26-clause conjunction with every shared constructor binder.
Normalized constructor inequalities reduce by disjointness, while the rejected
constructor compares the same normalized node with itself. No source binder,
side condition or callback body is specialized. The source ARB memory operation
is either in a distinct-constructor comparison or the same node on both sides;
no choice representative or extra premise is introduced. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_share_inst_def"
  (words_as_type_indexed_bitvec)]
theorem noShareInstDef {width : Nat} [NeZero width]
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
    (noShareInstSubprogsHOL (.mustTerminate p) = noShareInstSubprogsHOL p) ∧
    (noShareInstSubprogsHOL (.seq p1 p2) = (noShareInstSubprogsHOL p1 && noShareInstSubprogsHOL p2)) ∧
    (noShareInstSubprogsHOL (.loop names c exitNames) = noShareInstSubprogsHOL c) ∧
    (noShareInstSubprogsHOL (.ite v0 v1 v2 p1 p2) = (noShareInstSubprogsHOL p1 && noShareInstSubprogsHOL p2)) ∧
    (noShareInstSubprogsHOL (.call r dest args h) =
      ((match r with | none => true | some (_,_,body,_,_) => noShareInstSubprogsHOL body) &&
       (match h with | none => true | some (_,body,_,_) => noShareInstSubprogsHOL body))) ∧
    noShareInstSubprogsHOL (width := width) (.alloc v3 v4) = true ∧
    noShareInstSubprogsHOL (width := width) (.locValue v5 l) = true ∧
    noShareInstSubprogsHOL (.shareInst v6 v7 v8) = false ∧
    noShareInstSubprogsHOL (width := width) (.install v9 v10 v11 v12 v13) = true ∧
    noShareInstSubprogsHOL (width := width) .skip = true ∧
    noShareInstSubprogsHOL (width := width) (.move v18 v19) = true ∧
    noShareInstSubprogsHOL (.inst v20) = true ∧
    noShareInstSubprogsHOL (.assign v21 v22) = true ∧
    noShareInstSubprogsHOL (width := width) (.get v23 v24) = true ∧
    noShareInstSubprogsHOL (.set v25 v26) = true ∧
    noShareInstSubprogsHOL (.store v27 v28) = true ∧
    noShareInstSubprogsHOL (.storeConsts v46 v47 v48 v49 v50) = true ∧
    noShareInstSubprogsHOL (width := width) (.raise v51) = true ∧
    noShareInstSubprogsHOL (width := width) (.return v52 v53) = true ∧
    noShareInstSubprogsHOL (width := width) (.break v54) = true ∧
    noShareInstSubprogsHOL (width := width) (.continue v55) = true ∧
    noShareInstSubprogsHOL (width := width) .tick = true ∧
    noShareInstSubprogsHOL (width := width) (.opCurrHeap v56 v57 v58) = true ∧
    noShareInstSubprogsHOL (width := width) (.codeBufferWrite v66 v67) = true ∧
    noShareInstSubprogsHOL (width := width) (.dataBufferWrite v68 v69) = true ∧
    noShareInstSubprogsHOL (width := width) (.ffi v70 v71 v72 v73 v74 v75) = true := by
  simp [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp]
  cases r <;> cases h <;> simp [notCreatedSubprogsWithMemOp]


end Flapjack
