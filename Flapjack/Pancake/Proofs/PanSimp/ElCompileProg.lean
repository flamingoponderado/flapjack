module

public import Flapjack.Pancake.Proofs.PanSimp
public import Flapjack.Misc.ListEl
public import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

@[expose] public section

/-! `pan_simpProofScript.sml:1047-1057`: the `EL` entry of the compiled program
is the source entry, given name distinctness, the index bound and the `ALOOKUP`
value.  HOL's `EL` is rendered by the reviewed total `holEl`, never by an
`Option` projection, so the statement keeps both index observations total.

The `Nonempty` instances `holEl` needs are discharged from the concrete
carriers' constructors in this module, so no binder is added and no
`total_function_inhabitants` qualifier applies. -/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

local instance : Nonempty MlString := ⟨ofString ""⟩

local instance : Nonempty ShapeHOL := ⟨ShapeHOL.one⟩

local instance {width : Nat} [NeZero width] : Nonempty (ProgHOL width) :=
  ⟨ProgHOL.skip⟩

/-- `holEl` through a list map, at an in-range index (Flapjack list
infrastructure for the `EL` rendering below). -/
private theorem holEl_map {α β : Type} [Nonempty α] [Nonempty β]
    (f : α → β) (n : Nat) (entries : List α) (hn : n < entries.length) :
    holEl n (entries.map f) = f (holEl n entries) := by
  rw [holEl_eq_getElem n (entries.map f) (by simpa using hn)]
  rw [holEl_eq_getElem n entries hn]
  simp only [List.getElem_map]

/-- Exact port of HOL `pan_simpProof$el_compile_prog_el_prog_eq`
(`pan_simpProofScript.sml:1047-1057`). The typed capture
`el_compile_prog_el_prog_eq_pan_simp_typed`
(`pancake_pan_simp_proof_typed_probe.out`) gives
`∀prog n start pprog p rshape.
  EL n (functions (compile_prog prog)) = (start,[],pprog,rshape) ∧
  ALL_DISTINCT (MAP FST (functions prog)) ∧ n < LENGTH (functions prog) ∧
  ALOOKUP (functions prog) start = SOME ([],p,rshape) ⇒
  EL n (functions prog) = (start,[],p,rshape)`,
with the four conjuncts kept as ONE hypothesis and the binder order
`prog n start pprog p rshape`. Both `EL` occurrences are the reviewed total
`holEl`; `functions` is `functionsHOL`, `compile_prog` is `panSimpDeclsHOL`
(which maps `functionsHOL` entries, so the indexed entry is the mapped entry),
`ALL_DISTINCT` is `List.Nodup`, `LENGTH` is `.length` and `ALOOKUP` is
`holAlookup`. Name uniqueness plus the `ALOOKUP` value pins the entry. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "el_compile_prog_el_prog_eq"
  (words_as_type_indexed_bitvec)]
theorem elCompileProgElProgEqPanSimpHOL {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) (n : Nat) (start : MlS) (pprog : ProgHOL width)
    (p : ProgHOL width) (rshape : ShapeHOL)
    (h : holEl n (Flapjack.Pancake.PanLang.functionsHOL (panSimpDeclsHOL prog)) =
        (start, [], pprog, rshape) ∧
      ((Flapjack.Pancake.PanLang.functionsHOL prog).map Prod.fst).Nodup ∧
      n < (Flapjack.Pancake.PanLang.functionsHOL prog).length ∧
      holAlookup (Flapjack.Pancake.PanLang.functionsHOL prog) start =
        some ([], p, rshape)) :
    holEl n (Flapjack.Pancake.PanLang.functionsHOL prog) = (start, [], p, rshape) := by
  obtain ⟨hel, hdistinct, hn, hlookup⟩ := h
  have hexpand : Flapjack.Pancake.PanLang.functionsHOL (panSimpDeclsHOL prog) =
      (Flapjack.Pancake.PanLang.functionsHOL prog).map
        (fun entry => (entry.1, entry.2.1, panSimpCompileHOL entry.2.2.1,
          entry.2.2.2)) :=
    functionsHOL_panSimpDeclsHOL_eq prog
  have hprem : (fun entry => (entry.1, entry.2.1, panSimpCompileHOL entry.2.2.1,
      entry.2.2.2))
      (holEl n (Flapjack.Pancake.PanLang.functionsHOL prog)) =
        (start, [], pprog, rshape) := by
    rw [hexpand] at hel
    rw [holEl_map
      (f := fun entry => (entry.1, entry.2.1, panSimpCompileHOL entry.2.2.1,
        entry.2.2.2)) n
      (Flapjack.Pancake.PanLang.functionsHOL prog) hn] at hel
    exact hel
  have hmem : holEl n (Flapjack.Pancake.PanLang.functionsHOL prog) ∈
      Flapjack.Pancake.PanLang.functionsHOL prog := by
    rw [holEl_eq_getElem n (Flapjack.Pancake.PanLang.functionsHOL prog) hn]
    exact List.getElem_mem hn
  have hname : (holEl n (Flapjack.Pancake.PanLang.functionsHOL prog)).1 = start :=
    congrArg Prod.fst hprem
  have hvalue := holAlookup_snd_eq_of_mem_name
    (Flapjack.Pancake.PanLang.functionsHOL prog) start ([], p, rshape)
    (holEl n (Flapjack.Pancake.PanLang.functionsHOL prog)) hlookup hdistinct hmem hname
  exact Prod.ext hname hvalue

end Flapjack
