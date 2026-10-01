import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Compiler.Backend.RegAlloc.SortedInsert
import Flapjack.Compiler.Backend.RegAlloc.SpDefault
import Flapjack.Compiler.Backend.RegAlloc.StateForeach

/-!
# reg_alloc interference-graph construction

Literal ports of `reg_allocScript.sml:201-245` (edge insertion into the
adjacency lists) and `1159-1250` (`mk_tags`, `mk_graph`, `extend_graph`,
`init_ra_state`) over the reviewed `ra_state` carrier and its generated
accessors. HOL do-blocks are the accepted MonadBase `bind`/`ignoreBind`/`ret`,
including the literal `x <- return e` binders as `bind (ret e)`; HOL `let` is
`let`; `GENLIST (\x.x) n` is `List.range n`; MEM and FILTER use `decide`. These are proof-side ports: the executed allocator builds
its graph through `CakeRegAlloc` and is not routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal `insert_edge` (`reg_allocScript.sml:201-212`): read both
adjacency lists, then write `y` into `x`'s and `x` into `y`'s. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "insert_edge_def"]
def insertEdge (x y : Nat) : M State Unit StateException :=
  bind (adjLsSub x) fun adjx =>
    bind (adjLsSub y) fun adjy =>
      ignoreBind (updateAdjLs x (sortedInsert y [] adjx))
        (updateAdjLs y (sortedInsert x [] adjy))

/-- Literal `list_insert_edge` (`reg_allocScript.sml:214-221`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "list_insert_edge_def"]
def listInsertEdge (x : Nat) : List Nat → M State Unit StateException
  | [] => ret ()
  | y :: ys => ignoreBind (insertEdge x y) (listInsertEdge x ys)

/-- Literal `clique_insert_edge` (`reg_allocScript.sml:223-229`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "clique_insert_edge_def"]
def cliqueInsertEdge : List Nat → M State Unit StateException
  | [] => ret ()
  | x :: xs => ignoreBind (listInsertEdge x xs) (cliqueInsertEdge xs)

/-- Literal `extend_clique` (`reg_allocScript.sml:235-245`): members already
in the clique are skipped; a new member is joined to every current member. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "extend_clique_def"]
def extendClique : List Nat → List Nat → M State (List Nat) StateException
  | [], cli => ret cli
  | x :: xs, cli =>
    if x ∈ cli then extendClique xs cli
    else ignoreBind (listInsertEdge x cli) (extendClique xs (x :: cli))

/-- Literal `mk_tags` (`reg_allocScript.sml:1159-1176`): tag node `i` from the
wordLang variable `fa i` by its residue mod 4. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "mk_tags_def"]
def mkTags (n : Nat) (fs : NumSet) (fa : Nat → Nat) : M State Unit StateException :=
  bind (ret (List.range n)) fun inds =>
  stExForeach inds fun i =>
    let v := fa i
    let remainder := v % 4
    if remainder = 1 then
      match sptLookup v fs with
      | none => updateNodeTag i .Atemp
      | some () => updateNodeTag i .Stemp
    else if remainder = 3 then updateNodeTag i .Stemp
    else updateNodeTag i (.Fixed (v / 2))

/-- Literal `mk_graph` (`reg_allocScript.sml:1179-1217`), by recursion on the
clash tree. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "mk_graph_def"]
def mkGraph (ta : Nat → Nat) : ClashTree → List Nat → M State (List Nat) StateException
  | .delta w r, liveout =>
    bind (ret (w.map ta)) fun wta =>
    bind (ret (r.map ta)) fun rta =>
    bind (extendClique wta liveout) fun live =>
    bind (ret (live.filter (fun x => decide (x ∉ wta)))) fun live =>
    bind (extendClique rta live) fun livein => ret livein
  | .set t, _ =>
    bind (ret (((sptToAList t).map Prod.fst).map ta)) fun live =>
    ignoreBind (cliqueInsertEdge live) (ret live)
  | .branch topt t1 t2, liveout =>
    bind (mkGraph ta t1 liveout) fun t1Live =>
      bind (mkGraph ta t2 liveout) fun t2Live =>
        match topt with
        | none => bind (extendClique t1Live t2Live) fun livein => ret livein
        | some t =>
          bind (ret (((sptToAList t).map Prod.fst).map ta)) fun clashes =>
          ignoreBind (cliqueInsertEdge clashes) (ret clashes)
  | .seq t1 t2, liveout =>
    bind (mkGraph ta t2 liveout) fun live => mkGraph ta t1 live

/-- Literal `extend_graph` (`reg_allocScript.sml:1224-1230`); the forced-edge
endpoints have an arbitrary carrier, as in HOL (`(α -> num) -> (α # α) list -> ...`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "extend_graph_def"]
def extendGraph {α : Type} (ta : α → Nat) : List (α × α) → M State Unit StateException
  | [] => ret ()
  | (x, y) :: xs => ignoreBind (insertEdge (ta x) (ta y)) (extendGraph ta xs)

/-- Literal `init_ra_state` (`reg_allocScript.sml:1241-1248`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "init_ra_state_def"]
def initRaState (ct : ClashTree) (forced : List (Nat × Nat)) (fs : NumSet) :
    Spt Nat × Spt Nat × Nat → M State Unit StateException
  | (ta, fa, n) =>
    ignoreBind (mkGraph (spDefault ta) ct [])
      (ignoreBind (extendGraph (spDefault ta) forced) (mkTags n fs (spDefault fa)))

end Flapjack.RegAlloc
