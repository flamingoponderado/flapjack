module

public import Flapjack.RiscV.Allocator
public import Flapjack.RiscV.Backend
public import Flapjack.RiscV.RegAlloc
public import Flapjack.RiscV.Calls

@[expose] public section

/-!
Semantic foundations for the SSA and colouring stages of the Word allocator.
The register correspondence is deliberately expressed as an `Option`-valued
equation: it covers both valid RISC-V register names and the evaluator's
failure result for out-of-range virtual names.
-/

namespace Flapjack

open RiscV

theorem wordListRemap_lookup_preserves
    (sources : List Nat) (bijection : WordBijection)
    (source node : Nat)
    (hlookup : lookupNatInfo source bijection.toNode = some node) :
    lookupNatInfo source (wordListRemap sources bijection).toNode = some node := by
  induction sources generalizing bijection with
  | nil =>
      simpa [wordListRemap] using hlookup
  | cons head tail ih =>
      simp only [wordListRemap]
      split <;> rename_i hhead
      · exact ih bijection hlookup
      · by_cases heq : head = source
        · subst head
          simp [hlookup] at hhead
        · apply ih
          simp [lookupNatInfo, heq, hlookup]

theorem wordListRemap_lookup_of_mem
    (sources : List Nat) (bijection : WordBijection)
    (source : Nat) (hsource : source ∈ sources) :
    ∃ node, lookupNatInfo source (wordListRemap sources bijection).toNode = some node := by
  induction sources generalizing bijection with
  | nil =>
      cases hsource
  | cons head tail ih =>
      rcases List.mem_cons.mp hsource with hsource_head | htail
      · simp only [wordListRemap]
        have hsource_eq : source = head := hsource_head
        subst source
        split <;> rename_i hhead
        · exact ⟨_, wordListRemap_lookup_preserves tail bijection head _ hhead⟩
        · have hinsert : lookupNatInfo head
              ((head, bijection.next) :: bijection.toNode) = some bijection.next := by
            simp [lookupNatInfo]
          exact ⟨_, wordListRemap_lookup_preserves tail
            { toNode := (head, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, head) :: bijection.fromNode
              next := bijection.next + 1 } head bijection.next hinsert⟩
      · simp only [wordListRemap]
        split <;> rename_i hhead
        · exact ih bijection htail
        · exact ih
            { toNode := (head, bijection.next) :: bijection.toNode
              fromNode := (bijection.next, head) :: bijection.fromNode
              next := bijection.next + 1 } htail

def wordBijectionWellFormed (bijection : WordBijection) : Prop :=
  (∀ source node,
    lookupNatInfo source bijection.toNode = some node →
      lookupNatInfo node bijection.fromNode = some source) ∧
  (∀ source node,
    lookupNatInfo source bijection.toNode = some node →
      node < bijection.next)

theorem wordListRemap_wellFormed
    (sources : List Nat) (bijection : WordBijection)
    (hform : wordBijectionWellFormed bijection) :
    wordBijectionWellFormed (wordListRemap sources bijection) := by
  induction sources generalizing bijection with
  | nil =>
      simpa [wordListRemap] using hform
  | cons head tail ih =>
      simp only [wordListRemap]
      split <;> rename_i hhead
      · exact ih bijection hform
      · let extended : WordBijection :=
          { toNode := (head, bijection.next) :: bijection.toNode
            fromNode := (bijection.next, head) :: bijection.fromNode
            next := bijection.next + 1 }
        have hformExtended : wordBijectionWellFormed extended := by
          constructor
          · intro source node hlookup
            by_cases hsource : source = head
            · subst source
              have hnode : node = bijection.next := by
                simpa [extended, lookupNatInfo] using hlookup.symm
              subst node
              simp [extended, lookupNatInfo]
            · have hlookupOld : lookupNatInfo source bijection.toNode = some node := by
                by_cases hnode : node = bijection.next
                · subst node
                  have hold : lookupNatInfo source bijection.toNode =
                      some bijection.next := by
                    simpa [extended, lookupNatInfo, hsource, Ne.symm hsource] using hlookup
                  have hbound := hform.2 source bijection.next hold
                  exact False.elim (Nat.lt_irrefl _ hbound)
                · simpa [extended, lookupNatInfo, hsource, Ne.symm hsource,
                    hnode, Ne.symm hnode] using hlookup
              have hnodeBound : node < bijection.next := hform.2 source node hlookupOld
              have hnodeFresh : node ≠ bijection.next := Nat.ne_of_lt hnodeBound
              have hfromOld := hform.1 source node hlookupOld
              simpa [extended, lookupNatInfo, hsource, Ne.symm hsource,
                hnodeFresh, Ne.symm hnodeFresh] using hfromOld
          · intro source node hlookup
            by_cases hsource : source = head
            · subst source
              have hnode : node = bijection.next := by
                simpa [extended, lookupNatInfo] using hlookup.symm
              subst node
              simp [extended]
            · have hlookupOld : lookupNatInfo source bijection.toNode = some node := by
                by_cases hnode : node = bijection.next
                · subst node
                  have hold : lookupNatInfo source bijection.toNode =
                      some bijection.next := by
                    simpa [extended, lookupNatInfo, hsource, Ne.symm hsource] using hlookup
                  have hbound := hform.2 source bijection.next hold
                  exact False.elim (Nat.lt_irrefl _ hbound)
                · simpa [extended, lookupNatInfo, hsource, Ne.symm hsource,
                    hnode, Ne.symm hnode] using hlookup
              have hnodeBound := hform.2 source node hlookupOld
              exact Nat.lt_trans hnodeBound (Nat.lt_succ_self _)
        exact ih extended hformExtended

theorem wordListRemap_lookup_inverse
    (sources : List Nat) (bijection : WordBijection)
    (hform : wordBijectionWellFormed bijection) :
    ∀ source node,
      lookupNatInfo source (wordListRemap sources bijection).toNode = some node →
      lookupNatInfo node (wordListRemap sources bijection).fromNode = some source := by
  have hresult := wordListRemap_wellFormed sources bijection hform
  exact hresult.1

theorem wordMkBijection_wellFormed (tree : WordClashTree) :
    wordBijectionWellFormed (wordMkBijection tree) := by
  have hbase : wordBijectionWellFormed
      ({ toNode := [], fromNode := [], next := 0 } : WordBijection) := by
    constructor <;> simp [lookupNatInfo]
  have go : ∀ (tree : WordClashTree) (bijection : WordBijection),
      wordBijectionWellFormed bijection →
        wordBijectionWellFormed (wordClashTreeBijection tree bijection) := by
    intro tree
    induction tree with
    | delta writes reads =>
        intro bijection hform
        have hreads := wordListRemap_wellFormed reads bijection hform
        simpa [wordClashTreeBijection] using
          wordListRemap_wellFormed writes (wordListRemap reads bijection) hreads
    | set names =>
        intro bijection hform
        simpa [wordClashTreeBijection] using
          wordListRemap_wellFormed names bijection hform
    | branch live thenBranch elseBranch ihThen ihElse =>
        intro bijection hform
        have hthen := ihThen bijection hform
        have helse := ihElse (wordClashTreeBijection thenBranch bijection) hthen
        cases live with
        | none => simpa [wordClashTreeBijection] using helse
        | some names =>
            simpa [wordClashTreeBijection] using
              wordListRemap_wellFormed names
                (wordClashTreeBijection elseBranch
                  (wordClashTreeBijection thenBranch bijection)) helse
    | seq first second ihFirst ihSecond =>
        intro bijection hform
        have hsecond := ihSecond bijection hform
        simpa [wordClashTreeBijection] using
          ihFirst (wordClashTreeBijection second bijection) hsecond
  exact go tree { toNode := [], fromNode := [], next := 0 } hbase

theorem wordMkBijection_lookup_inverse (tree : WordClashTree) :
    ∀ source node,
      lookupNatInfo source (wordMkBijection tree).toNode = some node →
      lookupNatInfo node (wordMkBijection tree).fromNode = some source := by
  exact (wordMkBijection_wellFormed tree).1

end Flapjack
