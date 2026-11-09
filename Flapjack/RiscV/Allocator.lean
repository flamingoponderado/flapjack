module

public import Flapjack.Compiler.Backend.WordAlloc.SSAStateRoute
public import Flapjack.Compiler.Backend.WordAlloc.MergeMovesRoute
public import Flapjack.Compiler.Backend.WordAlloc.Instructions
public import Flapjack.Word
public import Flapjack.Compiler.Backend.WordAlloc.Expressions
public import Flapjack.NumSet
public import Std.Data.HashMap

@[expose] public section

/-!
The first explicit register-allocation boundary for the Word backend.

CakeML's full `word_alloc` pass uses SSA renaming, clash colouring, and
spill-aware allocation.  Flapjack currently represents Word variables by
natural-number register names directly, so this module ports the part of the
target contract that must hold before that larger pass is introduced:

* x0 is the architectural zero register;
* x1 is the call link register;
* x27 is the third AddCarry scratch register used by spill lowering;
* x29 is the address scratch register used by stack lowering;
* x30 is the stack pointer used by ordinary calls; and
* x31 is the backend scratch register.

The allocator preserves the historical `name + 2` assignment whenever it is
safe.  Out-of-range names are assigned the first free register that is not a
preferred register of another slot.  x27 and x28 are reserved as temporaries
used by spill-aware `AddCarry` and `LongMul` lowering.  Exhaustion is reported as `none`; it
is never converted into an aliased or reserved register.
-/

namespace Flapjack

def wordPreferredRegister (name : Nat) : Option Nat :=
  let register := name + 2
  if register < 27 then some register else none

def wordRegisterIsReserved (register : Nat) : Bool :=
  register == 0 || register == 1 || register == 27 || register == 28 ||
    register == 29 || register == 30 || register == 31

def wordRegisterIsAllocatable (register : Nat) : Bool :=
  register ≥ 2 && register < 27

/-! A compact executable clash-colouring interface.  CakeML builds a clash
tree from the SSA program and then colours its graph.  The current Word IR
does not yet carry the full spill metadata, but this layer already consumes
the resulting undirected clash edges instead of ignoring them. -/

def wordNeighbours (name : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (left, right) :: edges =>
      if left == name then right :: wordNeighbours name edges
      else if right == name then left :: wordNeighbours name edges
      else wordNeighbours name edges

def wordFirstAvailable : List Nat → List Nat → Option Nat
  | [], _ => none
  | register :: registers, forbidden =>
      if register ∈ forbidden then
        wordFirstAvailable registers forbidden
      else some register

/-! RISC-V has additional forced clashes for multi-result arithmetic.  The
    high half of `LongMul` is written before the low half, so its first
    destination must not reuse either source.  The carry sequence similarly
    reads both addends after writing the sum destination; the two result
    destinations must also remain distinct.  These edges are part of the
    allocator contract, rather than an instruction-selection afterthought. -/

def wordClashPairs (writes live : List Nat) : List (Nat × Nat) :=
  writes.flatMap (fun write =>
    (live.filter (fun name => name != write)).map (fun name => (write, name)))

/-! The allocator's production clash path consumes these pairs in the same
    left-to-right order as `wordClashPairs`.  Threading the suffix through
    both traversals avoids constructing the filtered and mapped lists while
    retaining the proof-facing definition above unchanged. -/
def wordClashPairsFastAcc (writes live : List Nat)
    (tail : List (Nat × Nat)) : List (Nat × Nat) :=
  writes.foldr
    (fun write rest =>
      live.foldr
        (fun name restLive =>
          if name != write then (write, name) :: restLive else restLive)
        rest)
    tail

def wordClashPairsFast (writes live : List Nat) : List (Nat × Nat) :=
  wordClashPairsFastAcc writes live []

/-! A production-only difference-list inventory.  The reference definitions
    above remain the proof-facing equations; this helper has the same
    left-to-right Cake traversal but threads the tail so large allocator
    programs do not repeatedly copy prefixes with `++`. -/
def wordListAppendAcc : List Nat → List Nat → List Nat
  | [], tail => tail
  | name :: names, tail => name :: wordListAppendAcc names tail

/-! CakeML's `full_ssa_cc_trans` is parameterised by the number of ABI
    arguments rather than by their source names.  Word functions use the even
    register names as their incoming ABI names, so expose that exact adapter
    here while retaining the named-parameter entry point above for callers
    that already have the ABI list. -/

/- Cake's call boundary scans the same syntax in left-to-right order as
   `wordProgReadVars`, but this private accumulator form avoids rebuilding the
   prefix list at every nested call.  Keep the public equation above unchanged
   for the proof-facing allocator interface. -/

def wordListUnion (left right : List Nat) : List Nat :=
  (left ++ right).eraseDups

/-! A CakeML-shaped clash-tree boundary for the RISC-V Word fragment.

    CakeML's `word_alloc` does not allocate from a flat list of pairwise
    clashes.  It first builds a tree whose `Delta` nodes describe writes and
    reads, whose `Branch` nodes preserve path-local live sets, and whose `Set`
    nodes model loop cut sets and call boundaries.  The earlier analysis above
    remains useful as a compact executable allocator input; this tree is the
    faithful structural interface that later colouring and spill proofs can
    consume.  The constructors absent from this RISC-V Word IR are naturally
    absent here as well. -/

inductive WordClashTree where
  | delta (writes reads : List Nat)
  | seq (first second : WordClashTree)
  | branch (live : Option (List Nat))
      (thenBranch elseBranch : WordClashTree)
  | set (names : List Nat)
  deriving Repr

/-! Backward interpretation of a clash tree.  `Delta` contributes clashes
    between its writes and the values live after it; `Seq` feeds the live set
    produced by its suffix into its prefix; and `Branch` joins the live sets
    computed for both paths.  `Set` is a cut-set boundary supplied by the
    source allocator. -/

def wordNumSetDelete : List Nat → List Nat → List Nat
  | [], live => live
  | name :: names, live =>
      wordNumSetDelete names (live.filter (fun other => other != name))

def wordCheckPartialColour (colour : Nat → Nat) : List Nat → List Nat →
    List Nat → Option (List Nat × List Nat)
  | [], live, flive => some (live, flive)
  | name :: names, live, flive =>
      if name ∈ live then
        wordCheckPartialColour colour names live flive
      else if colour name ∈ flive then
        none
      else
        wordCheckPartialColour colour names (name :: live)
          (colour name :: flive)

def wordCheckColour (colour : Nat → Nat) (names : List Nat) :
    Option (List Nat × List Nat) :=
  let coloured := names.map colour
  if coloured.Nodup then some (names, coloured) else none

def wordClashTreeCheck (colour : Nat → Nat) : WordClashTree →
    List Nat → List Nat → Option (List Nat × List Nat)
  | .delta writes reads, live, flive =>
      match wordCheckPartialColour colour writes live flive with
      | none => none
      | some _ =>
          wordCheckPartialColour colour reads
            (wordNumSetDelete writes live)
            (wordNumSetDelete (writes.map colour) flive)
  | .set names, _, _ => wordCheckColour colour names.eraseDups
  | .branch branchLive thenBranch elseBranch, live, flive =>
      match wordClashTreeCheck colour thenBranch live flive with
      | none => none
      | some (thenOut, fThenOut) =>
          match wordClashTreeCheck colour elseBranch live flive with
          | none => none
          | some (elseOut, _fElseOut) =>
              match branchLive with
              | none =>
                  wordCheckPartialColour colour
                    (elseOut.filter (fun name => name ∉ thenOut))
                    thenOut fThenOut
              | some names => wordCheckColour colour names.eraseDups
  | .seq first second, live, flive =>
      match wordClashTreeCheck colour second live flive with
      | none => none
      | some (secondOut, fSecondOut) =>
          wordClashTreeCheck colour first secondOut fSecondOut
termination_by tree => sizeOf tree
decreasing_by all_goals decreasing_trivial

theorem wordCheckPartialColour_sound (colour : Nat → Nat)
    (names live flive live' flive' : List Nat)
    (hlive : live.Nodup)
    (hflive : flive.Nodup)
    (himage : flive = live.map colour)
    (hcheck : wordCheckPartialColour colour names live flive =
      some (live', flive')) :
    live'.Nodup ∧ flive'.Nodup ∧ flive' = live'.map colour := by
  induction names generalizing live flive live' flive' with
  | nil =>
      simp [wordCheckPartialColour] at hcheck
      rcases hcheck with ⟨rfl, rfl⟩
      exact ⟨hlive, hflive, himage⟩
  | cons name names ih =>
      by_cases hname : name ∈ live
      · have hcheck' : wordCheckPartialColour colour names live flive =
            some (live', flive') := by
          simpa [wordCheckPartialColour, hname] using hcheck
        exact ih live flive live' flive' hlive hflive himage hcheck'
      · by_cases hcolour : colour name ∈ flive
        · simp [wordCheckPartialColour, hname, hcolour] at hcheck
        · have hcheck' :
              wordCheckPartialColour colour names (name :: live)
                (colour name :: flive) = some (live', flive') := by
            simpa [wordCheckPartialColour, hname, hcolour] using hcheck
          have hlive' : (name :: live).Nodup := by
            simp [List.nodup_cons, hname, hlive]
          have hflive' : (colour name :: flive).Nodup := by
            simp [List.nodup_cons, hcolour, hflive]
          have himage' : colour name :: flive = (name :: live).map colour := by
            simp [himage]
          exact ih (name :: live) (colour name :: flive) live' flive'
            hlive' hflive' himage' hcheck'

theorem wordCheckColour_sound (colour : Nat → Nat)
    (names names' coloured' : List Nat)
    (hcheck : wordCheckColour colour names = some (names', coloured')) :
    names' = names ∧ coloured' = names.map colour ∧
      coloured'.Nodup := by
  simp [wordCheckColour] at hcheck
  rcases hcheck with ⟨hcoloured, hnames, hmap⟩
  exact ⟨hnames.symm, hmap.symm, by simpa [hmap] using hcoloured⟩

theorem wordMapFilterDelete (colour : Nat → Nat) (name : Nat)
    (live : List Nat) (hinjective : Function.Injective colour) :
    (live.filter (fun other => other != name)).map colour =
      (live.map colour).filter (fun other => other != colour name) := by
  induction live with
  | nil => simp
  | cons head tail ih =>
      by_cases hhead : head = name
      · subst head
        simpa using ih
      · have hcolour : colour head ≠ colour name := by
          intro heq
          apply hhead
          exact hinjective heq
        simp [hhead, hcolour, ih]

theorem wordNumSetDelete_map (colour : Nat → Nat)
    (names live : List Nat) (hinjective : Function.Injective colour) :
    wordNumSetDelete (names.map colour) (live.map colour) =
      (wordNumSetDelete names live).map colour := by
  induction names generalizing live with
  | nil => rfl
  | cons name names ih =>
      simp only [List.map_cons, wordNumSetDelete]
      rw [← wordMapFilterDelete colour name live hinjective]
      rw [ih]

theorem wordNumSetDelete_nodup (names live : List Nat)
    (hlive : live.Nodup) :
    (wordNumSetDelete names live).Nodup := by
  induction names generalizing live with
  | nil => exact hlive
  | cons name names ih =>
      apply ih
      exact hlive.filter (fun other => other != name)

theorem wordMap_nodup_source (colour : Nat → Nat)
    (names : List Nat) (hcoloured : (names.map colour).Nodup) :
    names.Nodup := by
  induction names with
  | nil => simp
  | cons name names ih =>
      have hcoloured' := List.nodup_cons.mp hcoloured
      apply List.nodup_cons.mpr
      constructor
      · intro hname
        apply hcoloured'.1
        exact List.mem_map.mpr ⟨name, hname, rfl⟩
      · exact ih hcoloured'.2

theorem wordClashTreeCheck_sound (colour : Nat → Nat)
    (tree : WordClashTree) (live flive live' flive' : List Nat)
    (hinjective : Function.Injective colour)
    (hlive : live.Nodup)
    (hflive : flive.Nodup)
    (himage : flive = live.map colour)
    (hcheck : wordClashTreeCheck colour tree live flive =
      some (live', flive')) :
    live'.Nodup ∧ flive'.Nodup ∧ flive' = live'.map colour := by
  induction tree generalizing live flive live' flive' with
  | delta writes reads =>
      simp only [wordClashTreeCheck] at hcheck
      split at hcheck
      · contradiction
      · rename_i hpartial
        have hdeletedLive :
            (wordNumSetDelete writes live).Nodup :=
          wordNumSetDelete_nodup writes live hlive
        have hdeletedFlive :
            (wordNumSetDelete (writes.map colour) flive).Nodup := by
          rw [himage]
          exact wordNumSetDelete_nodup (writes.map colour)
            (live.map colour) (by simpa [himage] using hflive)
        have hdeletedImage :
            wordNumSetDelete (writes.map colour) flive =
              (wordNumSetDelete writes live).map colour := by
          simpa [himage] using
            (wordNumSetDelete_map colour writes live hinjective)
        have hreads :
            wordCheckPartialColour colour reads
              (wordNumSetDelete writes live)
              (wordNumSetDelete (writes.map colour) flive) =
              some (live', flive') := by
            simpa [hpartial] using hcheck
        exact wordCheckPartialColour_sound colour reads
          (wordNumSetDelete writes live)
          (wordNumSetDelete (writes.map colour) flive)
          live' flive' hdeletedLive hdeletedFlive hdeletedImage hreads
  | set names =>
      have hcheck' : wordCheckColour colour names.eraseDups =
          some (live', flive') := by
        simpa [wordClashTreeCheck] using hcheck
      have hcolour := wordCheckColour_sound colour names.eraseDups live' flive' hcheck'
      rcases hcolour with ⟨hnames, hmap, hcoloured⟩
      subst live'
      subst flive'
      exact ⟨wordMap_nodup_source colour names.eraseDups hcoloured, hcoloured, rfl⟩
  | branch branchLive thenBranch elseBranch ihThen ihElse =>
      cases hthen : wordClashTreeCheck colour thenBranch live flive with
      | none =>
          simp [wordClashTreeCheck, hthen] at hcheck
      | some thenResult =>
          cases helse : wordClashTreeCheck colour elseBranch live flive with
          | none =>
              simp [wordClashTreeCheck, hthen, helse] at hcheck
          | some elseResult =>
              cases thenResult with
              | mk thenOut fThenOut =>
                  cases elseResult with
                  | mk elseOut fElseOut =>
                      have hthen' :
                          thenOut.Nodup ∧ fThenOut.Nodup ∧
                            fThenOut = thenOut.map colour :=
                        ihThen live flive thenOut fThenOut
                          hlive hflive himage hthen
                      have helse' :
                          elseOut.Nodup ∧ fElseOut.Nodup ∧
                            fElseOut = elseOut.map colour :=
                        ihElse live flive elseOut fElseOut
                          hlive hflive himage helse
                      cases branchLive with
                      | none =>
                          have hfinal :
                              wordCheckPartialColour colour
                                (elseOut.filter
                                  (fun name => name ∉ thenOut))
                                thenOut fThenOut =
                                some (live', flive') := by
                            simpa only [wordClashTreeCheck, hthen, helse] using
                              hcheck
                          exact wordCheckPartialColour_sound colour
                            (elseOut.filter
                              (fun name => name ∉ thenOut))
                            thenOut fThenOut live' flive'
                            hthen'.1 hthen'.2.1 hthen'.2.2 hfinal
                      | some names =>
                          have hfinal : wordCheckColour colour names.eraseDups =
                              some (live', flive') := by
                            simpa only [wordClashTreeCheck, hthen, helse] using
                              hcheck
                          have hcolour := wordCheckColour_sound colour
                            names.eraseDups live' flive' hfinal
                          rcases hcolour with ⟨hnames, hmap, hcoloured⟩
                          subst live'
                          subst flive'
                          exact ⟨wordMap_nodup_source colour names.eraseDups hcoloured,
                            hcoloured, rfl⟩
  | seq first second ihFirst ihSecond =>
      cases hsecond : wordClashTreeCheck colour second live flive with
      | none =>
          simp [wordClashTreeCheck, hsecond] at hcheck
      | some secondResult =>
          cases secondResult with
          | mk secondOut fSecondOut =>
              have hsecond' :
                  secondOut.Nodup ∧ fSecondOut.Nodup ∧
                    fSecondOut = secondOut.map colour :=
                ihSecond live flive secondOut fSecondOut
                  hlive hflive himage hsecond
              have hfirst : wordClashTreeCheck colour first
                  secondOut fSecondOut = some (live', flive') := by
                simpa [wordClashTreeCheck, hsecond] using hcheck
              exact ihFirst secondOut fSecondOut live' flive'
                hsecond'.1 hsecond'.2.1 hsecond'.2.2 hfirst

/-! Follow preference edges through not-yet-coloured variables.  CakeML's
    allocator can coalesce a whole move chain with a fixed ABI source, even
    when the source variable is encountered after an intermediate copy in the
    work list.  A direct-only lookup misses that transitive opportunity and
    creates avoidable copies at returns (notably for a wide constant). -/
def wordPreferenceNeighbours (name : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (left, right) :: preferences =>
      if left == name then right :: wordPreferenceNeighbours name preferences
      else if right == name then left :: wordPreferenceNeighbours name preferences
      else wordPreferenceNeighbours name preferences

/-! The preference graph is static during one allocation, but the previous
    reachability query rescanned every preference edge at every graph node for
    every candidate.  The full guest's `main'` has 596 preference edges and
    11,538 candidate slots, making that otherwise faithful traversal dominate
    allocation.  Build an indexed undirected adjacency table once and retain
    the same depth-first neighbour order and location barrier semantics. -/

def wordPreferenceIndexAdd (index : Std.HashMap Nat (List Nat))
    (left right : Nat) : Std.HashMap Nat (List Nat) :=
  let add := fun index source target =>
    index.insert source ((index.get? source).getD [] ++ [target])
  let index := add index left right
  if left = right then index else add index right left

def wordPreferenceIndex : List (Nat × Nat) → Std.HashMap Nat (List Nat)
  | preferences =>
      preferences.foldl (fun index edge => wordPreferenceIndexAdd index edge.1 edge.2) ∅

/-! The clash graph is static for one SSA function as well.  Keep a separate
    index name so the oracle list scan remains available for equivalence tests;
    appending in edge order preserves `wordNeighbours`' exact traversal order. -/
def wordClashIndexAdd (index : Std.HashMap Nat (List Nat))
    (left right : Nat) : Std.HashMap Nat (List Nat) :=
  let add := fun index source target =>
    index.insert source ((index.get? source).getD [] ++ [target])
  let index := add index left right
  if left = right then index else add index right left

def wordClashIndex : List (Nat × Nat) → Std.HashMap Nat (List Nat)
  | edges =>
      edges.foldl (fun index edge => wordClashIndexAdd index edge.1 edge.2) ∅

def wordClashNeighboursIndexed (index : Std.HashMap Nat (List Nat))
    (name : Nat) : List Nat :=
  (index.get? name).getD []

def wordPreferenceNeighboursIndexed (index : Std.HashMap Nat (List Nat))
    (name : Nat) : List Nat :=
  (index.get? name).getD []

/-! Spill allocation over the complete CakeML-shaped SSA function.  In
    contrast with the historical entry point above, the explicit formal
    parameter moves are present in the clash tree, preferences, and returned
    program. -/

theorem wordPreferredRegister_safe (name register : Nat)
    (hregister : wordPreferredRegister name = some register) :
    wordRegisterIsAllocatable register = true := by
  simp [wordPreferredRegister] at hregister
  rcases hregister with ⟨hbound, rfl⟩
  simp [wordRegisterIsAllocatable]
  omega

end Flapjack
