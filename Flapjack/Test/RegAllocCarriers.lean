import Flapjack.Compiler.Backend.RegAlloc.Carriers

namespace Flapjack.RegAlloc

-- Kernel fixtures distinguish all constructors and exercise all twelve fields.
example : Tag.Fixed 100000000000000000000 ≠ Tag.Atemp := by decide
example : Tag.Atemp ≠ Tag.Stemp := by decide
example : Algorithm.Simple ≠ Algorithm.IRC := by decide

private def specimen : State :=
  ⟨[[1, 2], [0], []], [.Fixed 7, .Atemp, .Stemp], [2, 1, 0], 3,
    [1], [2], [0], [(11, (1, 2))], [(13, (2, 0))], [0, 1, 2],
    [true, false, true], [2, 1, 0]⟩

example : (specimen.adj_ls, specimen.node_tag, specimen.degrees, specimen.dim,
    specimen.simp_wl, specimen.spill_wl, specimen.freeze_wl,
    specimen.avail_moves_wl, specimen.unavail_moves_wl, specimen.coalesced,
    specimen.move_related, specimen.stack) =
    ([[1, 2], [0], []], [.Fixed 7, .Atemp, .Stemp], [2, 1, 0], 3,
    [1], [2], [0], [(11, (1, 2))], [(13, (2, 0))], [0, 1, 2],
    [true, false, true], [2, 1, 0]) := rfl

example : ({ specimen with stack := [] }).adj_ls = specimen.adj_ls := rfl
example : ({ specimen with move_related := [false] }).move_related = [false] := rfl

end Flapjack.RegAlloc
