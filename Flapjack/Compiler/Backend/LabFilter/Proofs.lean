import Flapjack.Compiler.Backend.LabFilter.Map
import Flapjack.Compiler.Backend.LabFilter.Proofs.CallFfiCases
import Flapjack.Compiler.Backend.LabFilter.Proofs.SharedMemoryCases
import Flapjack.Compiler.Backend.LabFilter.Proofs.BufferTerminalCases
import Flapjack.Compiler.Backend.LabFilter.Proofs.ControlCases
import Flapjack.Compiler.Backend.LabFilter.Proofs.InstructionCases
import Flapjack.Compiler.Backend.LabFilter.Proofs.Simulation
import Flapjack.Compiler.Backend.LabFilter.Proofs.ReturnLabels
import Flapjack.Compiler.Backend.LabFilter.Proofs.LocationLookup
import Flapjack.Compiler.Backend.LabFilter.Proofs.SharedMemory
import Flapjack.Compiler.Backend.LabFilter.Proofs.PcAdjustment
import Flapjack.Compiler.Backend.LabFilter.Proofs.StateRelation
import Flapjack.Compiler.Backend.LabFilter.Proofs.Navigation

/-! Original lab_filterProof prerequisite groups. The full filter simulation
and semantics equality remain open. -/
