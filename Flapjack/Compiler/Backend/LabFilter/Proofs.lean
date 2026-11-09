module

public import Flapjack.Compiler.Backend.LabFilter.Proofs.SectionEnd
public import Flapjack.Compiler.Backend.LabFilter.Proofs.Semantics
public import Flapjack.Compiler.Backend.LabFilter.Proofs.FilterCorrect
public import Flapjack.Compiler.Backend.LabFilter.Proofs.InstallCases
public import Flapjack.Compiler.Backend.LabFilter.Map
public import Flapjack.Compiler.Backend.LabFilter.Proofs.PlainAsmErrorCases
public import Flapjack.Compiler.Backend.LabFilter.Proofs.CallFfiCases
public import Flapjack.Compiler.Backend.LabFilter.Proofs.SharedMemoryCases
public import Flapjack.Compiler.Backend.LabFilter.Proofs.BufferTerminalCases
public import Flapjack.Compiler.Backend.LabFilter.Proofs.ControlCases
public import Flapjack.Compiler.Backend.LabFilter.Proofs.InstructionCases
public import Flapjack.Compiler.Backend.LabFilter.Proofs.Simulation
public import Flapjack.Compiler.Backend.LabFilter.Proofs.ReturnLabels
public import Flapjack.Compiler.Backend.LabFilter.Proofs.LocationLookup
public import Flapjack.Compiler.Backend.LabFilter.Proofs.SharedMemory
public import Flapjack.Compiler.Backend.LabFilter.Proofs.PcAdjustment
public import Flapjack.Compiler.Backend.LabFilter.Proofs.StateRelation
public import Flapjack.Compiler.Backend.LabFilter.Proofs.Navigation

@[expose] public section

/-! Original lab_filterProof prerequisite groups. The full filter simulation
and semantics equality remain open. -/
