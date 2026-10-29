import Tests.SourceConnectionPilot
import ZkcTools.ConstructionBindings.Root
import Zkc.Construction.ConnectionRootRoutes
import Zkc.Construction.ConnectionRouteCoverageRoot

/-! Two linked applications of one actual admitted declaration inside two
symbolic nested repeats. Counts, guards, helper stops and replies remain open.
The root keeps its complete nominal return and physical input ABI. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.ConnectionNestedApplications
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings
abbrev program := Tests.SourceConnectionPilot.program
abbrev artifact := Tests.SourceConnectionPilot.artifact
abbrev context := Tests.SourceConnectionPilot.context
def capabilities := ConnectionRootInputs.serviceCapabilities program.payload.entry.inputs
def routing : Original.Routing :=
  ConnectionRootRoutes.routing program.snapshot context .validator capabilities artifact (by decide +kernel)

noncomputable def library : ConnectionLibrary.Bundle program.payload :=
  by derive_connection_library

def root : RootCertificate program routing 1 artifact := by
  derive_root_connection_with_library
    target Tests.SourceConnectionPilot.rootView
    correspondence Tests.SourceConnectionPilot.body_view
    services capabilities library library

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation
      (Original.CompleteReturns program.payload.entry.signature context 1 artifact)
      (InputFrames root.inputs.abi program.payload.entry.inputs physical)
      (root.source model physical) (Domain.participant model program context artifact physical) :=
  root.simulation model physical

def facts := root.facts
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  facts.coverage model physical
example (model : DomainModel) : root.occurrenceSource model [] = .halt .refused := rfl

#print axioms root
#print axioms facts
end Tests.ConnectionNestedApplications
