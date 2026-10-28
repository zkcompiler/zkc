import Zkc.Construction.ConnectionApplicationCertificate
import ZkcTools.ConstructionBindings.Alignment
import ZkcTools.ConstructionBindings.Root
import Tests.SourceConnectionPilot
import Tests.ConnectionSymbolicRepeat

/-! One finite source body, two call placements, arbitrary enclosing repeat
coordinates, and a stopping owned helper. These are linked applications of the
admitted source declaration, not handwritten source process presentations.
The two placements are not yet composed into a root certificate. -/
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.ConnectionSharedLibrary
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary

abbrev program := Tests.SourceConnectionPilot.program

def pattern : InputPattern Tests.SourceConnectionPilot.stepInputs :=
  .cons .present (.cons .present (.cons .present .nil))
def template : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 1 pattern).toOption.get (by decide +kernel)
def library : Library program.payload [template.key] := .extend .empty template

example : template.source = Tests.SourceConnectionPilot.stepDefinition := rfl
example : template.key.signature = Tests.SourceConnectionPilot.stepSignature := rfl
example (model : DomainModel) {types : List Ty}
    (inputs : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model program.payload) (library.processes model) inputs :=
  library.holds model inputs

abbrev scope : Scope := [.value .boolean, .value .boolean, .value .index, .value .index, .value .index]
def arguments : Values (Argument [] scope) pattern.scope :=
  .cons (.var .here) (.cons (.var (.there .here)) (.cons (.var (.there (.there .here))) .nil))
def layout : Layout scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here))),
    .data (.present (.var (.there (.there .here)))),
    .data (.present (.var (.there (.there (.there .here))))),
    .data (.present (.var (.there (.there (.there (.there .here))))))]
def frames : ScopedFrames scope :=
  [⟨"outer", .var (.there (.there (.there .here)))⟩,
   ⟨"inner", .var (.there (.there (.there (.there .here))))⟩]
def context (site : String) : ProtocolContext := ({} : ProtocolContext).enter site [0,1]
def target (site : String) : ConnectionCertificate.Block := fun model =>
  Tests.SourceConnectionPilot.stepView model site 0 1 2 Domain.View.empty

def PlacementRoute (site : String) : Prop :=
  OccurrenceResolution.resolveStatic Tests.SourceConnectionPilot.routing.snapshot
    Tests.SourceConnectionPilot.routing.context
    (Tests.SourceConnectionPilot.routing.context.message
      (qualifyProtocolSite (context site).applicationPrefix "message")
      ((context site).roles 0) Tests.SourceConnectionPilot.routing.self)
    frames.sites Tests.SourceConnectionPilot.routing.messages =
      some (Tests.SourceConnectionPilot.messageTemplate site)

/-- One parametric alignment is checked once. Each placement supplies only its
finite route check; the guard/helper/receive derivation is retained by reference. -/
def sharedPlacement (site : String) (route : PlacementRoute site) :
    ConnectionApplications.Certificate template Tests.SourceConnectionPilot.routing (context site) arguments
      [.data 6] none frames layout (target site) where
  distinct := RosterDistinct.ofSeparate (by change 0 ≠ 1; decide) (by change 1 < 2; decide)
  alignment := by derive_connection_alignment

def first : ConnectionApplications.Certificate template Tests.SourceConnectionPilot.routing (context "first") arguments
    [.data 6] none frames layout (target "first") := sharedPlacement "first" (by unfold PlacementRoute; decide +kernel)

def second : ConnectionApplications.Certificate template Tests.SourceConnectionPilot.routing (context "second") arguments
    [.data 6] none frames layout (target "second") := sharedPlacement "second" (by unfold PlacementRoute; decide +kernel)

def producerTemplate : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 0 pattern).toOption.get (by decide +kernel)
def producerRouting : Original.Routing := { Tests.SourceConnectionPilot.routing with mode := .producer }
def producerTarget : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.send (qualifyProtocolSite (some "first") "message")
    (qualifyProtocolSite (some "first") "message") "V" 2 []) Domain.View.empty
def producer : ConnectionApplications.Certificate producerTemplate producerRouting (context "first") arguments
    [.data 2] none frames layout producerTarget where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment

def fsContext : Context := .fiatShamir "main" ["P", "V"] 0 1 0 "random.bls12-381.fr/0"
  (some (.draw "bls12-381.fr")) "suite" []
def fsRouting : Original.Routing := { Tests.SourceConnectionPilot.routing with context := fsContext }
def fsLayout : Layout scope := layout ++ [.history "suite"]
def fsTarget (reversed : Bool := false) : ConnectionCertificate.Block := fun model =>
  Tests.SourceConnectionPilot.stepView model "first" 0 1 2 <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 8 (if reversed then 4 else 3) [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 9 (if reversed then 3 else 4) [.indices]) <|
  Domain.View.sequence (Domain.View.observe fsContext "suite"
    (Tests.SourceConnectionPilot.messageTemplate "first") 5 7 10 [.transcript "suite"]) Domain.View.empty

def observed : ConnectionApplications.Certificate template fsRouting (context "first") arguments
    [.data 7] (some 11) frames fsLayout (fsTarget false) where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment

/-- This theorem includes arbitrary guard/helper values and provider replies,
so reject and abort paths are retained. Neither index is a runtime constant. -/
def placed (model : DomainModel) (guard helper : Bool) (seed outer inner : Nat)
    (history : Domain.History model.toCarriers) :=
  first.simulation .empty model
    (.cons guard (.cons helper (.cons seed (.cons outer (.cons inner .nil))))) .nil
    ⟨[⟨"outer",outer⟩,⟨"inner",inner⟩],history⟩ rfl
    ([.data (.boolean guard), .data (.boolean helper), .data (.index seed),
      .data (.index outer), .data (.index inner)] : Domain.Environment model.toCarriers)
    _
    (.cons ⟨guard,rfl,rfl⟩ (.cons ⟨helper,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩
      (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ .nil)))))
    (by simp [ArtifactBinding.Captures])

def observedPlaced (model : DomainModel) (guard helper : Bool) (seed outer inner : Nat)
    (history : Domain.History model.toCarriers) :=
  observed.simulation .empty model
    (.cons guard (.cons helper (.cons seed (.cons outer (.cons inner .nil))))) .nil
    ⟨[⟨"outer",outer⟩,⟨"inner",inner⟩],history⟩ rfl
    ([.data (.boolean guard), .data (.boolean helper), .data (.index seed),
      .data (.index outer), .data (.index inner), .transcript "suite" history] : Domain.Environment model.toCarriers)
    _
    (.cons ⟨guard,rfl,rfl⟩ (.cons ⟨helper,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩
      (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ (.cons rfl .nil))))))
    (by simp [ArtifactBinding.Captures])

-- The root parser does not reserve public record-field names.
private structure ParserRecord where
  services : List Nat := []
example : (show ParserRecord from { services := [] }).services = [] := rfl

-- Finite signature, role, helper declaration, route and output checks refuse
-- mutations before any process or repeat count executes.
example : (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 2 pattern).isOk = false := by decide +kernel
example : True := by
  fail_if_success
    have : template.key.signature = {Tests.SourceConnectionPilot.stepSignature with outputs := [.boolean]} := by rfl
  trivial

example : True := by
  fail_if_success
    have : ConnectionApplications.Certificate template fsRouting (context "first") arguments
        [.data 7] (some 11) frames fsLayout (fsTarget true) :=
      ⟨RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel), by derive_connection_alignment⟩
  trivial

example : True := by
  fail_if_success
    have : ConnectionHelpers.Binding [] Tests.SourceConnectionPilot.gateHelper program := by
      exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  trivial

example : True := by
  fail_if_success
    have : ConnectionApplications.Certificate producerTemplate producerRouting (context "first") arguments
        [.data 6] none frames layout (target "first") :=
      ⟨RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel), by derive_connection_alignment⟩
  trivial
example : True := by
  fail_if_success
    have : ConnectionApplications.Certificate template Tests.SourceConnectionPilot.routing (context "first") arguments
        [.data 5] none frames layout (target "first") := ⟨RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel), by derive_connection_alignment⟩
  trivial
example : True := by
  fail_if_success
    have : ConnectionApplications.Certificate template {Tests.SourceConnectionPilot.routing with messages := []}
        (context "first") arguments [.data 6] none frames layout (target "first") :=
      ⟨RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel), by derive_connection_alignment⟩
  trivial

namespace Repeats
abbrev program := Tests.ConnectionSymbolicRepeat.program
abbrev pattern := Tests.ConnectionSymbolicRepeat.pattern
abbrev routing := Tests.ConnectionSymbolicRepeat.routing Tests.ConnectionSymbolicRepeat.plainContext
abbrev layout := Tests.ConnectionSymbolicRepeat.plainLayout
abbrev target := Tests.ConnectionSymbolicRepeat.plainView

def template : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 1 pattern).toOption.get (by decide +kernel)
def library : Library program.payload [template.key] := .extend .empty template

def form : Form [] [template.key] pattern.scope [.index] :=
  (normalize {strict := true, callees := [template.key]}
    Tests.ConnectionSymbolicRepeat.nestedBody 1 2 pattern).toOption.getD (.halt .refused)

def accepted : ConnectionCertificate.Derivation routing {} program.payload.definitions [template.key]
    [.index] 1 [[0,1]] [.data 3] none [] layout form target := by derive_connection_alignment

-- Generalizing repeats to a shared library preserves the finite certificate
-- size. Both arbitrary counts remain source binders, not expansion bounds.
example : accepted.size = 6 := rfl

def simulation (model : DomainModel) (outer inner seed : Nat)
    (history : Domain.History model.toCarriers) :=
  accepted.librarySimulation library model ⟨[],history⟩ []
    (.cons outer (.cons inner (.cons seed .nil))) rfl
    [.data (.index outer), .data (.index inner), .data (.index seed)]
    (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩ .nil)))
    (by simp [ArtifactBinding.Captures])
end Repeats

#print axioms placed
#print axioms observedPlaced
#print axioms Library.holds
#print axioms Repeats.simulation
end Tests.ConnectionSharedLibrary
