import Zkc.Construction.ConnectionApplications
import Tests.SourceConnectionPilot

/-! Actual-prefix/root transport on the earlier nested client, together with
the complementary finite producer/private-service client. These use existing
callee and artifact derivations; no root equation is an instance premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
noncomputable section
namespace Tests.ConnectionApplications
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open NormalForm Original
namespace Nested
open Tests.SourceConnectionPilot
variable (model : DomainModel)

/-- Lookup states the captured prefix explicitly, including the selected
iteration observations and the payload's actual closed/component helpers. -/
theorem captured_root :
    invokeProtocol (Occurrence.table model program.payload) runDefinition.signature =
      runDefinition.denoteWithOn model (.silent _) Occurrence.actions
        (Occurrence.helpers model program.payload)
        ([stepDefinition].foldl (fun table definition => extendProtocolTableOn model (.silent _)
          Occurrence.actions (Occurrence.helpers model program.payload) table definition Occurrence.iterations) [])
        Occurrence.iterations :=
  protocol_invoke_declarationOn model (.silent _) Occurrence.actions
    (Occurrence.helpers model program.payload) Occurrence.iterations
    program.payload.protocols program.payload.protocolsLinked [stepDefinition] runDefinition [] rfl

def normalized (outer inner : Nat) (guard helper : Bool) (seed : Nat) :=
  (rootForm.denoteOn model Occurrence.actions (Occurrence.helpers model program.payload)
    (LawResults.empty model) {}
    (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model program.payload)
      (Occurrence.table model program.payload) {} 1) (noCallees model _)
    (.cons outer (.cons inner (.cons guard (.cons helper (.cons seed .nil)))))).bind
      fun values => .done (maskValues 1 runSignature.outputScopes values)

theorem actual_root (outer inner : Nat) (guard helper : Bool) (seed : Nat) :
    Occurrence.participant model program 1 (sourceInputs model outer inner guard helper seed) =
      normalized model outer inner guard helper seed := by
  exact normalize_program_occurrence program {} 1 rootPattern rootForm
    (by kernel_rfl) (by rfl) (by intro other bound different; exact different)
    (LawResults.empty model) (noCallees model _) (sourceInputs model outer inner guard helper seed)
    (.cons outer (.cons inner (.cons guard (.cons helper (.cons seed .nil)))))
    (by kernel_rfl) (LawsHold.empty _ _) (noCallees_hold _ _)

/-- Nested symbolic counts, stopping helper, all receive replies and complete
returns use the generic actual-payload normalization wrapper. -/
def composed (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns runSignature context 1 artifact)
      (fun _ frame => ArtifactBinding.Captures (inputFrame model outer inner guard helper seed) frame)
      (fold routing (normalized model outer inner guard helper seed) ⟨[],history⟩)
      (Domain.participant model program context artifact (inputFrame model outer inner guard helper seed)) := by
  rw [← actual_root]
  exact Tests.SourceConnectionPilot.composed model outer inner guard helper seed history
end Nested

namespace PrivateProducer
open Tests.SourceConnectionPilot.FiatShamir
variable (model : DomainModel)

def pattern : InputPattern inputs := .cons .absent (.cons .absent (.cons .present .nil))
def form : Form [] [] pattern.scope outputs :=
  (normalize {} runBody 0 2 pattern).toOption.getD (.halt .refused)
def normalized :=
  (form.denoteOn model Occurrence.actions (Occurrence.helpers model program.payload)
    (LawResults.empty model) {}
    (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model program.payload)
      (Occurrence.table model program.payload) {} 0) (noCallees model _) (.cons 91 .nil)).bind
      fun values => .done (maskValues 0 runSignature.outputScopes values)

theorem actual_root (accept : Bool) :
    source model .producer accept = normalized model := by
  exact normalize_program_occurrence program {} 0 pattern form
    (by kernel_rfl) (by rfl) (by intro other bound different; exact different)
    (LawResults.empty model) (noCallees model _) (sourceInputs model .producer accept)
    (.cons 91 .nil) (by kernel_rfl) (LawsHold.empty _ _) (noCallees_hold _ _)

/-- The same root theorem handles absent inputs and a private producer draw;
this complementary case is finite and does not claim a private repeated loop. -/
def composed (accept : Bool) (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns signature context 0 producer)
      (fun _ frame => ArtifactBinding.Captures (producerInputs model history) frame)
      (fold (routing .producer) (normalized model) ⟨[],history⟩)
      (Domain.participant model program context producer (producerInputs model history)) := by
  rw [← actual_root model accept]
  exact producer_composed model accept history
end PrivateProducer
end Tests.ConnectionApplications
