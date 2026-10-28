module

public import TestsSecurity.RootConnectionPublicDraw
public import ZkcSecurity.FiatShamir.RootConnectionSampledReadback

@[expose] public section

/-! Property-specific consumer checks. Public endpoint reading, successful
source-pair readback and private-service authorization remain distinct inputs.
The tests quantify private replies and preserve their complete residuals.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
namespace TestsSecurity.RootConnectionConsumers
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir
open RootConnectionPublicDraw

theorem source_pair (model : DomainModel) (history : Domain.History model.toCarriers) :
    Readback (fun producer validator =>
      producer.1.get (.there .here) = validator.1.get (.there .here) ∧
      producer.2.history = validator.2.history)
      (producerRoot.source model [.transcript "suite" history])
      (root.source model [.transcript "suite" history]) := by
  apply Readback.query history (context.query "challenge" (.draw "bls12-381.fr")) rfl
  intro answer
  apply Readback.observeLeft
  apply Readback.observeRight
  exact .done ⟨rfl, rfl⟩

/-- Both actual artifact returns are retained, including the producer's field
and the validator's Boolean, field and transcript. -/
theorem actual_pair (model : DomainModel) (history : Domain.History model.toCarriers) :
    Readback (fun actualP actualV => ∃ sourceP sourceV,
      (sourceP.1.get (.there .here) = sourceV.1.get (.there .here) ∧
        sourceP.2.history = sourceV.2.history) ∧
      Original.CompleteReturns program.payload.entry.signature producerRouting.context 0 producerArtifact sourceP actualP ∧
      Original.CompleteReturns program.payload.entry.signature routing.context 1 artifact sourceV actualV)
      (Domain.participant model program context producerArtifact [.transcript "suite" history])
      (Domain.participant model program context artifact [.transcript "suite" history]) :=
  RootConnection.honestReadback producerRoot root model _ _ _ (source_pair model history)

section PrivateService
variable {carriers : Carriers}

def privateSource (port : ServicePort) (origin : Origin) :=
  (PIR.Process.call (.localService port origin) fun reply => .done (reply, true) :
    PIR.Process (Domain.effects carriers) (Domain.Raw (.challenge origin : Domain.Event carriers) × Bool))
def privateTarget (port : ServicePort) (origin : Origin) (frame : Domain.Environment carriers) :=
  (PIR.Process.call (.localService port origin) fun reply =>
    .call (.checkpoint frame) fun _ => .done (reply, true) :
    PIR.Process (Domain.effects carriers) (Domain.Raw (.challenge origin : Domain.Event carriers) × Bool))

/-- The private reply is arbitrary and is retained as a non-Boolean residual;
the target's additional physical checkpoint has its explicit live obligation. -/
def privateSimulation (port : ServicePort) (origin : Origin) (frame : Domain.Environment carriers) :
    Original.Simulation Eq (fun _ reached => reached = frame)
      (privateSource port origin) (privateTarget port origin frame) :=
  .call (.localService port origin) fun _ => .checkpoint frame rfl (.done rfl)

theorem private_readback (port : ServicePort) (origin : Origin) (frame : Domain.Environment carriers)
    (Allowed : ServicePort → Origin → Prop) (authorized : Allowed port origin) :
    SampledReadback Allowed
      (fun target (_ : Unit) => ∃ source,
        source.1 = target.1 ∧ source.2 = true ∧ source = target)
      (privateTarget port origin frame) (.done ()) := by
  have source : SampledReadback Allowed (fun source (_ : Unit) => source.2 = true)
      (privateSource (carriers := carriers) port origin) (.done ()) :=
    .localServiceLeft port origin authorized (fun _ => .deterministic (.done rfl))
  apply (SampledReadback.original_left (privateSimulation port origin frame) source).mono
  intro target value related
  obtain ⟨source, accepted, same⟩ := related
  exact ⟨source, congrArg Prod.fst same, accepted, same⟩

/-- The same private computation has no public endpoint bridge. Its successful
readback cannot be repackaged as public Fiat-Shamir absorption. -/
theorem private_not_public (port : ServicePort) (origin : Origin)
    (history : Domain.History carriers) (presented : PIR.Process (NominalDomain.signature carriers)
      (Domain.Raw (.challenge origin : Domain.Event carriers) × Bool)) :
    ¬ DomainReduction.Bridge NominalDomain.interface (fun _ _ => True) history
      (privateSource port origin) presented := by
  intro bridge
  cases bridge.coherent

end PrivateService

#print axioms source_pair
#print axioms actual_pair
#print axioms private_readback
#print axioms private_not_public
#print axioms SampledReadback.original_left
#print axioms SampledReadback.original_right
#print axioms SampledReadback.original
#print axioms RootConnection.sampledReadback

end TestsSecurity.RootConnectionConsumers
