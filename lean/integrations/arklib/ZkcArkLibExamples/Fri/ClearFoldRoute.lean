module

public import ZkcArkLibExamples.Fri.ClearSites
public import ZkcExamples.Structured.FriCommitTerminal
public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.AccessLog

@[expose] public section

/-! Relate the actual field request and delivery in the source Commit loop to
the selected clear descriptor. Dynamic iteration indices and prior histories
are arbitrary. An occurrence at another repeat site cannot satisfy the
source route just by presenting the right reply type. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace ZkcSecurity.ArkLib.Fri.ClearFoldRoute
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.Examples
open ClearSites (event base sites)
open FriScalarQueries (routing publicRoutes context)
open ZkcSecurity.FiatShamir QueryTreeSource

abbrev commitContext := FriSourceCalls.commitment.childContext FriSource.lowDegreeContext
abbrev drawSite := FriCommitRound.serviceSite commitContext 0
abbrev deliverySite := FriCommitRound.serviceSite commitContext 1
abbrev stack := SourceOccurrences.repeatSites (event 1).template

private theorem drawStatic :
    OccurrenceResolution.resolveStatic publicRoutes.snapshot context
      (context.query drawSite (.draw FriSource.extension)) stack publicRoutes.draws = some (event 1).template := by decide +kernel

private theorem deliveryStatic :
    OccurrenceResolution.resolveStatic publicRoutes.snapshot context
      (context.message deliverySite context.validator context.producer) stack publicRoutes.messages = some (event 2).template := by decide +kernel

theorem draw (handle ordinal : Nat) (frames : Original.Frames)
    (matched : frames.map (·.site) = stack) (coordinates : frames.map (·.index) = [ordinal]) :
    (routing .validator handle).draw frames drawSite FriSource.extension handle = some (sites.round ordinal).draw := by
  have found := Original.Routing.draw_of_static (routing := routing .validator handle)
    (by exact (by decide +kernel : context.service.isSome = true)) drawStatic frames matched
  rw [coordinates] at found
  exact found

theorem delivery (handle ordinal : Nat) (frames : Original.Frames)
    (matched : frames.map (·.site) = stack) (coordinates : frames.map (·.index) = [ordinal]) :
    (routing .validator handle).message frames deliverySite context.validator context.producer =
      some (sites.round ordinal).delivery := by
  have found := Original.Routing.message_of_static (routing := routing .validator handle) deliveryStatic frames matched
  rw [coordinates] at found
  exact found

abbrev terminalSite := qualifyProtocolSite commitContext.applicationPrefix FriCommitTerminal.messageSite

private theorem terminalStatic :
    OccurrenceResolution.resolveStatic publicRoutes.snapshot context
      (context.message terminalSite context.producer context.validator) [] publicRoutes.messages = some (event 3).template := by decide +kernel

/-- Only an actual received terminal vector is absorbed. An exhausted proof
still stops at the receive, before the observation is produced. -/
theorem terminalReceive {carriers : Carriers} (handle : Nat) (history : Domain.History carriers) :
    Original.receive (routing .validator handle) ⟨[], history⟩ (.vector FriSource.extension) terminalSite context.producer =
      .call (.receive (.vector FriSource.extension) terminalSite terminalSite (context.role context.producer)) (fun values ↦
        .call (.observe (.message sites.terminal (.vector FriSource.extension values))) (fun _ ↦
          .done (values, ⟨[], history ++ [.message sites.terminal (.vector FriSource.extension values)]⟩))) := by
  have found : (routing .validator handle).message [] terminalSite context.producer context.validator = some sites.terminal :=
    Original.Routing.message_of_static (routing := routing .validator handle) terminalStatic [] rfl
  have mode : (routing .validator handle).mode = .validator := rfl
  have validator : (routing .validator handle).context.validator = context.validator := rfl
  simp only [Original.receive, mode, validator, found, Domain.Payload.ofValue, Ty.isHandle,
    ↓reduceDIte, Original.record, PIR.Process.bind]
  rfl

/-- The validator queries the typed oracle at the actual prefix. The source
continuation uses that reply and observes the matching delivery, in order. -/
theorem drawThenDeliver {carriers : Carriers} (handle ordinal : Nat) (state : Original.State carriers)
    (matched : state.frames.map (·.site) = stack) (coordinates : state.frames.map (·.index) = [ordinal]) :
    let site := sites.round ordinal
    ((Original.query (routing .validator handle) state drawSite FriSource.extension handle).bind fun (beta, after) ↦
      Original.send (routing .validator handle) after (.field FriSource.extension) deliverySite context.producer beta) =
      .call (.query state.history site.draw) (fun reply ↦
        let beta := Original.fieldReply site.draw FriSource.extension (ClearSites.fields ordinal) reply
        .call (.observe (.message site.delivery (.field FriSource.extension beta))) fun _ ↦
          .done ((), {state with history := state.history ++ [.challenge site.draw, .message site.delivery (.field FriSource.extension beta)]})) := by
  dsimp only
  rw [Original.public_query _ _ _ _ _ _ rfl (draw handle ordinal state.frames matched coordinates)]
  have mode : (routing .validator handle).mode = .validator := rfl
  have validator : (routing .validator handle).context.validator = context.validator := rfl
  simp only [PIR.Process.bind, Original.send, mode, validator, delivery handle ordinal state.frames matched coordinates,
    Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record, List.append_assoc]
  rfl

end ZkcSecurity.ArkLib.Fri.ClearFoldRoute
