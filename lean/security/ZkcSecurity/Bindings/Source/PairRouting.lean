module

public import ZkcSecurity.Bindings.Source.Pair
public import ZkcSecurity.Bindings.Transcript.DomainViewReading
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! Shared route agreement follows from successful source resolution and the
original def-use association. Coverage is supplied independently by each root;
this module authors no transcript layout or per-instance route proof.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Source
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir

theorem message_origin {routing : Original.Routing} {frames : Original.Frames}
    {site : String} {sender receiver : Nat} {origin : Origin}
    (found : routing.message frames site sender receiver = some origin) :
    origin = Domain.atCoordinates (routing.context.message site sender receiver) (frames.map (·.index)) :=
  OccurrenceResolution.resolved_origin found

theorem draw_origin {routing : Original.Routing} {frames : Original.Frames}
    {site field : String} {handle : Nat} {origin : Origin}
    (found : routing.draw frames site field handle = some origin) :
    origin = Domain.atCoordinates (routing.context.query site (.draw field)) (frames.map (·.index)) := by
  unfold Original.Routing.draw at found
  split at found
  · exact OccurrenceResolution.resolved_origin found
  · cases found

/-- Successful delivery resolution fixes both canonical origins. Uniqueness
of the source's draw/delivery associations identifies the same original query. -/
theorem delivery_origins {routing : Original.Routing} {frames : Original.Frames}
    {query site field : String} {sender : Nat} {draw message : Origin}
    (owned : (query, site) ∈ routing.context.draws)
    (found : routing.delivery frames site field sender = some (draw, message)) :
    draw = Domain.atCoordinates (routing.context.query query (.draw field)) (frames.map (·.index)) ∧
    message = Domain.atCoordinates (routing.context.message site sender routing.context.producer)
      (frames.map (·.index)) := by
  unfold Original.Routing.delivery at found
  split at found
  · cases found
  · rename_i unique
    have uniqueMessages : (routing.context.draws.map Prod.snd).Nodup := by
      simp only [Bool.or_eq_true, Bool.not_eq_true, not_or] at unique
      simpa using unique.2
    dsimp only [bind, Option.bind] at found
    split at found
    · rename_i candidate selected
      have member : candidate ∈ routing.deliveries.filter (fun candidate =>
          Original.deliveryValid routing.snapshot routing.context candidate.draw candidate.message &&
            candidate.message.qualify (candidate.message.event[2]?.getD "") == site &&
            routing.context.draws.contains
              (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), site)) := by
        rw [selected]
        exact List.mem_singleton_self _
      have admitted := (List.mem_filter.mp member).2
      simp only [Bool.and_eq_true, List.contains_iff_mem] at admitted
      have sameQuery : candidate.draw.qualify (candidate.draw.event[2]?.getD "") = query :=
        congrArg Prod.fst (List.inj_on_of_nodup_map uniqueMessages admitted.2 owned rfl)
      cases messageRoute : OccurrenceResolution.resolve routing.snapshot routing.context
          (routing.context.message site sender routing.context.producer) frames [candidate.message] with
      | none => simp only [messageRoute, reduceCtorEq] at found
      | some messageOrigin =>
        simp only [messageRoute] at found
        cases drawRoute : OccurrenceResolution.resolve routing.snapshot routing.context
            (routing.context.query (candidate.draw.qualify (candidate.draw.event[2]?.getD ""))
              (.draw field)) frames [candidate.draw] with
        | none => simp only [drawRoute, reduceCtorEq] at found
        | some drawOrigin =>
          simp only [drawRoute, pure, Option.some.injEq,
            Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          exact ⟨by simpa only [sameQuery] using OccurrenceResolution.resolved_origin drawRoute,
            OccurrenceResolution.resolved_origin messageRoute⟩
    · cases found

def PairScope.ofContext (context : Context) : PairScope :=
  ⟨context.producer, context.validator, context.draws⟩

/-- Finite configuration facts suffice for interpreting any covered paired
process. Neither routing candidate lists nor protocol names occur in this API. -/
theorem publicFoldLaws {carriers : Carriers} (context : Context) (replacement : Replacement)
    (profile : context.profile = .fiatShamir replacement)
    (routingP routingV : Original.Routing)
    (contextP : routingP.context = context) (contextV : routingV.context = context)
    (modeP : routingP.mode = .producer) (modeV : routingV.mode = .validator)
    (noLocal : routingV.locals = []) :
    Pair.FoldLaws (carriers := carriers) (PairScope.ofContext context) routingP routingV := by
  have profileP : routingP.context.profile = .fiatShamir replacement := by rw [contextP, profile]
  have profileV : routingV.context.profile = .fiatShamir replacement := by rw [contextV, profile]
  constructor
  · intro ty site producer validator value state data roles coveredP coveredV
    obtain ⟨rfl, rfl⟩ := roles
    simp only [Original.ActionCovered, Original.Routing.self, modeP] at coveredP
    simp only [Original.ActionCovered, profileV, modeV, Original.Routing.self] at coveredV
    obtain ⟨_, originP, routeP⟩ := coveredP
    obtain ⟨_, originV, routeV⟩ := coveredV
    have same : originP = originV := by
      rw [message_origin routeP, message_origin routeV, contextP, contextV]
      rfl
    subst originV
    simp only [Original.operations, profileP, profileV]
    simp only [Original.receive, modeV, routeV, Original.send, modeP, routeP,
      Domain.Payload.ofValue, data, ↓reduceDIte, Original.record, PIR.Process.bind]
    apply Readback.sendReceive _ _ _ _ _ _ ⟨ty, data, value⟩ value
      (by simp [Domain.Payload.value])
    apply Readback.observeLeft
    apply Readback.observeRight
    exact .done ⟨rfl, rfl⟩
  · intro field query delivery producer validator handle state roles owned coveredP coveredV sends
    obtain ⟨rfl, rfl⟩ := roles
    simp only [Original.ActionCovered, profileP, modeP] at coveredP
    obtain ⟨drawP, messageP, receiveRoute, requestP⟩ := coveredP
    simp only [Original.ActionCovered] at coveredV
    have publicDraw : routingV.mode = .validator ∧ ∃ origin,
        routingV.draw state.frames query field handle = some origin ∧
          origin.request = some (.draw field) := by
      rcases coveredV with publicDraw | ⟨port, origin, localRoute, _⟩
      · exact publicDraw
      · simp [Original.Routing.local, noLocal] at localRoute
    obtain ⟨_, drawV, queryRoute, _⟩ := publicDraw
    have canonical := delivery_origins (by simpa only [contextP, PairScope.ofContext] using owned) receiveRoute
    have sameDraw : drawP = drawV := by
      rw [canonical.1, draw_origin queryRoute, contextP, contextV]
    subst drawV
    simp only [Original.operations, profileP, profileV]
    change Readback _ (Original.receive routingP state (.field field) delivery _)
      ((Original.query routingV state query field handle).bind fun (value, reached) =>
        (Original.send routingV reached (.field field) delivery _ value).bind
          fun (_, final) => .done (value, final))
    rw [Original.producer_delivery routingP state delivery field _ drawP messageP modeP receiveRoute requestP]
    rw [Original.public_query routingV state query field handle drawP modeV queryRoute]
    simp only [PIR.Process.bind]
    apply Readback.query _ _ (DomainReduction.drawRequest_of_request requestP)
    intro reply
    have sendCovered := sends (Original.fieldReply drawP field requestP reply)
    simp only [Original.ActionCovered, Original.Routing.self, modeV] at sendCovered
    obtain ⟨_, messageV, sendRoute⟩ := sendCovered
    have sameMessage : messageP = messageV := by
      rw [canonical.2, message_origin sendRoute, contextP, contextV]
      rfl
    subst messageV
    have sendRoute' : routingV.message
        ({ state with history := state.history ++ [.challenge drawP] } : Original.State carriers).frames
          delivery routingV.context.validator (PairScope.ofContext context).producer = some messageP := sendRoute
    simp only [Original.send, modeV, sendRoute', Domain.Payload.ofValue, Original.record]
    apply Readback.observeLeft
    apply Readback.observeRight
    exact .done ⟨by simp only [List.append_assoc, List.singleton_append], rfl⟩

end ZkcSecurity.Source
