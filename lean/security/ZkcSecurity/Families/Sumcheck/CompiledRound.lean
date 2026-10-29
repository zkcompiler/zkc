module

public import ZkcSecurity.FiatShamir.DomainViewReading
public import ZkcSecurity.Families.Sumcheck.TableComponentNominal
public import ZkcSecurity.Families.Sumcheck.TableComponentHistory
public import Zkc.Construction.DomainCalculations
public import Zkc.Construction.DomainViewLaws

@[expose] public section

/-! A full scalar validator round with its original SSA frame. The plan is
ordinary occurrence/helper data; a client must prove its exact generated block
is this view. The append helper law concerns every point and challenge. No
honest received message or true scalar claim is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ZkcSecurity.Families.Sumcheck.CompiledRound
open ZkcSecurity.FiatShamir
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir.DomainReduction
open TableComponent.Execution

structure Plan where
  lowSite : String
  highSite : String
  producer : String
  lowTemplate : Template
  highTemplate : Template
  queryTemplate : Template
  deliveryTemplate : Template
  appendHelper : String

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev carriers := Structured.uniformCarriers F G

/-- SSA references after an arbitrary capture frame retain their exact offsets. -/
@[simp] theorem lookup_suffix {A : Type} (captured suffix : List A) (position : Nat) :
    (captured ++ suffix)[captured.length + position]? = suffix[position]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]

@[simp] theorem lookup_first_suffix {A : Type} (captured suffix : List A) :
    (captured ++ suffix)[captured.length]? = suffix[0]? := by
  simpa only [Nat.add_zero] using lookup_suffix captured suffix 0

/-- The entire caller capture frame is arbitrary and retained verbatim. -/
def input (field suite : String) (captured : Domain.Environment (carriers (F := F) (G := G)))
    (index : Nat) (point : List F) (claim : F) (history : Domain.History (carriers (F := F) (G := G))) :
    Domain.Environment (carriers (F := F) (G := G)) :=
  captured ++ [.data (.index index), .data (.vector field point), .data (.field field claim),
    .transcript suite history]

/-- This is an existing View composition with all original checkpoints. -/
def block (plan : Plan) (program : Structured.Program) (context : Context) (field : String) (offset : Nat) :
    Domain.View.Block (ringModel F G).toCarriers :=
  Domain.View.sequence (Domain.View.receive plan.lowSite plan.lowSite plan.producer (.field field) [.data (.field field)]) (
    Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
      Domain.View.sequence (Domain.View.indicesAppend (offset + 5) offset [.indices]) (
        Domain.View.sequence (Domain.View.observe context context.suite plan.lowTemplate (offset + 3) (offset + 4) (offset + 6) [.transcript context.suite]) (
          Domain.View.sequence (Domain.View.receive plan.highSite plan.highSite plan.producer (.field field) [.data (.field field)]) (
            Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
              Domain.View.sequence (Domain.View.indicesAppend (offset + 9) offset [.indices]) (
                Domain.View.sequence (Domain.View.observe context context.suite plan.highTemplate (offset + 7) (offset + 8) (offset + 10) [.transcript context.suite]) (
                  Domain.View.sequence (Domain.View.calculation (ringModel F G) (.fieldAdd field) [(offset + 4), (offset + 8)] [.data (.field field)]) (
                    Domain.View.sequence (Domain.View.calculation (ringModel F G) (.fieldEqual field) [(offset + 2), (offset + 12)] [.data .boolean]) (
                      Domain.View.sequence (Domain.View.guard (offset + 13) []) (
                        Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
                          Domain.View.sequence (Domain.View.indicesAppend (offset + 14) offset [.indices]) (
                            Domain.View.sequence (Domain.View.challenge context context.suite field plan.queryTemplate (offset + 11) (offset + 15) [.data (.field field), .transcript context.suite]) (
                              Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
                                Domain.View.sequence (Domain.View.indicesAppend (offset + 18) offset [.indices]) (
                                  Domain.View.sequence (Domain.View.observe context context.suite plan.deliveryTemplate (offset + 17) (offset + 16) (offset + 19) [.transcript context.suite]) (
                                    Domain.View.sequence (Domain.View.helper (ringModel F G) program plan.appendHelper [(offset + 1), (offset + 16)] [.data (.vector field)]) (
                                      Domain.View.sequence (Domain.View.calculation (ringModel F G) (.fieldConstant field 1) [] [.data (.field field)]) (
                                        Domain.View.sequence (Domain.View.calculation (ringModel F G) (.fieldSubtract field) [(offset + 22), (offset + 16)] [.data (.field field)]) (
                                          Domain.View.sequence (Domain.View.calculation (ringModel F G) (.fieldMultiply field) [(offset + 23), (offset + 4)] [.data (.field field)]) (
                                            Domain.View.sequence (Domain.View.calculation (ringModel F G) (.fieldMultiply field) [(offset + 16), (offset + 8)] [.data (.field field)]) (
                                              Domain.View.sequence (Domain.View.calculation (ringModel F G) (.fieldAdd field) [(offset + 24), (offset + 25)] [.data (.field field)]) (
                                                Domain.View.empty)))))))))))))))))))))))

/-- Every intermediate slot, including the boundary Boolean, is retained. -/
def output (field suite : String) (captured : Domain.Environment (carriers (F := F) (G := G)))
    (index : Nat) (point : List F) (claim : F)
    (history : Domain.History (carriers (F := F) (G := G)))
    (lowOrigin highOrigin queryOrigin deliveryOrigin : Origin) (low high challenge : F) :
    Domain.Environment (carriers (F := F) (G := G)) :=
  input field suite captured index point claim history ++
    [.data (.field field low), .indices [], .indices [index],
      .transcript suite (history ++ [.message lowOrigin (.field field low)]),
      .data (.field field high), .indices [], .indices [index],
      .transcript suite (receivedHistory field lowOrigin highOrigin history low high),
      .data (.field field (low + high)), .data (.boolean (decide (claim = low + high))),
      .indices [], .indices [index], .data (.field field challenge),
      .transcript suite (receivedHistory field lowOrigin highOrigin history low high ++ [.challenge queryOrigin]),
      .indices [], .indices [index],
      .transcript suite (finalHistory field lowOrigin highOrigin queryOrigin deliveryOrigin history low high challenge),
      .data (.vector field (point ++ [challenge])), .data (.field field 1),
      .data (.field field (1 - challenge)), .data (.field field ((1 - challenge) * low)),
      .data (.field field (challenge * high)),
      .data (.field field ((1 - challenge) * low + challenge * high))]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The actual yielded references read back the next point, interpolated
scalar and reached transcript. All remaining cells still belong to output. -/
theorem output_yielded (field suite : String)
    (captured : Domain.Environment (carriers (F := F) (G := G)))
    (index : Nat) (point : List F) (claim : F)
    (history : Domain.History (carriers (F := F) (G := G)))
    (lowOrigin highOrigin queryOrigin deliveryOrigin : Origin) (low high challenge : F) :
    Domain.read (output field suite captured index point claim history
      lowOrigin highOrigin queryOrigin deliveryOrigin low high challenge)
      [captured.length + 21, captured.length + 26, captured.length + 20] =
        some [.data (.vector field (point ++ [challenge])),
          .data (.field field ((1 - challenge) * low + challenge * high)),
          .transcript suite (finalHistory field lowOrigin highOrigin queryOrigin deliveryOrigin
            history low high challenge)] := by
  simp [output, input, Domain.read, List.append_assoc]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Captured private/runtime data survives the entire successful round. -/
theorem output_captured (field suite : String)
    (captured : Domain.Environment (carriers (F := F) (G := G)))
    (index : Nat) (point : List F) (claim : F)
    (history : Domain.History (carriers (F := F) (G := G)))
    (lowOrigin highOrigin queryOrigin deliveryOrigin : Origin) (low high challenge : F) :
    (output field suite captured index point claim history lowOrigin highOrigin queryOrigin
      deliveryOrigin low high challenge).take captured.length = captured := by
  simp [output, input, List.append_assoc]

noncomputable def presented (field suite : String)
    (captured : Domain.Environment (carriers (F := F) (G := G)))
    (index : Nat) (point : List F) (claim : F)
    (history : Domain.History (carriers (F := F) (G := G)))
    (lowOrigin highOrigin queryOrigin deliveryOrigin : Origin)
    (request : queryOrigin.request = some (.draw field)) :
    PIR.Process (NominalField.signature F field)
      (Domain.Environment (carriers (F := F) (G := G))) :=
  .call (.receive lowOrigin) fun low =>
  .call (.receive highOrigin) fun high =>
    if claim = low + high then
      .call (.query queryOrigin request) fun challenge =>
      .call (.deliver deliveryOrigin challenge) fun _ =>
        .done (output field suite captured index point claim history
          lowOrigin highOrigin queryOrigin deliveryOrigin low high challenge)
    else .halt .reject

variable (plan : Plan) (program : Structured.Program) (context : Context) (field : String)
variable (captured : Domain.Environment (carriers (F := F) (G := G)))
  (index : Nat) (point : List F) (claim : F)
  (history : Domain.History (carriers (F := F) (G := G)))
  (lowOrigin highOrigin queryOrigin deliveryOrigin : Origin)
  (lowFound : Domain.templateOrigin context plan.lowTemplate [index] = some lowOrigin)
  (highFound : Domain.templateOrigin context plan.highTemplate [index] = some highOrigin)
  (queryFound : Domain.queryOrigin context context.suite field plan.queryTemplate [index] = some queryOrigin)
  (deliveryFound : Domain.templateOrigin context plan.deliveryTemplate [index] = some deliveryOrigin)
  (lowMessage : lowOrigin.request = none) (highMessage : highOrigin.request = none)
  (deliveryMessage : deliveryOrigin.request = none)
  (request : queryOrigin.request = some (.draw field))
  (append : ∀ point challenge,
    Domain.callHelper (ringModel F G) program plan.appendHelper [.data (.vector field)]
      [.data (.vector field point), .data (.field field challenge)] =
      .returned [.data (.vector field (point ++ [challenge]))])

include lowFound highFound queryFound deliveryFound lowMessage highMessage deliveryMessage append in
/-- All typed replies are related, with exact returned frame and history.
The only helper premise is its explicit all-input operational equation. -/
theorem reading
    (Post : Domain.History (carriers (F := F) (G := G)) →
      Domain.Environment (carriers (F := F) (G := G)) → Prop)
    (post : ∀ low high challenge, claim = low + high →
      Post (finalHistory field lowOrigin highOrigin queryOrigin deliveryOrigin history low high challenge)
        (output field context.suite captured index point claim history
          lowOrigin highOrigin queryOrigin deliveryOrigin low high challenge)) :
    ReadingTo (NominalField.interface (F := F) (G := G) field) Post history
      (block plan program context field captured.length (input field context.suite captured index point claim history))
      (presented field context.suite captured index point claim history
        lowOrigin highOrigin queryOrigin deliveryOrigin request) := by
  simp only [block, presented, Domain.View.sequence, Domain.View.receive, Domain.dataType, Ty.isHandle, Bool.not_false,
    true_and, ite_true, PIR.Process.bind]
  apply ReadingTo.checkpoint
  apply ReadingTo.receive (I := NominalField.signature F field) (.field field)
    plan.lowSite plan.lowSite plan.producer _ (.receive lowOrigin) _ (.message lowOrigin)
    (NominalField.received field lowOrigin) id rfl
      (by intro payload; simpa using NominalField.received_message (F := F) (G := G) field lowOrigin payload)
  intro payload low decoded
  have same := Domain.Payload.ofValue_value decoded
  have payload_eq : payload = .field field low := by
    simpa [Domain.Payload.ofValue, Ty.isHandle] using same.symm
  subst payload
  simp [PIR.Process.bind, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, Domain.View.append, Domain.sortsMatch,
    Domain.Value.sort, input, List.append_assoc, Domain.View.indicesEmpty, Domain.View.indicesAppend,
    Domain.View.observe, lowFound, lowMessage]
  repeat' first | apply ReadingTo.checkpoint | apply ReadingTo.observe
  apply ReadingTo.receive (I := NominalField.signature F field) (.field field)
    plan.highSite plan.highSite plan.producer _ (.receive highOrigin) _ (.message highOrigin)
    (NominalField.received field highOrigin) id rfl
      (by intro payload; simpa using NominalField.received_message (F := F) (G := G) field highOrigin payload)
  intro payload high decoded
  have same := Domain.Payload.ofValue_value decoded
  have payload_eq : payload = .field field high := by
    simpa [Domain.Payload.ofValue, Ty.isHandle] using same.symm
  subst payload
  simp [PIR.Process.bind, Domain.View.append, Domain.sortsMatch,
    Domain.Value.sort, List.append_assoc, Domain.View.calculation, Domain.read, Domain.View.guard,
    Domain.Calculations.fieldAdd (F := F) (G := G),
    Domain.Calculations.fieldEqual (F := F) (G := G), highFound, highMessage]
  repeat' first | apply ReadingTo.checkpoint | apply ReadingTo.observe
  by_cases boundary : claim = low + high
  · simp [boundary, PIR.Process.bind, Domain.View.challenge, queryFound, request,
      Domain.View.helper, append, Domain.read, Domain.View.append, Domain.sortsMatch,
      Domain.Value.sort, List.append_assoc, deliveryFound, deliveryMessage,
      Domain.Calculations.fieldConstant (F := F) (G := G),
      Domain.Calculations.fieldSubtract (F := F) (G := G),
      Domain.Calculations.fieldMultiply (F := F) (G := G),
      Domain.Calculations.fieldAdd (F := F) (G := G)]
    repeat' apply ReadingTo.checkpoint
    apply ReadingTo.query (I := NominalField.signature F field) _ queryOrigin _
      (.query queryOrigin request) _ (fieldReply request) (drawRequest_of_request request) rfl
    intro raw
    apply ReadingTo.absorbSend (I := NominalField.signature F field)
      (.deliver deliveryOrigin (fieldReply request raw)) _
      (.message deliveryOrigin (.field field (fieldReply request raw))) () rfl
    repeat' first | apply ReadingTo.checkpoint | apply ReadingTo.observe
    simpa [Domain.View.empty, output, input, finalHistory, receivedHistory,
      List.append_assoc, boundary, fieldReply] using
      (ReadingTo.done (absorb := NominalField.interface (F := F) (G := G) field)
        _ _ (post low high (fieldReply request raw) boundary))
  · simp [boundary, PIR.Process.bind]
    exact .halt _ .reject


include lowFound highFound queryFound deliveryFound lowMessage highMessage deliveryMessage request append in
/-- Independent coherence follows actual observations, including rejection
before the query and every dependent challenge continuation. -/
theorem coherent
    (Post : Domain.History (carriers (F := F) (G := G)) →
      Domain.Environment (carriers (F := F) (G := G)) → Prop)
    (post : ∀ low high challenge, claim = low + high →
      Post (finalHistory field lowOrigin highOrigin queryOrigin deliveryOrigin history low high challenge)
        (output field context.suite captured index point claim history
          lowOrigin highOrigin queryOrigin deliveryOrigin low high challenge)) :
    CoherentTo Post history
      (block plan program context field captured.length
        (input field context.suite captured index point claim history)) := by
  simp only [block, Domain.View.sequence, Domain.View.receive, Domain.dataType, Ty.isHandle, Bool.not_false,
    true_and, ite_true, PIR.Process.bind]
  apply CoherentTo.checkpoint
  apply CoherentTo.receive
  intro low
  simp [PIR.Process.bind, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, Domain.View.append, Domain.sortsMatch,
    Domain.Value.sort, input, List.append_assoc, Domain.View.indicesEmpty, Domain.View.indicesAppend,
    Domain.View.observe, lowFound, lowMessage]
  repeat' first | apply CoherentTo.checkpoint | apply CoherentTo.observe
  apply CoherentTo.receive
  intro high
  simp [PIR.Process.bind, Domain.View.append, Domain.sortsMatch,
    Domain.Value.sort, List.append_assoc, Domain.View.calculation, Domain.read, Domain.View.guard,
    Domain.Calculations.fieldAdd (F := F) (G := G),
    Domain.Calculations.fieldEqual (F := F) (G := G), highFound, highMessage]
  repeat' first | apply CoherentTo.checkpoint | apply CoherentTo.observe
  by_cases boundary : claim = low + high
  · simp [boundary, PIR.Process.bind, Domain.View.challenge, queryFound, request,
      Domain.View.helper, append, Domain.read, Domain.View.append, Domain.sortsMatch,
      Domain.Value.sort, List.append_assoc, deliveryFound, deliveryMessage,
      Domain.Calculations.fieldConstant (F := F) (G := G),
      Domain.Calculations.fieldSubtract (F := F) (G := G),
      Domain.Calculations.fieldMultiply (F := F) (G := G),
      Domain.Calculations.fieldAdd (F := F) (G := G)]
    repeat' apply CoherentTo.checkpoint
    apply CoherentTo.query _ queryOrigin _ (drawRequest_of_request request)
    intro raw
    repeat' first | apply CoherentTo.checkpoint | apply CoherentTo.observe
    simpa [Domain.View.empty, output, input, finalHistory, receivedHistory,
      List.append_assoc, boundary, fieldReply] using
      (CoherentTo.done
        _ _ (post low high (fieldReply request raw) boundary))
  · simp [boundary, PIR.Process.bind]
    exact .halt _ .reject

end ZkcSecurity.Families.Sumcheck.CompiledRound
