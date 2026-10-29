module

public import Zkc.Construction.Uniform.DomainHandler
public import Zkc.Source.Structured.CommonAdapter
public import Zkc.Construction.DomainCalculations
public meta import Zkc.Construction.ArtifactBindingTactic

@[expose] public section

/-! Shared source-process views for the finite scalar consumers. This folds
participant effects, never constructed instructions. The actual artifact is
connected separately by the generated Domain correspondence rules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.Uniform.SourceProcess
open Zkc Zkc.Source Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
variable {F G A : Type}

/-- The five finite artifacts have no repeat coordinates. Their actual
origins already are the legacy static keys. This adapter is installed before
the legacy oracle is invoked, including when that oracle maintains a cache. -/
def legacyOrigin (origin : Origin) : Origin := origin

theorem static_origin (origin : Origin) :
    legacyOrigin (Domain.atCoordinates origin []) = origin := rfl

def receive (context : Context) (ty : Common.Native.Ty) (site : String) (sender : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G))
      (Common.Native.ScalarValue F G ty × Domain.History (Structured.uniformCarriers F G)) :=
  let origin := context.message site sender context.validator
  match ty with
  | .boolean =>
      .call (.receive .boolean site site (context.role sender)) fun value =>
      let event := Domain.Event.message origin (.boolean value)
      .call (.observe event) fun _ => .done (value, history ++ [event])
  | .field field =>
      .call (.receive (.field field) site site (context.role sender)) fun value =>
      let event := Domain.Event.message origin (.field field value)
      .call (.observe event) fun _ => .done (value, history ++ [event])
  | .group group =>
      .call (.receive (.group group) site site (context.role sender)) fun value =>
      let event := Domain.Event.message origin (.group group value)
      .call (.observe event) fun _ => .done (value, history ++ [event])
  | .service _ => .halt .refused

def send (context : Context) (ty : Common.Native.Ty) (site : String) (receiver : Nat)
    (value : Common.Native.ScalarValue F G ty)
    (history : Domain.History (Structured.uniformCarriers F G)) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G))
      (Unit × Domain.History (Structured.uniformCarriers F G)) :=
  match Payload.ofValue ty value with
  | none => .halt .refused
  | some payload =>
      let event := Domain.Event.message (context.message site context.validator receiver)
        (embedPayload payload)
      .call (.observe event) fun _ => .done ((), history ++ [event])

def query (context : Context) (site field : String)
    (history : Domain.History (Structured.uniformCarriers F G)) :
    PIR.Process (Domain.effects (Structured.uniformCarriers F G))
      (F × Domain.History (Structured.uniformCarriers F G)) :=
  let origin := context.query site (.draw field)
  .call (.query history origin) fun answer =>
    .done (answer, history ++ [.challenge origin])

/-- A direct view of a scalar participant, carrying its exact transcript
suffix. Delivery sends become observations at their original positions. -/
def sourceView (context : Context) : PIR.Process (Actions F G) A →
    Domain.History (Structured.uniformCarriers F G) →
    PIR.Process (Domain.effects (Structured.uniformCarriers F G))
      (A × Domain.History (Structured.uniformCarriers F G))
  | .done value, history => .done (value, history)
  | .halt reason, _ => .halt reason
  | .call (.receive ty site sender) next, history =>
      (receive context ty site sender history).bind fun (value, final) =>
        sourceView context (next value) final
  | .call (@Participant.Action.send _ _ _ _ ty site receiver value) next, history =>
      (send context ty site receiver value history).bind fun (_, final) =>
        sourceView context (next ()) final
  | .call (.query site field _) next, history =>
      (query context site field history).bind fun (answer, final) =>
        sourceView context (next answer) final

theorem sourceView_map {B : Type} (context : Context) (process : PIR.Process (Actions F G) A)
    (project : A → B) (history : Domain.History (Structured.uniformCarriers F G)) :
    sourceView context (process.bind fun value => .done (project value)) history =
      (sourceView context process history).bind fun result => .done (project result.1, result.2) := by
  induction process generalizing history with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      cases operation <;> simp only [PIR.Process.bind, sourceView, PIR.Process.bind_assoc]
      all_goals congr 1; funext result; exact ih _ result.2

theorem readback_message (history : Domain.History (Structured.uniformCarriers F G))
    (suffix : History F G) (mapped : readbackHistory legacyOrigin history = some suffix)
    (origin : Origin) (payload : Payload F G) :
    readbackHistory legacyOrigin (history ++ [.message origin (embedPayload payload)]) =
      some (suffix ++ [.message origin payload]) := by
  rw [readbackHistory_append, mapped]
  cases payload <;> rfl

theorem readback_challenge (history : Domain.History (Structured.uniformCarriers F G))
    (suffix : History F G) (mapped : readbackHistory legacyOrigin history = some suffix)
    (origin : Origin) :
    readbackHistory legacyOrigin (history ++ [.challenge origin]) =
      some (suffix ++ [.challenge origin]) := by
  rw [readbackHistory_append, mapped]
  rfl

/-- The complete scalar validator ABI: its decision and transcript suffix. -/
def returnValues (suite : String)
    (result : Bool × Domain.History (Structured.uniformCarriers F G)) :
    Domain.Environment (Structured.uniformCarriers F G) :=
  [.data (.boolean result.1), .transcript suite result.2]

/-- Read the selected acceptance value without replacing a malformed sort by
an accepting Boolean. The full returned tuple is connected independently. -/
def acceptance (values : Domain.Environment (Structured.uniformCarriers F G)) : Option Bool :=
  match values with
  | .data ⟨.boolean, _, decision⟩ :: _ => some decision
  | _ => none

section Calculations
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem groupScale (group field : String) (point : G) (scalar : F) :
    Domain.calculate (Structured.ringModel F G) (.groupScale group field)
      [.data (.group group point), .data (.field field scalar)] =
      .returned [.data (.group group (scalar • point))] := by
  simp only [Domain.calculate, Calculation.op, Structured.Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

theorem groupAdd (group : String) (left right : G) :
    Domain.calculate (Structured.ringModel F G) (.groupAdd group)
      [.data (.group group left), .data (.group group right)] =
      .returned [.data (.group group (left + right))] := by
  simp only [Domain.calculate, Calculation.op, Structured.Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

theorem groupEqual (group : String) (left right : G) :
    Domain.calculate (Structured.ringModel F G) (.groupEqual group)
      [.data (.group group left), .data (.group group right)] =
      .returned [.data (.boolean (decide (left = right)))] := by
  simp only [Domain.calculate, Calculation.op, Structured.Op.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte]
  rfl

theorem booleanAnd (left right : Bool) :
    Domain.calculate (Structured.ringModel F G) .booleanAnd
      [.data (.boolean left), .data (.boolean right)] =
      .returned [.data (.boolean (left && right))] := rfl

end Calculations

section Handler
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Full outcome and unread-proof law for the source effect fold. It accepts
arbitrary typed public values, proof heads, oracle answers and stopped prefixes.
The initial legacy history is an opaque prefix, outside nominal serialization. -/
theorem sourceView_transform (context : Context) (challenge : History F G → m F)
    (process : PIR.Process (Actions F G) A) (initial : History F G)
    (history : Domain.History (Structured.uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory legacyOrigin history = some suffix) (proof : Proof F G) :
    runK legacyOrigin initial challenge (sourceView context process history) proof
        (fun result unread => pure (.returned result.1, unread)) =
      transform context challenge process (initial ++ suffix) proof := by
  induction process generalizing history suffix proof with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      cases operation with
      | receive ty site sender =>
          rw [sourceView, runK_bind, transform_eq_receive]
          cases ty <;> cases proof with
          | nil => rfl
          | cons payload unread =>
              cases payload <;>
                simp only [receive, runK, Value.decode, Payload.value]
              all_goals try (split_ifs <;> subst_vars <;> simp_all only)
              all_goals first
                | simpa only [List.append_assoc, embedPayload] using (ih _ _ _
                    (readback_message history suffix mapped
                      (context.message site sender context.validator) (.boolean _)) unread)
                | simpa only [List.append_assoc, embedPayload] using (ih _ _ _
                    (readback_message history suffix mapped
                      (context.message site sender context.validator) (.field _ _)) unread)
                | simpa only [List.append_assoc, embedPayload] using (ih _ _ _
                    (readback_message history suffix mapped
                      (context.message site sender context.validator) (.group _ _)) unread)
      | send site receiver value =>
          rename_i ty
          rw [sourceView, runK_bind, transform_eq_send]
          cases ty <;> simp only [send, Payload.ofValue, runK]
          all_goals
            simpa only [List.append_assoc] using
              (ih () _ _ (readback_message history suffix mapped _ _) proof)
      | query site field arguments =>
          rw [sourceView, runK_bind, transform_eq_query]
          have request : (context.query site (.draw field)).request = some (.draw field) := rfl
          simp only [query, runK, drawRequest_of_draw _ _ request, ite_true,
            query_of_draw legacyOrigin initial challenge history _ field request suffix mapped]
          simp only [bind_assoc, pure_bind, legacyOrigin]
          congr 1
          funext answer
          simp only [eq_mpr_eq_cast, cast_eq]
          simpa only [List.append_assoc] using
            ih answer _ _ (readback_challenge history suffix mapped _) proof

theorem sourceView_transform_map {B : Type} (context : Context) (challenge : History F G → m F)
    (process : PIR.Process (Actions F G) A) (project : A → B)
    (initial : History F G) (proof : Proof F G) :
    runK legacyOrigin initial challenge (sourceView context process []) proof
        (fun result unread => pure (.returned (project result.1), unread)) =
      transform context challenge (process.bind fun value => .done (project value)) initial proof := by
  have law := sourceView_transform context challenge
    (process.bind fun value => .done (project value)) initial [] [] rfl proof
  simpa only [sourceView_map, runK_bind, runK, List.append_nil] using law

end Handler
end Zkc.Construction.Uniform.SourceProcess

@[expose] public meta section
namespace Zkc.Construction.Uniform.SourceProcess
open Lean
/-- Shared proof normalization of the checked finite views. Arithmetic laws
are equations of Domain.calculate, not another calculation implementation. -/
macro "normalize_scalar_connection" " unfolding " "[" definitions:term,* "]" : tactic => do
  let defs := definitions.getElems
  `(tactic|
    (normalize_artifact_operations [groupScale, groupAdd, groupEqual, booleanAnd]
      unfolding [$defs,*, sourceView, receive, send, query, returnValues,
        PIR.Process.interpret, Zkc.Construction.Original.forgetCheckpoints,
        Zkc.Construction.Domain.templateOrigin, Zkc.Construction.Domain.queryOrigin,
        Zkc.Construction.Template.origin, Zkc.Construction.Template.qualify,
        Zkc.Construction.Template.repeats, Zkc.Construction.Domain.atCoordinates,
        Zkc.Construction.Context.message, Zkc.Construction.Context.query,
        Zkc.Construction.Context.role, Zkc.Construction.Context.suite,
        Zkc.Construction.Context.contract, Zkc.Construction.Context.request,
        Zkc.Construction.Context.replacement?, Zkc.Construction.Context.service,
        Zkc.Construction.Context.fiatShamir,
        Zkc.Construction.Payload.ofValue,
        Zkc.Source.Structured.Ty.isHandle, Bool.not_false, Bool.not_true,
        List.append_assoc, List.isEmpty_nil, List.take_nil,
        Zkc.Construction.Domain.Calculations.fieldAdd,
        Zkc.Construction.Domain.Calculations.fieldEqual]
    <;> rfl))
end Zkc.Construction.Uniform.SourceProcess
