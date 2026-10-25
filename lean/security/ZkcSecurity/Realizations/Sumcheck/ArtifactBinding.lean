module

public import Zkc.Construction.ArtifactBinding
public import Zkc.Construction.OriginalABI
public import Zkc.Source.Structured.Labels
public import ZkcExamples.Structured.OriginalSumcheckLibrary
public import ZkcSecurity.Realizations.Sumcheck.DomainHelpers

@[expose] public section

/-! The one original-library callback binding. Source normal forms are proved
from the admitted Reduce body. Origin equations are individual action-routing
obligations, independently checked against the original snapshot. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

structure Origins where
  low : Origin
  high : Origin
  draw : Origin
  delivery : Origin

/-- Static source occurrence data, independent of the compiled instruction
layout. The source checker authorizes the actual call/repeat/event path. -/
structure Occurrence where
  entry : String
  library : String
  application : String

def Occurrence.protocol (occurrence : Occurrence) : ProtocolContext :=
  ({} : ProtocolContext).enter occurrence.application [0, 1]

def Occurrence.steps (occurrence : Occurrence) : List Step :=
  [⟨"apply", occurrence.entry, occurrence.application⟩,
   ⟨"repeat", occurrence.library, "s15"⟩]

def Occurrence.message (occurrence : Occurrence) (site : String) (sender receiver : String) : Template :=
  ⟨occurrence.entry, occurrence.steps,
    ["message", occurrence.library, site, site, sender, receiver]⟩

def Occurrence.low (occurrence : Occurrence) : Template :=
  occurrence.message (encodedLabel "round" ++ "_0") "role00000000" "role00000001"
def Occurrence.high (occurrence : Occurrence) : Template :=
  occurrence.message (encodedLabel "round" ++ "_1") "role00000000" "role00000001"
def Occurrence.delivery (occurrence : Occurrence) : Template :=
  occurrence.message (encodedLabel "delivery" ++ "_0") "role00000001" "role00000000"
def Occurrence.draw (occurrence : Occurrence) : Template :=
  ⟨occurrence.entry, occurrence.steps,
    ["query", occurrence.library, encodedLabel "challenge", "input_5",
      "random.bls12-381.fr/0", "draw", "role00000001"]⟩

def Occurrence.messages (occurrence : Occurrence) : List Template :=
  [occurrence.low, occurrence.high, occurrence.delivery]

def Occurrence.origins (occurrence : Occurrence) (context : Zkc.Construction.Context)
    (index : Nat) : Origins :=
  { low := Domain.atCoordinates (context.message
      (SumcheckVerifierLaws.lowSite occurrence.protocol) 0 1) [index]
    high := Domain.atCoordinates (context.message
      (SumcheckVerifierLaws.highSite occurrence.protocol) 0 1) [index]
    draw := Domain.atCoordinates (context.query
      (SumcheckVerifierLaws.challengeSite occurrence.protocol) (.draw "bls12-381.fr")) [index]
    delivery := Domain.atCoordinates (context.message
      (SumcheckVerifierLaws.deliverySite occurrence.protocol) 1 0) [index] }

/-- An SSA coordinate with a fixed nominal output sort. The coordinate is
candidate layout data; only a full simulation proves that it contains the value. -/
structure OutputReference (sort : ValueSort) where
  index : Nat
  deriving DecidableEq, Repr

/-- The validator callback's complete physical result ABI. Capture length is
independent of these selected coordinates. -/
structure VerifierOutputs (suite : String) where
  point : OutputReference (.data (.vector "bls12-381.fr"))
  scalar : OutputReference (.data (.field "bls12-381.fr"))
  transcript : OutputReference (.transcript suite)
  deriving DecidableEq, Repr

def VerifierOutputs.references {suite : String} (outputs : VerifierOutputs suite) : List Nat :=
  [outputs.point.index, outputs.scalar.index, outputs.transcript.index]

def VerifierOutputs.sorts (suite : String) : List ValueSort :=
  [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript suite]

/-- Read exactly three actual loop yields with the installed nominal sorts.
This checks the candidate ABI; it does not certify callback semantics. -/
def VerifierOutputs.ofYields (suite : String) (yielded : List Nat)
    (sorts : List ValueSort) : Option (VerifierOutputs suite) :=
  match yielded with
  | [point, scalar, transcript] =>
      if sorts = VerifierOutputs.sorts suite then
        some ⟨⟨point⟩, ⟨scalar⟩, ⟨transcript⟩⟩ else none
  | _ => none

/-- Full six-slot original callback ABI, exact live data references, reached
transcript and source occurrence stack. Four producer slots are absent here. -/
def VerifierReturns (context : Zkc.Construction.Context) (outputs : VerifierOutputs context.suite)
    (frames : Zkc.Construction.Original.Frames)
    (source : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
      Zkc.Construction.Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point scalar, source.1 = SumcheckVerifierLaws.embedV (some point, some scalar) ∧
    frame[outputs.point.index]? = some (.data (.vector "bls12-381.fr" point)) ∧
    frame[outputs.scalar.index]? = some (.data (.field "bls12-381.fr" scalar)) ∧
    frame[outputs.transcript.index]? = some (.transcript context.suite source.2.history) ∧
    source.2.frames = frames

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem verifier_returns_abi (context : Zkc.Construction.Context) (outputs : VerifierOutputs context.suite)
    (frames : Zkc.Construction.Original.Frames)
    (source : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
      Zkc.Construction.Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G))
    (related : VerifierReturns context outputs frames source frame) :
    Zkc.Construction.Original.ValuesHolds frame
      [.absent, .absent, .absent, .absent, .data outputs.point.index, .data outputs.scalar.index] source.1 := by
  obtain ⟨point, scalar, result, pointRead, scalarRead, _, _⟩ := related
  rw [result]
  change (none = none ∧ none = none ∧ none = none ∧ none = none ∧
    (∃ actual, some point = some actual ∧
      (frame[outputs.point.index]?).bind (Domain.Value.decode (.vector "bls12-381.fr")) = some actual) ∧
    (∃ actual, some scalar = some actual ∧
      (frame[outputs.scalar.index]?).bind (Domain.Value.decode (.field "bls12-381.fr")) = some actual) ∧ True)
  simp [pointRead, scalarRead, Domain.Value.decode, Domain.Payload.value]

/-- These are local source resolution equations, not an assumed callback or
region equation. The selected service handle is compared by Routing.draw. -/
structure Routes (routing : Zkc.Construction.Original.Routing) (context : ProtocolContext)
    (frames : Zkc.Construction.Original.Frames) (handle : Nat) (origins : Origins) : Prop where
  mode : routing.mode = .validator
  low : routing.message frames (SumcheckVerifierLaws.lowSite context)
    (context.roles 0) routing.context.validator = some origins.low
  high : routing.message frames (SumcheckVerifierLaws.highSite context)
    (context.roles 0) routing.context.validator = some origins.high
  draw : routing.draw frames (SumcheckVerifierLaws.challengeSite context)
    "bls12-381.fr" handle = some origins.draw
  delivery : routing.message frames (SumcheckVerifierLaws.deliverySite context)
    routing.context.validator (context.roles 0) = some origins.delivery

/-- An ordinary process combinator for the exact ordered nominal operations.
It retains source optional ABI values and the reached construction state. -/
def verifier (routing : Zkc.Construction.Original.Routing) (context : ProtocolContext) (origins : Origins)
    (point : List F) (scalar : F) (state : Zkc.Construction.Original.State (uniformCarriers F G)) :
    PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
        Zkc.Construction.Original.State (uniformCarriers F G)) :=
  .call (.receive (.field "bls12-381.fr") (SumcheckVerifierLaws.lowSite context)
    (SumcheckVerifierLaws.lowSite context) (routing.context.role (context.roles 0))) fun low =>
  .call (.observe (.message origins.low (.field "bls12-381.fr" low))) fun _ =>
  .call (.receive (.field "bls12-381.fr") (SumcheckVerifierLaws.highSite context)
    (SumcheckVerifierLaws.highSite context) (routing.context.role (context.roles 0))) fun high =>
  .call (.observe (.message origins.high (.field "bls12-381.fr" high))) fun _ =>
  if scalar = low + high then
    (Zkc.Construction.Original.queryField { state with history := state.history ++
      [.message origins.low (.field "bls12-381.fr" low),
       .message origins.high (.field "bls12-381.fr" high)] }
      origins.draw "bls12-381.fr").bind fun (challenge, final) =>
    .call (.observe (.message origins.delivery (.field "bls12-381.fr" challenge))) fun _ =>
      .done (SumcheckVerifierLaws.embedV (some (point ++ [challenge]),
        some ((1 - challenge) * low + challenge * high)),
        { final with history := final.history ++
          [.message origins.delivery (.field "bls12-381.fr" challenge)] })
  else .halt .reject

set_option backward.isDefEq.respectTransparency false in
theorem original_round (payload : UnitPayload)
    (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (routing : Zkc.Construction.Original.Routing) (context : ProtocolContext)
    (separate : context.roles 0 ≠ context.roles 1)
    (index handle : Nat) (origins : Origins)
    (point : List F) (scalar : F) (state : Zkc.Construction.Original.State (uniformCarriers F G))
    (routes : Routes routing context state.frames handle origins) :
    Zkc.Construction.Original.fold routing
      (OriginalSumcheckLibrary.round payload context (context.roles 1)
        (.cons (some index) ((SumcheckVerifierLaws.embedV (some point, some scalar)).append
          (.cons (some handle) .nil)))) state =
      verifier routing context origins point scalar state := by
  rw [OriginalSumcheckLibrary.round_verifier payload bodies context (context.roles 1)
    rfl separate index (some handle) (some point) (some scalar), Zkc.Construction.Original.fold_bind, Zkc.Construction.Original.fold_actions]
  simp only [SumcheckVerifierLaws.roundPlain, PIR.Process.interpretState,
    Zkc.Construction.Original.operations, Zkc.Construction.Original.receive, Zkc.Construction.Original.send, Zkc.Construction.Original.query, routes.mode, routes.low, routes.high,
    routes.draw, routes.delivery, Zkc.Construction.Original.record, Domain.Payload.ofValue,
    PIR.Process.bind, PIR.Process.bind_assoc, verifier, List.append_assoc]
  congr 1
  funext low
  congr 1
  funext observedLow
  congr 1
  funext high
  congr 1
  funext observedHigh
  have request := Zkc.Construction.Original.Routing.draw_request routes.draw
  by_cases passed : scalar = low + high <;>
    simp only [passed, ite_true, ite_false, PIR.Process.interpretState,
      Zkc.Construction.Original.operations, Zkc.Construction.Original.query,
      Zkc.Construction.Original.send, routes.mode, routes.draw, routes.delivery,
      Zkc.Construction.Original.queryField, request, Zkc.Construction.Original.record,
      Domain.Payload.ofValue, PIR.Process.bind, Zkc.Construction.Original.fold,
      ↓reduceDIte, List.cons_append, List.nil_append]

end ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
