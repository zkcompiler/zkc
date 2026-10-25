module

public import ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
public import Zkc.Construction.OriginalCorrespondence

@[expose] public section

/-! Producer-side construction of the original Reduce callback. The delivery
route is checked against the original source and the fixed draw policy. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalProducer
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured
open ZkcSecurity.Realizations.Sumcheck.ArtifactBinding

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

structure Routes (routing : Original.Routing) (context : ProtocolContext)
    (frames : Original.Frames) (origins : Origins) : Prop where
  mode : routing.mode = .producer
  low : routing.message frames (SumcheckVerifierLaws.lowSite context)
    routing.context.producer (context.roles 1) = some origins.low
  high : routing.message frames (SumcheckVerifierLaws.highSite context)
    routing.context.producer (context.roles 1) = some origins.high
  delivery : routing.delivery frames (SumcheckVerifierLaws.deliverySite context)
    "bls12-381.fr" (context.roles 1) = some (origins.draw, origins.delivery)
  request : origins.draw.request = some (.draw "bls12-381.fr")

/-- The producer callback's four data outputs and transcript. These typed
coordinates are supplied by actual loop yields, separately from capture length. -/
structure Outputs (suite : String) where
  raw : OutputReference (.data (.vector "bls12-381.fr"))
  dimension : OutputReference (.data .index)
  width : OutputReference (.data .index)
  point : OutputReference (.data (.vector "bls12-381.fr"))
  transcript : OutputReference (.transcript suite)
  deriving DecidableEq, Repr

def Outputs.references {suite : String} (outputs : Outputs suite) : List Nat :=
  [outputs.raw.index, outputs.dimension.index, outputs.width.index,
    outputs.point.index, outputs.transcript.index]

def Outputs.sorts (suite : String) : List ValueSort :=
  [.data (.vector "bls12-381.fr"), .data .index, .data .index,
    .data (.vector "bls12-381.fr"), .transcript suite]

/-- Check all five actual loop yields against the complete producer ABI. -/
def Outputs.ofYields (suite : String) (yielded : List Nat)
    (sorts : List ValueSort) : Option (Outputs suite) :=
  match yielded with
  | [raw, dimension, width, point, transcript] =>
      if sorts = Outputs.sorts suite then
        some ⟨⟨raw⟩, ⟨dimension⟩, ⟨width⟩, ⟨point⟩, ⟨transcript⟩⟩ else none
  | _ => none

/-- The complete six-slot source ABI and all five physical carried values.
The relation also fixes the transcript suite, reached history and source frames.
It makes no claim about honest scalar agreement with a validator. -/
def Returns (context : Zkc.Construction.Context) (outputs : Outputs context.suite) (frames : Original.Frames)
    (source : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
      Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ raw dimension width point,
    source.1 = SumcheckProverLaws.embedP (raw, dimension, width, point) ∧
    frame[outputs.raw.index]? = some (.data (.vector "bls12-381.fr" raw)) ∧
    frame[outputs.dimension.index]? = some (.data (.index dimension)) ∧
    frame[outputs.width.index]? = some (.data (.index width)) ∧
    frame[outputs.point.index]? = some (.data (.vector "bls12-381.fr" point)) ∧
    frame[outputs.transcript.index]? = some (.transcript context.suite source.2.history) ∧
    source.2.frames = frames

/-- The callback return additionally fixes its mathematical state update.
This is needed to compose admitted rounds, since a mere ABI projection does
not establish that the next table still has the required shape. -/
def RoundReturns (context : Zkc.Construction.Context) (outputs : Outputs context.suite) (frames : Original.Frames)
    (raw : List F) (dimension width : Nat) (point : List F)
    (source : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
      Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  Returns context outputs frames source frame ∧
    ∃ challenge, source.1 = SumcheckProverLaws.embedP
      (Zkc.Polynomial.Multilinear.restrictValues raw challenge, dimension - 1, width,
        point ++ [challenge])

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem returns_abi (context : Zkc.Construction.Context) (outputs : Outputs context.suite) (frames : Original.Frames)
    (source : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
      Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G))
    (related : Returns context outputs frames source frame) :
    Original.ValuesHolds frame
      [.data outputs.raw.index, .data outputs.dimension.index, .data outputs.width.index,
        .data outputs.point.index, .absent, .absent] source.1 := by
  obtain ⟨raw, dimension, width, point, output, rawRead, dimensionRead, widthRead, pointRead, _, _⟩ := related
  rw [output]
  change ((∃ actual, some raw = some actual ∧
      (frame[outputs.raw.index]?).bind (Domain.Value.decode (.vector "bls12-381.fr")) = some actual) ∧
    (∃ actual, some dimension = some actual ∧
      (frame[outputs.dimension.index]?).bind (Domain.Value.decode .index) = some actual) ∧
    (∃ actual, some width = some actual ∧
      (frame[outputs.width.index]?).bind (Domain.Value.decode .index) = some actual) ∧
    (∃ actual, some point = some actual ∧
      (frame[outputs.point.index]?).bind (Domain.Value.decode (.vector "bls12-381.fr")) = some actual) ∧
    none = none ∧ none = none ∧ True)
  simp [rawRead, dimensionRead, widthRead, pointRead, Domain.Value.decode, Domain.Payload.value]

def producer (routing : Original.Routing) (context : ProtocolContext) (origins : Origins)
    (raw : List F) (dimension width : Nat) (point : List F)
    (state : Original.State (uniformCarriers F G)) :
    PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
        Original.State (uniformCarriers F G)) :=
  let low := (raw.take (raw.length / 2)).sum
  let high := (raw.drop (raw.length / 2)).sum
  .call (.send (SumcheckVerifierLaws.lowSite context) (SumcheckVerifierLaws.lowSite context)
    (routing.context.role (context.roles 1)) (.field "bls12-381.fr" low)) fun _ =>
  .call (.observe (.message origins.low (.field "bls12-381.fr" low))) fun _ =>
  .call (.send (SumcheckVerifierLaws.highSite context) (SumcheckVerifierLaws.highSite context)
    (routing.context.role (context.roles 1)) (.field "bls12-381.fr" high)) fun _ =>
  .call (.observe (.message origins.high (.field "bls12-381.fr" high))) fun _ =>
  (Original.queryField { state with history := state.history ++
    [.message origins.low (.field "bls12-381.fr" low),
     .message origins.high (.field "bls12-381.fr" high)] }
    origins.draw "bls12-381.fr").bind fun (challenge, final) =>
  .call (.observe (.message origins.delivery (.field "bls12-381.fr" challenge))) fun _ =>
    .done (SumcheckProverLaws.embedP
      (Zkc.Polynomial.Multilinear.restrictValues raw challenge, dimension - 1, width,
        point ++ [challenge]),
      { final with history := final.history ++
        [.message origins.delivery (.field "bls12-381.fr" challenge)] })

set_option backward.isDefEq.respectTransparency false in
/-- This equation comes from the shared original callback, at its producer
role. Shape assumptions justify its actual sums and restriction helpers. -/
theorem original_round (payload : UnitPayload)
    (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (routing : Original.Routing) (context : ProtocolContext)
    (separate : context.roles 1 ≠ context.roles 0)
    (index : Nat) (service : Option Nat) (origins : Origins)
    (raw : List F) (dimension width : Nat) (point : List F)
    (shape : PrimitiveLibrary.HasShape raw dimension width)
    (bounded : raw.length < indexLimit) (positive : 0 < dimension)
    (state : Original.State (uniformCarriers F G))
    (routes : Routes routing context state.frames origins) :
    Original.fold routing
      (OriginalSumcheckLibrary.round payload context (context.roles 0)
        (.cons (some index) ((SumcheckProverLaws.embedP (raw, dimension, width, point)).append
          (.cons service .nil)))) state =
      producer routing context origins raw dimension width point state := by
  rw [OriginalSumcheckLibrary.round_producer payload bodies context (context.roles 0)
    rfl separate index service (raw, dimension, width, point) shape bounded positive,
    Original.fold_bind, Original.fold_actions]
  simp only [SumcheckProverLaws.roundPresent, PIR.Process.interpretState,
    Original.operations, Original.send, Original.receive, routes.mode, routes.low, routes.high,
    routes.delivery, Original.record, Domain.Payload.ofValue, Original.queryField, routes.request,
    PIR.Process.bind, PIR.Process.bind_assoc, Original.fold, producer, ↓reduceDIte,
    List.append_assoc, List.cons_append, List.nil_append]

end ZkcSecurity.Realizations.Sumcheck.OriginalProducer
