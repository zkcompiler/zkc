module

public import ZkcSecurity.Realizations.Sumcheck.OriginalRawComposition
public import ZkcSecurity.Realizations.Sumcheck.OriginalHonestReduce
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactRoot
public import ZkcSecurity.FiatShamir.HonestReadbackCompleteness
public import ZkcSecurity.Families.Sumcheck.TableComponentNominalLossless

@[expose] public section

/-! Installed laws used by structural security bindings. These are shared
family adapters, independent of any root name, source catalogue or ABI index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcExamples.Structured.SumcheckArtifacts
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev verifierCall (payload : UnitPayload) (maximum : Nat) (context : ProtocolContext)
    (scopes : List (List Nat)) (scalar : F) (count handle : Nat) :=
  (OriginalSumcheckLibrary.reduce (G := G) payload maximum context (context.roles 1) []
    (.cons none (.cons none (.cons none (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil))))))).bind
    fun result => .done (maskValues (context.roles 1) (context.mapScopes scopes) result)

theorem call_raw (payload : UnitPayload) (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (maximum : Nat) (context : Realizations.Sumcheck.Original.Context)
    (separate : context.protocol.roles 0 ≠ context.protocol.roles 1)
    (scopes : List (List Nat)) (count : Nat) (scalar : F) :
    verifierCall (G := G) payload maximum context.protocol scopes scalar count context.handle =
      if count ≤ maximum then
        (run (G := G) context (List.range count) ⟨[], scalar⟩).bind fun result =>
          .done (maskValues (context.protocol.roles 1) (context.protocol.mapScopes scopes) (output result))
      else .halt .refused := by
  unfold verifierCall
  have reduced := source_reduce (G := G) payload bodies maximum context separate [] count scalar
  change OriginalSumcheckLibrary.reduce payload maximum context.protocol (context.protocol.roles 1) []
    (.cons none (.cons none (.cons none (.cons (some scalar) (.cons (some count) (.cons (some context.handle) .nil)))))) = _ at reduced
  rw [reduced]
  split <;> simp only [PIR.Process.bind_assoc, PIR.Process.bind]

theorem honest_check (payload : UnitPayload) (bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions)
    (state : OriginalHonest.MathState F 0) (bounded : state.original.length < indexLimit)
    (pointBound : state.point.length < 64) :
    Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers (G := G) payload).closed
      SumcheckHelperBodies.checkHelper)
      (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) =
      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by
  rw [OriginalSumcheckLibrary.check_present payload bodies 1 state.original state.point state.scalar
    bounded (pointBound.trans (by decide +kernel))]
  have shape : PrimitiveLibrary.HasShape state.original state.point.length 1 := by
    simp only [PrimitiveLibrary.HasShape, Nat.mod_one, Nat.div_one]
    exact ⟨by decide, pointBound, trivial, by simpa only [Nat.zero_add] using state.shape⟩
  simp only [shape, true_and]
  rfl

abbrev RootResult := Values (Component (assignment F G)) [.boolean] × Original.State (uniformCarriers F G)

def RootPost (producer validator : RootResult (F := F) (G := G)) : Prop :=
  ∃ history, producer = (.cons none .nil, ⟨[], history⟩) ∧
    validator = (.cons (some true) .nil, ⟨[], history⟩)

def closedPost (reached : Domain.History (uniformCarriers F G))
    (result : Result (F := F) (G := G)) : Prop :=
  result.2.history = reached ∧ result.2.frames = []

def schedule (occurrence : ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding.Occurrence)
    (context : Zkc.Construction.Context) : Nominal.Schedule "bls12-381.fr" where
  low index := (occurrence.origins context index).low
  high index := (occurrence.origins context index).high
  query index := (occurrence.origins context index).draw
  delivery index := (occurrence.origins context index).delivery
  request _ := rfl

theorem routes (routing : Original.Routing)
    (occurrence : ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding.Occurrence) (handle : Nat)
    (checked : ∀ index, ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding.Routes routing occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩] handle
      (occurrence.origins routing.context index)) :
    OriginalSecurity.Routes routing ⟨occurrence.protocol, handle⟩ (schedule occurrence routing.context) [] := by
  exact ⟨(checked 0).mode, fun index => (checked index).low, fun index => (checked index).high,
    fun index => (checked index).draw, fun index => (checked index).delivery⟩

def ActualPost (context : Context) (producerRef producerArity booleanRef transcriptRef : Nat)
    (producer validator : Domain.Result (uniformCarriers F G)) : Prop :=
  ∃ a b, RootPost a b ∧ ArtifactRoot.ProducerReturns context producerRef producerArity a producer ∧
    ArtifactRoot.ValidatorReturns context booleanRef transcriptRef b validator

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem ActualPost.acceptance {context : Context} {producerRef producerArity booleanRef transcriptRef : Nat}
    {producer validator : Domain.Result (uniformCarriers F G)}
    (related : ActualPost context producerRef producerArity booleanRef transcriptRef producer validator) :
    Domain.acceptanceAt 0 validator.values = some true := by
  obtain ⟨a, b, ⟨history, rfl, rfl⟩, _, value, sourceEq, valuesEq, _⟩ := related
  have valueTrue : value = true := by
    simpa only [Values.cons.injEq, Option.some.injEq, and_true] using sourceEq.symm
  subst value
  rw [valuesEq]
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem root_acceptance {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) (context : Context)
    (booleanRef transcriptRef : Nat) (first : compiled.selection.position = 0)
    (source : Result (F := F) (G := G)) (actual : Domain.Result (uniformCarriers F G))
    (related : ArtifactRoot.ValidatorReturns context booleanRef transcriptRef source actual) :
    acceptance source = compiled.acceptance actual := by
  obtain ⟨value, sourceEq, actualEq, _, _, _⟩ := related
  simp only [acceptance, OriginalSecurity.acceptance, sourceEq,
    ZkcSecurity.Endpoint.Domain.Compiled.acceptance, first, actualEq, List.getElem?_cons_zero]

end ZkcSecurity.Realizations.Sumcheck.OriginalRoot
