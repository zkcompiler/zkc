module

public import ZkcExamples.Structured.SumcheckFoldInvariant
public import ZkcExamples.Structured.SumcheckHonestExecution
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Controls for the fold invariant and honest completeness over `ZMod 5`.

A concrete two-variable table satisfies every premise of the completeness and
fold theorems. The actual prover loop reaches the honest frame of the received
challenges, where the invariant holds under the library meaning and fails under
a least-significant-first reading of the same atoms. Exported frame metadata
that observes a slot outside the observed role's scope, a wrongly typed slot, an
unknown repeat, a role outside the repeat or a misplaced iteration index is
refused with the matching reason. -/
namespace ZkcExamples.Structured.SumcheckFoldControls
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical PrimitiveLibrary
open SumcheckVerifierBodies SumcheckVerifierLaws SumcheckProverLaws SumcheckFoldInvariant
open SumcheckHonestExecution
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear (PartialEvaluation roundEndpoint)

abbrev F := ZMod 5

/-- MSB-first table `f(0,0)=0, f(0,1)=1, f(1,0)=2, f(1,1)=4`. -/
def raw : List F := [0, 1, 2, 4]

def table : Table F 2 := (ofList? 2 raw).get (by decide)

theorem raw_shape : HasShape raw 2 1 := by decide

theorem raw_bound : raw.length < indexLimit := by decide +kernel

theorem raw_decoded : ofList? 2 raw = some table := (Option.some_get _).symm

/-! ### Premise satisfiability -/

/-- Every premise of `source_complete` holds for this table and tape. -/
theorem source_complete_instance :
    (SumcheckSourceViews.program.participant F F 1
        (SumcheckSourceVerifier.sourceRootInputs (some raw) (some raw.sum) (some 2) (some 7))).run
      (network SumcheckSourceVerifier.childContext)
      ⟨SumcheckSourceViews.program.participant F F 0
        (SumcheckSourceVerifier.sourceRootInputs (some raw) (some raw.sum) (some 2) (some 7)),
        [2, 3]⟩ =
      ⟨.returned (.cons (some true) .nil), ⟨.done (.cons none .nil), []⟩, []⟩ :=
  source_complete raw 2 raw_shape raw_bound (Nat.le_refl _) 7 [2, 3] (by decide)

/-- Every premise of `reduction_complete` holds, with one of two rounds. -/
theorem reduction_complete_instance :
    (SumcheckReduceViews.program.participant F F 1
        (SumcheckReduceVerifier.reduceRootInputs (some raw) (some 2) (some raw.sum)
          (some 1) (some 7))).run
      (network reductionChild)
      ⟨SumcheckReduceViews.program.participant F F 0
        (SumcheckReduceVerifier.reduceRootInputs (some raw) (some 2) (some raw.sum)
          (some 1) (some 7)), [2, 3]⟩ =
      ⟨.returned (SumcheckReduceVerifier.reduceRootResults
          (some [2], some (restrictPrefixValues raw [2]).sum)),
        ⟨.done (SumcheckProverRoots.reductionResults raw [2]), [3]⟩, []⟩ :=
  reduction_complete raw 2 1 raw_shape raw_bound (by decide) (by decide) 7 [2, 3] (by decide)

/-- The folded value at the complete point `(2, 3)` is the original extension there. -/
theorem source_value :
    (restrictPrefixValues raw [2, 3]).sum = 3 ∧ extension 2 table (coordinates 2 [2, 3]) = 3 := by
  decide

/-- The residual request holds on the honest Reduction run with one of two rounds. -/
theorem reduction_residual_instance :
    SumcheckContractBindings.Residual 1 1 table [2] (restrictPrefixValues raw [2]).sum ∧
      ofList? 1 (restrictPrefixValues raw [2]) = some (fixPrefix 1 table (coordinates 1 [2])) :=
  (reduction_complete_residual (G := F) 1 1 raw table raw_decoded raw_shape raw_bound (by decide) 7
    [2, 3] (by decide)).2

/-! ### The actual loop reaches the honest frame -/

/-- Acknowledge sends and answer receives in order; every other action refuses. -/
def deliveries : PIR.Handler (participantInterface F F) (List F) Unit
  | .send .., replies => ⟨.returned (), replies, []⟩
  | .receive (.field _) _ _, r :: rest => ⟨.returned r, rest, []⟩
  | _, replies => ⟨.stopped .refused, replies, []⟩

/-- The actual prover loop of the Source unit, delivering the challenges 2 and 3. -/
theorem loop_reaches_honest_frame :
    ((Repeat.loop (repeatSpec SumcheckSourceNormalForms.reduceMaximum) SumcheckSourceVerifier.childContext 0 (cap none)
        (bodyFn SumcheckSourceViews.unit SumcheckSourceVerifier.childContext 0) 0 2
        (embedP (G := F) (honestState raw 2 []))).run deliveries [2, 3]).outcome =
      .returned (embedP (honestState raw 2 [2, 3])) := by
  rw [loop_honest SumcheckSourceViews.unit SumcheckSourceContracts.bodies
    SumcheckSourceVerifier.childContext 0 rfl (by decide) 2 none raw 2 raw_shape raw_bound 0 2 []]
  rfl

/-- The invariant holds at that frame under the library meaning. -/
theorem invariant_holds_at_reached_frame :
    Holds (G := F) 2 table 2 (embedP (honestState raw 2 [2, 3])) :=
  holds_honest raw 2 table raw_decoded [2, 3] (by decide)

/-- The same run with its received challenges recorded as the phase. -/
abbrev recordedRun :=
  (Repeat.loop (repeatSpec SumcheckSourceNormalForms.reduceMaximum) SumcheckSourceVerifier.childContext 0 (cap none)
    (bodyFn SumcheckSourceViews.unit SumcheckSourceVerifier.childContext 0) 0 2
    (embedP (G := F) (honestState raw 2 []))).run
    (PIR.ExecutionPath.handler (receivedChallenges (F := F) (G := F) SumcheckSourceVerifier.childContext)
      deliveries) ([], [2, 3])

theorem recorded_outcome : recordedRun.outcome = .returned (embedP (honestState raw 2 [2, 3])) := by
  unfold recordedRun
  rw [loop_honest SumcheckSourceViews.unit SumcheckSourceContracts.bodies
    SumcheckSourceVerifier.childContext 0 rfl (by decide) 2 none raw 2 raw_shape raw_bound 0 2 []]
  rfl

theorem recorded_challenges : recordedRun.state.1 = [2, 3] := by
  unfold recordedRun
  rw [loop_honest SumcheckSourceViews.unit SumcheckSourceContracts.bodies
    SumcheckSourceVerifier.childContext 0 rfl (by decide) 2 none raw 2 raw_shape raw_bound 0 2 []]
  rfl

/-- `source_frames` itself, applied to the frame this run actually reaches: it is
the honest state of the challenges the run delivered, and every atom holds. -/
theorem source_frames_at_reached_frame :
    HonestFrame raw 2 2 [2, 3] (embedP (G := F) (honestState raw 2 [2, 3])) ∧
      Holds (G := F) 2 table 2 (embedP (honestState raw 2 [2, 3])) := by
  have reached := PIR.Boundary.actual_return
    (receivedChallenges (F := F) (G := F) SumcheckSourceVerifier.childContext) _ deliveries _ [] [2, 3]
    (source_frames raw 2 raw_shape raw_bound table raw_decoded 2) _ recorded_outcome
  rw [recorded_challenges] at reached
  exact reached

/-- The round messages from the initial frame are the endpoints of the correct
round polynomial: `f(0,0)+f(0,1) = 1` and `f(1,0)+f(1,1) = 6 = 1`. -/
theorem first_round_messages :
    Repeat.step (repeatSpec SumcheckSourceNormalForms.reduceMaximum) SumcheckSourceVerifier.childContext 0 (cap none)
        (bodyFn SumcheckSourceViews.unit SumcheckSourceVerifier.childContext 0)
        (embedP (G := F) (honestState raw 2 [])) 0 =
      .call (.send (ty := .field "bls12-381.fr") (lowSite SumcheckSourceVerifier.childContext)
        (SumcheckSourceVerifier.childContext.roles 1) (roundEndpoint table [] 0)) (fun _ =>
      .call (.send (ty := .field "bls12-381.fr") (highSite SumcheckSourceVerifier.childContext)
        (SumcheckSourceVerifier.childContext.roles 1) (roundEndpoint table [] 1)) fun _ =>
      .call (.receive (.field "bls12-381.fr") (deliverySite SumcheckSourceVerifier.childContext)
        (SumcheckSourceVerifier.childContext.roles 1)) fun (cp : F) =>
      .done (embedP (honestState raw 2 ([] ++ [cp])))) ∧
      roundEndpoint table [] 0 = 1 ∧ roundEndpoint table [] 1 = 1 :=
  ⟨prover_messages SumcheckSourceViews.unit SumcheckSourceContracts.bodies
      SumcheckSourceVerifier.childContext 0 rfl (by decide) 2 none raw 2 raw_shape raw_bound table
      raw_decoded [] (by decide) 0, by decide, by decide⟩

/-- Past the table's dimension the actual step stops at the halves of a
zero-dimensional table, before any send. -/
theorem step_past_dimension_rejects :
    Repeat.step (repeatSpec SumcheckSourceNormalForms.reduceMaximum) SumcheckSourceVerifier.childContext 0 (cap none)
        (bodyFn SumcheckSourceViews.unit SumcheckSourceVerifier.childContext 0)
        (embedP (G := F) (honestState raw 2 [2, 3])) 2 = .halt .reject := by
  rw [step_honest SumcheckSourceViews.unit SumcheckSourceContracts.bodies
    SumcheckSourceVerifier.childContext 0 rfl (by decide) 2 none raw 2 raw_shape raw_bound [2, 3] 2]
  rfl

/-! ### A wrong invariant fails -/

/-- The same atoms with the received point reversed before the partial
evaluation; at a complete point this is the least-significant-first reading.
Only this meaning changes. -/
def reversedInterpretation : Interpretation vocabulary (assignment F F) :=
  { interpretation F F with
    holds := fun predicate arguments => match predicate, arguments with
      | .partialEvaluation _, .cons table (.cons point (.cons entries .nil)) =>
        PartialEvaluation table point.reverse entries
      | predicate, arguments => (interpretation F F).holds predicate arguments }

/-- At the frame the actual loop reaches, the least-significant-first reading of
the invariant is false: the folded entry is the original extension at `(2, 3)`,
not at `(3, 2)`. -/
theorem reversed_invariant_fails :
    ¬ (proverInvariant (F := F) (G := F) 2).Holds reversedInterpretation indexValue
      (tableBinders 2 table) ⟨2, embedP (honestState raw 2 [2, 3])⟩ := by
  intro holds
  obtain ⟨_, read, partialHolds⟩ := holds _ (List.mem_cons_self ..)
  cases read
  have complete := Zkc.Protocols.Sumcheck.Multilinear.partialEvaluation_complete table _ _
    partialHolds (by decide)
  exact absurd complete (by decide)

/-! ### Exported frame refusals

Each refusal is checked against the actual Source body's repeat occurrences. -/

abbrev sourceRepeats := repeatAt SumcheckSourceViews.reduceDefinition.raw.operations

open SumcheckRoundNormalForms (proverEntriesPosition proverDimensionPosition proverPointPosition
  verifierPointPosition)

/-- The verifier's local role cannot observe the prover's point slot (scope). -/
theorem verifier_role_refused :
    checkFrame (Value := assignment F F) resolution sourceRepeats (tableContext 2)
      { frameExport 2 with role := 1 } = .error (.slotScope proverPointPosition 1) := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, frameExport, partialIdentity,
    vocabulary, bind, Except.bind, pure, Except.pure]
  rfl

/-- The verifier's own point slot is hidden from the prover (scope). -/
theorem hidden_slot_refused :
    checkFrame (Value := assignment F F) resolution sourceRepeats (tableContext 2)
      ⟨"s15", 0, [⟨partialIdentity 2,
        [.binder 0, .carried verifierPointPosition, .carried proverEntriesPosition]⟩]⟩ =
      .error (.slotScope verifierPointPosition 0) := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, partialIdentity,
    vocabulary, bind, Except.bind, pure, Except.pure]
  rfl

/-- The prover's own dimension slot is an index, not a point vector (type). -/
theorem wrong_type_refused :
    checkFrame (Value := assignment F F) resolution sourceRepeats (tableContext 2)
      ⟨"s15", 0, [⟨partialIdentity 2,
        [.binder 0, .carried proverDimensionPosition, .carried proverEntriesPosition]⟩]⟩ =
      .error (.slotType proverDimensionPosition) := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, partialIdentity,
    vocabulary, bind, Except.bind, pure, Except.pure]
  rfl

/-- A site naming no repeat occurrence of the actual body is refused before any atom. -/
theorem unknown_repeat_refused :
    checkFrame (Value := assignment F F) resolution sourceRepeats (tableContext 2)
      { frameExport 2 with site := "s16" } = .error (.unknownRepeat "s16") := by
  simp only [checkFrame]
  rfl

/-- A role outside the repeat's roster is refused, even for atoms reading no slot. -/
theorem unknown_role_refused :
    checkFrame (Value := assignment F F) resolution sourceRepeats (tableContext 2)
      ⟨"s15", 2, [⟨widthIdentity, [.iteration]⟩]⟩ = .error (.unknownRole 2) := by
  simp only [checkFrame]
  rfl

/-- The iteration index is not a vector. -/
theorem iteration_refused :
    checkFrame (Value := assignment F F) resolution sourceRepeats (tableContext 2)
      ⟨"s15", 0, [⟨partialIdentity 2, [.binder 0, .iteration, .carried proverEntriesPosition]⟩]⟩ =
      .error .iterationMismatch := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, partialIdentity,
    vocabulary, bind, Except.bind, pure, Except.pure]
  rfl

end ZkcExamples.Structured.SumcheckFoldControls
