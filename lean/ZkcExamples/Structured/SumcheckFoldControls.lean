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
that observes a slot hidden from the prover, a wrongly typed slot, an unknown
repeat or a misplaced iteration index is refused by name. -/
namespace ZkcExamples.Structured.SumcheckFoldControls
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical PrimitiveLibrary
open SumcheckVerifierBodies SumcheckVerifierLaws SumcheckProverLaws SumcheckFoldInvariant
open SumcheckHonestExecution
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear (PartialEvaluation)

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

/-- The completed point's value is the original extension at the tape prefix. -/
theorem source_value : (restrictPrefixValues raw [2, 3]).sum = 3 := by decide

/-! ### The actual loop reaches the honest frame -/

/-- Acknowledge sends and answer receives in order; every other action refuses. -/
def deliveries : PIR.Handler (participantInterface F F) (List F) Unit
  | .send .., replies => ⟨.returned (), replies, []⟩
  | .receive (.field _) _ _, r :: rest => ⟨.returned r, rest, []⟩
  | _, replies => ⟨.stopped .refused, replies, []⟩

/-- The actual prover loop of the Source unit, delivering the challenges 2 and 3. -/
theorem loop_reaches_honest_frame :
    ((Repeat.loop (repeatSpec 2) SumcheckSourceVerifier.childContext 0 (cap none)
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

/-! ### A wrong invariant fails -/

/-- The same atoms read least-significant coordinate first: the received point
is reversed before the partial evaluation. Only this meaning changes. -/
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

/-! ### Exported frame refusals -/

/-- The verifier's local role cannot observe the prover's point slot. -/
theorem verifier_role_refused :
    checkFrame (Value := assignment F F) resolution (repeats 2) (tableContext 2)
      { frameExport 2 with role := 1 } = .error (.carriedMismatch 3 1) := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, frameExport, partialIdentity,
    vocabulary, repeats, decode_first_binder, bind, Except.bind, pure, Except.pure]
  rfl

/-- The verifier's own point slot is hidden from the prover. -/
theorem hidden_slot_refused :
    checkFrame (Value := assignment F F) resolution (repeats 2) (tableContext 2)
      ⟨"s15", 0, [⟨partialIdentity 2, [.binder 0, .carried 4, .carried 0]⟩]⟩ =
      .error (.carriedMismatch 4 0) := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, partialIdentity,
    vocabulary, repeats, decode_first_binder, bind, Except.bind, pure, Except.pure]
  rfl

/-- The scalar claim slot is not a vector. -/
theorem wrong_type_refused :
    checkFrame (Value := assignment F F) resolution (repeats 2) (tableContext 2)
      ⟨"s15", 0, [⟨partialIdentity 2, [.binder 0, .carried 5, .carried 0]⟩]⟩ =
      .error (.carriedMismatch 5 0) := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, partialIdentity,
    vocabulary, repeats, decode_first_binder, bind, Except.bind, pure, Except.pure]
  rfl

/-- A site naming no repeat occurrence is refused before any atom. -/
theorem unknown_repeat_refused :
    checkFrame (Value := assignment F F) resolution (repeats 2) (tableContext 2)
      { frameExport 2 with site := "s16" } = .error (.unknownRepeat "s16") := by
  simp [checkFrame, repeats]

/-- The iteration index is not a vector. -/
theorem iteration_refused :
    checkFrame (Value := assignment F F) resolution (repeats 2) (tableContext 2)
      ⟨"s15", 0, [⟨partialIdentity 2, [.binder 0, .iteration, .carried 0]⟩]⟩ =
      .error .iterationMismatch := by
  simp [checkFrame, checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, partialIdentity,
    vocabulary, repeats, bind, Except.bind, pure, Except.pure]
  rfl

end ZkcExamples.Structured.SumcheckFoldControls
