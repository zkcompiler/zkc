module

public import ZkcSecurity.Realizations.Sumcheck.OriginalComponent
public import Zkc.Protocols.Sumcheck.Source.Checks
public import Zkc.Protocols.Sumcheck.Source.Reduce

@[expose] public section

/-! A shape-free state for the original verifier callback. The raw table is
only inspected by the root's terminal helper. Neither this state nor the
Reduce equation requires an honest table, claim, or callback reply. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open SumcheckVerifierBodies

structure State (F : Type) where
  point : List F
  scalar : F

variable {F G : Type} [Field F] [DecidableEq F]

def advance (state : State F) (low high challenge : F) : State F :=
  ⟨state.point ++ [challenge], (1 - challenge) * low + challenge * high⟩

def embedded (state : State F) : Values (Component (assignment F G)) repeatState :=
  SumcheckVerifierLaws.embedV (some state.point, some state.scalar)

/-- All six original optional output slots, in the source return order. -/
def output (state : State F) : Values (Component (assignment F G)) reduceOutputs :=
  reduceReturnValues (embedded state)

noncomputable def step (context : Realizations.Sumcheck.Original.Context) (index : Nat)
    (state : State F) : PIR.Process (OriginalSumcheckLibrary.signature (F := F) (G := G)) (State F) :=
  .call (.enter ⟨Realizations.Sumcheck.Original.loopSite context, index⟩) fun _ =>
  .call (.action (.receive (.field "bls12-381.fr")
    (SumcheckVerifierLaws.lowSite context.protocol) (context.protocol.roles 0))) fun low =>
  .call (.action (.receive (.field "bls12-381.fr")
    (SumcheckVerifierLaws.highSite context.protocol) (context.protocol.roles 0))) fun high =>
  if state.scalar = low + high then
    .call (.action (.query (SumcheckVerifierLaws.challengeSite context.protocol)
      "bls12-381.fr" (.cons context.handle .nil))) fun challenge =>
    .call (.action (.send (ty := .field "bls12-381.fr")
      (SumcheckVerifierLaws.deliverySite context.protocol) (context.protocol.roles 0) challenge)) fun _ =>
    .call (.leave ⟨Realizations.Sumcheck.Original.loopSite context, index⟩) fun _ =>
    .done (advance state low high challenge)
  else .halt .reject

noncomputable def run (context : Realizations.Sumcheck.Original.Context) :
    List Nat → State F → PIR.Process (OriginalSumcheckLibrary.signature (F := F) (G := G)) (State F)
  | [], state => .done state
  | index :: rest, state => (step context index state).bind (run context rest)

variable [AddCommGroup G] [Module F G] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem source_step (payload : UnitPayload) (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (context : Realizations.Sumcheck.Original.Context)
    (separate : context.protocol.roles 0 ≠ context.protocol.roles 1)
    (maximum index : Nat) (state : State F) :
    (step (G := G) context index state).bind (fun result => .done (embedded result)) =
      Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) context.protocol
        (context.protocol.roles 1) (.cons (some context.handle) .nil)
        (OriginalSumcheckLibrary.round payload context.protocol (context.protocol.roles 1))
        (embedded state) index Occurrence.iterations SumcheckVerifierBodies.repeatSite := by
  unfold Repeat.stepOn embedded
  rw [SumcheckVerifierLaws.mask_embedV context.protocol (context.protocol.roles 1) rfl maximum]
  rw [OriginalSumcheckLibrary.round_verifier payload bodies context.protocol
    (context.protocol.roles 1) rfl separate]
  simp only [step, SumcheckVerifierLaws.roundPlain, OriginalSumcheckLibrary.actions,
    Occurrence.actions, PIR.Process.interpret, PIR.Process.bind, PIR.Process.bind_assoc,
    Structured.IterationObservations.within_eq, Occurrence.iterations,
    Structured.IterationObservations.enter, Structured.IterationObservations.leave,
    Realizations.Sumcheck.Original.loopSite]
  congr 1
  funext entered
  congr 1
  funext low
  congr 1
  funext high
  by_cases passed : state.scalar = low + high
  · simp only [ite_eq_left passed, PIR.Process.bind, PIR.Process.interpret,
      Occurrence.actions]
    congr 1
    funext challenge
    congr 1
    funext sent
    congr 1
    funext left
    exact congrArg PIR.Process.done
      (SumcheckVerifierLaws.mask_embedV context.protocol (context.protocol.roles 1) rfl maximum _).symm
  · simp only [passed, ite_false, PIR.Process.bind, PIR.Process.interpret]

theorem source_loop (payload : UnitPayload) (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (context : Realizations.Sumcheck.Original.Context)
    (separate : context.protocol.roles 0 ≠ context.protocol.roles 1)
    (maximum : Nat) (indices : List Nat) (state : State F) :
    (run (G := G) context indices state).bind (fun result => .done (embedded result)) =
      Finite.fold (fun carried index =>
        Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) context.protocol
          (context.protocol.roles 1) (.cons (some context.handle) .nil)
          (OriginalSumcheckLibrary.round payload context.protocol (context.protocol.roles 1))
          carried index Occurrence.iterations SumcheckVerifierBodies.repeatSite) indices (embedded state) := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
    simp only [run, Finite.fold, ← source_step payload bodies context separate maximum,
      PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind (step context index state))
    funext next
    exact ih next

/-- Complete original Reduce equation, including its actual count refusal.
Shape and vector capacity are not premises: Reduce does not inspect the table. -/
theorem source_reduce (payload : UnitPayload) (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (claims : SumcheckPendingLaws.Bodies payload.definitions)
    (maximum : Nat) (context : Realizations.Sumcheck.Original.Context)
    (separate : context.protocol.roles 0 ≠ context.protocol.roles 1)
    (protocols : ProtocolTable (assignment F G) (OriginalSumcheckLibrary.signature (F := F) (G := G)))
    (count : Nat) (point : List F) (scalar : F) :
    OriginalSumcheckLibrary.reduce payload maximum context.protocol (context.protocol.roles 1)
      protocols (OriginalSumcheckLibrary.verifierInputs (some point) (some scalar) (some count) (some context.handle)) =
      if count ≤ maximum then
        (run (G := G) context (List.range count) ⟨point, scalar⟩).bind (fun result => .done (output result))
      else .halt .refused := by
  unfold OriginalSumcheckLibrary.verifierInputs
  rw [OriginalSumcheckLibrary.reduce_verifier payload bodies maximum context.protocol separate]
  rw [SumcheckPendingLaws.identity_owned payload _ claims.openClaim, ite_eq_left rfl]
  dsimp only [PIR.Process.bind, Values.get]
  have active : ((repeatSpec maximum).roles.map context.protocol.roles).contains
      (context.protocol.roles 1) = true := by
    simp only [List.map_cons, List.map_nil, List.contains_cons,
      List.contains_nil, beq_self_eq_true, Bool.true_or, Bool.or_true]
  simp only [denoteRepeatOn, active, ↓reduceIte]
  by_cases bound : count ≤ maximum
  · simp only [bound, ite_true]
    rw [SumcheckVerifierLaws.mask_embedV context.protocol (context.protocol.roles 1) rfl maximum]
    have loop := source_loop (F := F) (G := G) payload bodies context separate maximum
      (List.range count) ⟨point, scalar⟩
    change (Finite.fold _ (List.range count) (embedded (G := G) ⟨point, scalar⟩)).bind _ = _
    rw [← loop]
    simp only [output, PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext result
    exact OriginalSumcheckLibrary.return_verifier payload claims context.protocol result.point result.scalar
  · simp only [bound, ite_false, PIR.Process.bind]

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
