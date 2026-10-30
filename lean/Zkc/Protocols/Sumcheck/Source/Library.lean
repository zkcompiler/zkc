module

public import Zkc.Protocols.Sumcheck.Source.VerifierLaws
public import Zkc.Protocols.Sumcheck.Source.ProverLaws
public import Zkc.Source.Structured.Occurrence

@[expose] public section

/-! Source-level Sumcheck laws with the actual iteration observations retained.
The helper tables are folds of the admitted declarations. No constructed
instruction pattern or artifact supplies a body or a helper law here. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace ZkcExamples.Structured.OriginalSumcheckLibrary
open Zkc.Source Zkc.Source.Structured
open SumcheckVerifierBodies SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev signature := Occurrence.signature (uniformCarriers F G)

abbrev actions : PIR.OperationInterpretation (participantInterface F G) (signature (F := F) (G := G)) :=
  Occurrence.actions (carriers := uniformCarriers F G)

def helpers (payload : UnitPayload) : Evaluation.ComponentTables F G (signature (F := F) (G := G)) :=
  payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩

theorem helpers_on (payload : UnitPayload) :
    (helpers (F := F) (G := G) payload).toOn =
      payload.definitions.foldl
        (Evaluation.ComponentTablesOn.extend (ringModel F G) (.silent _)) ⟨[], []⟩ :=
  Evaluation.ComponentTables.fold_toOn (.silent _) payload.definitions ⟨[], []⟩

theorem helpers_lift (payload : UnitPayload) :
    Evaluation.ComponentTables.Interprets actions
      (plainHelpers (F := F) (G := G) payload) (helpers payload) :=
  Evaluation.ComponentTables.fold_interpret actions
    (SiteObservations.silent_interpret _) (.empty _) payload.definitions

def round (payload : UnitPayload) (context : ProtocolContext) (self : Nat) :
    RegionFunction (Component (assignment F G)) (signature (F := F) (G := G))
      (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"]), repeatState) :=
  fun args => roundBody.denote
    (participantMeaningWith (.silent _) actions (helpers payload) self [] context) args.get

/-- This body has no nested protocol application or repeat. Its lifted equation
is independent of the caller's captured protocol table and iteration handler. -/
theorem round_lift (payload : UnitPayload) (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G))
      (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"]))) :
    (SumcheckVerifierLaws.bodyFn payload context self args).interpret actions =
      round payload context self args := by
  change (roundBody.denote
    (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload)
      self [] context) args.get).interpret actions = _
  exact participant_denote_interpret actions (SiteObservations.silent_interpret _)
    (fun _ => by simp only [participantActions, PIR.Process.interpret, PIR.Process.bind_done])
    (helpers_lift payload) self roundBody args.get (.empty _) context

/-- The callback is literally the callback of the occurrence-aware nominal
source interpreter, for any captured protocol prefix. -/
theorem round_on (payload : UnitPayload) (context : ProtocolContext) (self : Nat)
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G)))
    (iterations : IterationObservations (signature (F := F) (G := G)))
    (args : Values (Component (assignment F G))
      (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"]))) :
    roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions
      (helpers payload).toOn self protocols context iterations) args.get =
      round payload context self args := by
  change roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions
    (helpers payload).toOn self [] context) args.get = _
  exact (denote_participantMeaningWith_eq (.silent _) actions (helpers payload) self [] context
    roundBody args.get).symm

/-- Arbitrary optional state and every typed reply, including all source stops. -/
theorem round_verifier (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (context : ProtocolContext) (self : Nat) (role : self = context.roles 1)
    (separate : context.roles 0 ≠ self) (index : Nat) (service : Option Nat)
    (point : Option (List F)) (claim : Option F) :
    round payload context self (.cons (some index)
      ((SumcheckVerifierLaws.embedV (G := G) (point, claim)).append (.cons service .nil))) =
      ((SumcheckVerifierLaws.roundPlain context service (point, claim)).interpret actions).bind
        (fun result => .done (SumcheckVerifierLaws.embedV result)) := by
  rw [← round_lift]
  simpa only [SumcheckVerifierLaws.cap, PIR.Process.interpret_bind, PIR.Process.interpret] using
    congrArg (PIR.Process.interpret actions)
      (SumcheckVerifierLaws.round_body_optional (F := F) (G := G) payload bodies context self
        role separate index service (point, claim))

/-- Producer correspondence is a different theorem. The shape and bounded
indices justify the actual sums and restriction helpers, not a security claim. -/
theorem round_producer (payload : UnitPayload) (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (context : ProtocolContext) (self : Nat) (role : self = context.roles 0)
    (separate : context.roles 1 ≠ self) (index : Nat) (service : Option Nat)
    (state : SumcheckProverLaws.ProverState F)
    (shape : PrimitiveLibrary.HasShape state.1 state.2.1 state.2.2.1)
    (bound : state.1.length < indexLimit) (positive : 0 < state.2.1) :
    round payload context self (.cons (some index)
      ((SumcheckProverLaws.embedP (G := G) state).append (.cons service .nil))) =
      ((SumcheckProverLaws.roundPresent context state).interpret actions).bind
        (fun result => .done (SumcheckProverLaws.embedP result)) := by
  rw [← round_lift]
  simpa only [SumcheckVerifierLaws.cap, PIR.Process.interpret_bind, PIR.Process.interpret] using
    congrArg (PIR.Process.interpret actions)
      (SumcheckProverLaws.round_body_present (F := F) (G := G) payload bodies context self
        role separate index service state shape bound positive)

end ZkcExamples.Structured.OriginalSumcheckLibrary
