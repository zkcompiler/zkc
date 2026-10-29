module

public import Zkc.Source.Structured.DomainProtocolLinking
public import Zkc.Source.Structured.PlainHelpers

@[expose] public section

/-! Transport of mathematical helper and callback laws to the occurrence view.
The helpers are the actual admitted declaration fold, for every payload. The
callback law retains arbitrary effects and replies; iteration observations are
silent on both sides. A client with observed nested loops must use the loop
presentation rules instead of erasing those boundaries. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OccurrencePresentation

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Effect interpretation commutes with the complete helper table, including
captured declaration prefixes and optional component inputs. -/
theorem helpers_interpret (payload : UnitPayload) :
    Evaluation.ComponentTablesOn.Interprets (model := ringModel F G) Occurrence.actions
      (plainHelpers (F := F) (G := G) payload).toOn
      (Occurrence.helpers (ringModel F G) payload) := by
  unfold plainHelpers Occurrence.helpers
  rw [Evaluation.ComponentTables.fold_toOn]
  exact Evaluation.ComponentTablesOn.fold_interpret _ (SiteObservations.silent_interpret _)
    (.empty _) _

/-- Reuse a closed helper law without writing an occurrence-specific copy. -/
theorem closed_helper (payload : UnitPayload) (helper : Helper)
    (args : Values (assignment F G) helper.inputs) :
    invoke (Occurrence.helpers (ringModel F G) payload).closed helper args =
      (invoke (plainHelpers (F := F) (G := G) payload).closed helper args).interpret
        Occurrence.actions :=
  ((helpers_interpret payload).closed helper args).symm

/-- Callback naturality is independent of the protocol, role and input layout.
It applies directly to callbacks whose actual body has no observed nested
iteration or protocol call. The empty callee table and silent iteration mode
are explicit, so this theorem cannot silently discard either effect. -/
theorem callback (payload : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    {inputs outputs : List Ty} (body : Region protocolDialect inputs outputs)
    (args : Values (Component (assignment F G)) inputs) :
    body.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      (Occurrence.helpers (ringModel F G) payload) self [] ctx .silent) args.get =
    (body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers payload) self [] ctx) args.get).interpret Occurrence.actions := by
  rw [denote_participantMeaningWith_eq]
  symm
  exact participant_denoteOn_interpret _ (SiteObservations.silent_interpret _)
    (fun _ => by rfl) (helpers_interpret payload) self body args.get (.empty _) ctx
    (by constructor <;> intros <;> rfl)

/-- A callback that cannot observe a callee table or iteration policy. This is
checked on every operation of the complete typed body, including subregions. -/
def contextFree : ProtocolOp → Bool
  | .protocolApply .. | .«repeat» .. => false
  | _ => true

/-- Unused protocol tables and iteration observations may change only when
all operations in the actual body satisfy the structural check. -/
theorem context_free (model : DomainModel) {I : PIR.Signature}
    (sites : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (helpers : Evaluation.ComponentTablesOn model.toCarriers I) (self : Nat)
    (left right : ProtocolTable model.Value I) (ctx : ProtocolContext)
    (leftIterations rightIterations : IterationObservations I)
    {inputs outputs : List Ty} (body : Region protocolDialect inputs outputs)
    (checked : body.erase.operations.all contextFree = true) :
    body.denote (participantMeaningWithOn model sites actions helpers self left ctx leftIterations) =
      body.denote (participantMeaningWithOn model sites actions helpers self right ctx rightIterations) := by
  apply Region.denote_congr
  intro op member
  have allowed := List.all_eq_true.mp checked op member
  funext args callbacks
  cases op with
  | protocolApply | «repeat» => simp [contextFree] at allowed
  | calculate | localCall | draw | statement => rfl
  | guard | exchange | restrict =>
    cases args with | cons value rest => cases rest; rfl
  | mark => cases args; rfl

/-- A complete structural check lets a local callback reuse its mathematical
presentation under the actual occurrence tables. No iteration or callee effect
can disappear: either constructor makes the check false. -/
theorem local_callback (payload : UnitPayload) (ctx : ProtocolContext) (self : Nat)
    {inputs outputs : List Ty} (body : Region protocolDialect inputs outputs)
    (checked : body.erase.operations.all contextFree = true)
    (left : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
    (right : ProtocolTable (assignment F G) (participantInterface F G))
    (args : Values (Component (assignment F G)) inputs) :
    body.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      (Occurrence.helpers (ringModel F G) payload) self left ctx Occurrence.iterations) args.get =
    (body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers payload) self right ctx) args.get).interpret Occurrence.actions := by
  rw [context_free (ringModel F G) _ _ _ self left [] ctx Occurrence.iterations .silent body checked]
  rw [denote_participantMeaningWith_eq,
    context_free (ringModel F G) _ _ _ self right [] ctx .silent .silent body checked]
  exact (callback payload ctx self body args).trans
    (congrArg (PIR.Process.interpret Occurrence.actions)
      (denote_participantMeaningWith_eq _ _ _ _ _ _ body args.get))

end Zkc.Source.Structured.OccurrencePresentation
