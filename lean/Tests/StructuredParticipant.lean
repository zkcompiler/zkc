import Zkc.Source.Structured.ClosedProjection

/-! Handbuilt controls of the actual protocol operation and region meanings.
These are process equations over arbitrary scalar/module values, not admission,
native execution, availability soundness, or cryptographic security results. -/

set_option autoImplicit false
namespace Tests.StructuredParticipant
open Zkc.Source Zkc.Source.Structured

private abbrev scalar : Ty := .field "bls12-381.fr"

private def helper {inputs outputs : List Ty} (name : String) (kind : HelperKind)
    (body : Region dialect inputs outputs) : CheckedDefinition :=
  ⟨name, kind, inputs, outputs, body.erase, body, body.elaborate_erase⟩

private def root {inputs outputs : List Ty} (inputScopes outputScopes : List (List Nat))
    (body : Region protocolDialect inputs outputs) : CheckedProtocol :=
  ⟨"control", ["owner", "receiver"], inputs, outputs, inputScopes, outputScopes,
    body.erase, body, body.elaborate_erase⟩

private def first : CheckedDefinition :=
  helper "first" .math (.ret (.cons .here .nil) : Region dialect [scalar, scalar] [scalar])

private def relay : CheckedDefinition :=
  helper "relay" .math (.letOp (.invoke first.helper)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)) :
      Region dialect [scalar, scalar] [scalar])

private def constant : CheckedDefinition :=
  helper "constant" .math (.letOp (.fieldConstant "bls12-381.fr" 7) .nil .nil
    (.ret (.cons .here .nil)) : Region dialect [scalar, scalar] [scalar])

private def stopping : CheckedDefinition :=
  helper "stopping" .local (.letOp (.mark "inside-local") .nil .nil (.stop .abort) :
    Region dialect [] [])

private def strictFirst : CheckedDefinition :=
  helper "strictFirst" .local (.ret (.cons .here .nil) : Region dialect [scalar, scalar] [scalar])

variable (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private def tables : OpenTables F G :=
  [first, relay, constant, stopping, strictFirst].foldl
    (Evaluation.ComponentTables.extend (observedSites F G)) ⟨[], []⟩

private def firstRoot : CheckedProtocol :=
  root (inputs := [scalar, scalar]) [[0, 1], [0, 1]] [[0, 1]]
    (.letOp (.calculate (.invoke relay.helper) (by decide +kernel))
      (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))

/-- Optional inputs pass through two named Math closures on the actual root. -/
theorem optional_first (x y : Option F) :
    firstRoot.participant (tables F G) 0 (.cons x (.cons y .nil)) =
      .done (.cons x .nil) := rfl

theorem missing_unused (x : F) :
    firstRoot.participant (tables F G) 0 (.cons (some x) (.cons none .nil)) =
      .done (.cons (some x) .nil) := rfl

theorem missing_needed (y : F) :
    firstRoot.participant (tables F G) 0 (.cons none (.cons (some y) .nil)) =
      .done (.cons none .nil) := rfl

/-- The reusable full-table law proves the same helper result without unfolding
any concrete table or knowing either helper's position in the declaration list. -/
theorem optional_first_full_table (payload : UnitPayload)
    (firstMember : first ∈ payload.definitions) (relayMember : relay ∈ payload.definitions)
    (x y : Option F) :
    invoke (payload.tables F G).components relay.helper (.cons x (.cons y .nil)) =
      .done (.cons x .nil) := by
  have firstEquation : invoke (payload.tables F G).components first.helper
      (.cons x (.cons y .nil)) = .done (.cons x .nil) :=
    payload.component_invoke_body first firstMember _
  apply (payload.component_invoke_body (F := F) (G := G) relay relayMember
    (.cons x (.cons y .nil))).trans
  change (invoke (payload.tables F G).components first.helper
    (.cons x (.cons y .nil))).bind _ = _
  rw [firstEquation]
  rfl

private def constantRoot : CheckedProtocol :=
  root (inputs := [scalar, scalar]) [[0], [0]] [[0]]
    (.letOp (.calculate (.invoke constant.helper) (by decide +kernel))
      (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))

theorem constant_absent_inputs :
    constantRoot.participant (tables F G) 0 (.cons none (.cons none .nil)) =
      .done (.cons (some (7 : F)) .nil) := rfl

private def separateRoot : CheckedProtocol :=
  root [[0, 1], [0, 1]] [[0], [1]]
    (.ret (.cons .here (.cons (.there .here) .nil)) :
      Region protocolDialect [scalar, scalar] [scalar, scalar])

theorem separate_results_owner (x y : Option F) :
    separateRoot.participant (tables F G) 0 (.cons x (.cons y .nil)) =
      .done (.cons x (.cons none .nil)) := rfl

theorem separate_results_receiver (x y : Option F) :
    separateRoot.participant (tables F G) 1 (.cons x (.cons y .nil)) =
      .done (.cons none (.cons y .nil)) := rfl

private def selectRoot : CheckedProtocol :=
  root [[0], [0, 1]] [[0, 1]]
    (.letOp (.calculate (.select scalar) (by decide +kernel))
      (.cons .here (.cons (.there .here) (.cons (.there .here) .nil))) .nil
      (.ret (.cons .here .nil)) : Region protocolDialect [.boolean, scalar] [scalar])

/-- Even equal public arms cannot recover the private condition after masking. -/
theorem strict_select_private_condition (condition : Bool) (x : F) :
    selectRoot.participant (tables F G) 1 (.cons (some condition) (.cons (some x) .nil)) =
      .done (.cons none .nil) := rfl

private def maskedRoot : CheckedProtocol :=
  root [[0]] [[0, 1]] (.ret (.cons .here .nil) : Region protocolDialect [scalar] [scalar])

theorem input_mask_precedes_work (x : F) :
    maskedRoot.participant (tables F G) 1 (.cons (some x) .nil) =
      .done (.cons none .nil) := rfl

private def stoppingRoot : CheckedProtocol :=
  root [] [] (.letOp (.localCall stopping.helper rfl 0 "local-call") .nil .nil
    (.ret .nil) : Region protocolDialect [] [])

/-- The zero-result Local body retains its mark and aborts for its owner. -/
theorem owner_local_observed :
    stoppingRoot.observed (tables F G) 0 .nil =
      .call (.mark "inside-local") (fun _ => .halt .abort) := rfl

theorem owner_local_abort :
    stoppingRoot.participant (tables F G) 0 .nil = .halt .abort := rfl

theorem nonowner_local_skips :
    stoppingRoot.observed (tables F G) 1 .nil = .done .nil := rfl

private def strictLocalRoot : CheckedProtocol :=
  root (inputs := [scalar, scalar]) [[0], [0]] [[0]]
    (.letOp (.localCall strictFirst.helper rfl 0 "strict-local")
      (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))

theorem owner_requires_unused_local_argument (x : F) :
    strictLocalRoot.participant (tables F G) 0 (.cons (some x) (.cons none .nil)) =
      .halt .incomplete := rfl

private def receiveRoot : CheckedProtocol :=
  root (inputs := [scalar]) [[0, 1]] [[0, 1]]
    (.letOp (.exchange scalar 0 1 "receive") (.cons .here .nil) .nil
      (.ret (.cons .here .nil)))

/-- The returned value is the independent reply, irrespective of the local copy. -/
theorem receiver_ignores_local_copy (localCopy : Option F) :
    receiveRoot.participant (tables F G) 1 (.cons localCopy .nil) =
      .call (.receive scalar "receive" 0)
        (fun received => .done (.cons (some received) .nil)) := rfl

private def guardRoot : CheckedProtocol :=
  root (inputs := [.boolean]) [[0]] [] (.letOp (.guard 0 "guard") (.cons .here .nil) .nil (.ret .nil))

theorem guard_owner_missing :
    guardRoot.participant (tables F G) 0 (.cons none .nil) = .halt .incomplete := rfl

theorem guard_owner_false :
    guardRoot.participant (tables F G) 0 (.cons (some false) .nil) = .halt .reject := rfl

theorem guard_owner_true :
    guardRoot.participant (tables F G) 0 (.cons (some true) .nil) = .done .nil := rfl

theorem guard_nonowner_skips (condition : Option Bool) :
    guardRoot.participant (tables F G) 1 (.cons condition .nil) = .done .nil := rfl

private def hiddenReceiveRoot : CheckedProtocol :=
  root (inputs := [scalar]) [[0, 1]] [[0]]
    (.letOp (.exchange scalar 0 1 "hidden-receive") (.cons .here .nil) .nil
      (.ret (.cons .here .nil)))

/-- Hiding the result leaves the receive action in the process. -/
theorem output_filter_after_receive (localCopy : Option F) :
    hiddenReceiveRoot.participant (tables F G) 1 (.cons localCopy .nil) =
      .call (.receive scalar "hidden-receive" 0) (fun _ => .done (.cons none .nil)) := rfl

private def hiddenStopRoot : CheckedProtocol :=
  root [[0]] [[1]] (.letOp (.localCall stopping.helper rfl 0 "hidden-stop") .nil .nil
    (.ret (.cons .here .nil)) : Region protocolDialect [scalar] [scalar])

/-- Output filtering cannot discard a prior zero-result Local stop. -/
theorem output_filter_preserves_stop (x : Option F) :
    hiddenStopRoot.participant (tables F G) 0 (.cons x .nil) = .halt .abort := rfl

private def projectionSnapshot : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [],
    [.function ⟨"main", .protocol, .privateDef, [.boolean], [],
      some ⟨["P"], [["P"]], []⟩, [], none,
      .block [.instruction (.guard "P") [0] [] [] "checked-guard"] (.ret [])⟩]⟩

private def checkedProjection : ClosedProgram :=
  (closedImportedOfIsOk projectionSnapshot (by decide +kernel)).program

/-- A concrete whole-unit admission supplies the syntactic projection witness. -/
theorem checked_projection_exact :
    ClosedProjection checkedProjection.subject.payload.entry.body checkedProjection.projectedBody :=
  checkedProjection.root_projection

set_option maxHeartbeats 1000000 in
/-- The general bridge applies to the actual checked subject, including marks. -/
theorem checked_observed_projection (condition : Bool) :
    checkedProjection.subject.observed F G 0 (.cons (some condition) .nil) =
      (checkedProjection.projectedBody.denote
        (Evaluation.meaning (observedSites F G)
          (checkedProjection.subject.payload.tables F G).closed)
        (Values.cons condition .nil).get).bind fun results => .done results.present :=
  checkedProjection.observed_projected (.cons condition .nil)

set_option maxHeartbeats 1000000 in
theorem checked_observed_reject :
    checkedProjection.subject.observed F G 0 (.cons (some false) .nil) =
      .call (.mark "checked-guard") (fun _ => .halt .reject) := rfl

set_option maxHeartbeats 1000000 in
theorem checked_participant_projection (condition : Bool) :
    checkedProjection.subject.participant F G 0 (.cons (some condition) .nil) =
      ((checkedProjection.projectedBody.denote
        (Evaluation.meaning (observedSites F G)
          (checkedProjection.subject.payload.tables F G).closed)
        (Values.cons condition .nil).get).interpret forgetSites).bind
        fun results => .done results.present :=
  checkedProjection.participant_projected (.cons condition .nil)


set_option maxHeartbeats 1000000 in
/-- The checked closed denotation now shares exactly the participant value family. -/
theorem checked_closed_denote (condition : Bool) :
    checkedProjection.subject.participant F G 0 (.cons (some condition) .nil) =
      ((checkedProjection.denote F G
        (checkedProjection.closedInputs (.cons condition .nil))).interpret closedLift).bind
        fun results => .done (checkedProjection.subjectOutputs results).present :=
  checkedProjection.participant_eq_denote (.cons condition .nil)

end Tests.StructuredParticipant
