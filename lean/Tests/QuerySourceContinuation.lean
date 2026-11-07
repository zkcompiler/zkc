module

public import Zkc.Realization.QuerySourceContinuation
public import Zkc.Source.Structured.OracleProcessContinuation
public import Tests.OracleProcessData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QuerySourceContinuation
open Zkc.Source Zkc.Source.Structured Zkc.Realization
open Zkc.Realization.QuerySourceContinuation OracleProcessData

def source (captured : OracleAnchor) (position : Nat) :
    PIR.Process (oracleReadInterface model.toCarriers) (Values (Component model.Value) [.index]) :=
  checked.denote model (.cons (some captured) (.cons (some position) .nil))

def child (captured : OracleAnchor) (position ordinal : Nat) : OracleRead :=
  ⟨kind, captured, position, ⟨⟨1, []⟩, 1, [7, 1, ordinal]⟩, []⟩

/-- The checked source has two distinct occurrences of the same query. Its
first answer is unused, but still occupies a saved position and an access. -/
theorem source_body (captured : OracleAnchor) (position : Nat) :
    source captured position =
      .call (child captured position 0) (fun _ ↦
      .call (child captured position 1) (fun reply ↦
      .done (.cons (some reply) .nil))) := by
  kernel_rfl

def arenas : (kind : OracleKind) → List (model.Value kind.answer)
  | .table .index _ => ([10, 20] : List Nat)
  | _ => []

/-- The saved prefix recovers the second actual occurrence. The continuation
is obtained by consuming the first reply of the checked body. -/
def afterFirst (captured : OracleAnchor) (position : Nat) :
    Associated arenas (source captured position)
      (.call (child captured position 1) (fun reply ↦
        .done (.cons (some reply) .nil))) [0] := by
  have initial := initial arenas (source captured position)
  rw [source_body] at initial
  have advanced := initial.resume (slot := 0) (reply := (10 : Nat)) rfl
  simpa only [source_body, List.nil_append] using advanced

/-- Repeated equal-typed requests remain two ordered responses, even though
the result uses only the second one. No new mathematical premise is needed. -/
def completed (captured : OracleAnchor) (position : Nat) :
    Associated arenas (source captured position) (.done (.cons (some (20 : Nat)) .nil)) [0, 1] :=
  (afterFirst captured position).resume (slot := 1) (reply := (20 : Nat)) rfl

example (captured : OracleAnchor) (position : Nat) :
    (completed captured position).answers.kinds.length = 2 :=
  (completed captured position).width.symm

/-- A saved reply cannot redirect the remaining source request to a different
same-typed handle. This is a statement about any association proof, not merely
the particular proof constructed above. -/
theorem handle_swap_rejected (captured other : OracleAnchor) (position : Nat)
    (different : captured ≠ other) :
    IsEmpty (Associated arenas (source captured position)
      (.call (child other position 1) (fun reply ↦ .done (.cons (some reply) .nil))) [0]) := by
  constructor
  intro association
  obtain ⟨request, next, reply, first, residual, read⟩ := association.one
  rw [source_body] at first
  obtain ⟨sameRequest, sameNext⟩ := PIR.Process.call.inj first
  cases sameRequest
  cases sameNext
  have sameHandle := congrArg OracleRead.anchor (PIR.Process.call.inj residual).1
  exact different sameHandle.symm

/-- A stopped source has no returned child value to insert into a frame. -/
theorem stopped_reply_rejected :
    IsEmpty (Associated arenas (A := Unit) (.halt .refused) (.done ()) [0]) := by
  constructor
  intro association
  obtain ⟨request, next, reply, impossible, _⟩ := association.one
  cases impossible

/-- Restoring a saved continuation is exact before provider selection. The
cut uses the first actual source request; arbitrary child outcomes retain
their states and ordered event prefixes through the common sequencing law. -/
theorem source_cut {I : PIR.Signature} {S E : Type}
    (operations : (request : OracleRead) → S →
      PIR.Process I (PIR.Execution S E (model.Value request.kind.answer)))
    (captured : OracleAnchor) (position : Nat) (state : S) :
    OracleProcess.present operations (source captured position) state =
      (OracleProcess.present operations
        (.call (I := oracleReadInterface model.toCarriers)
          (child captured position 0) .done) state).bind (fun result ↦
          OracleProcess.sequence result (fun _ current ↦
            OracleProcess.present operations
              (.call (I := oracleReadInterface model.toCarriers)
                (child captured position 1) (fun reply ↦
                .done (.cons (some reply) .nil))) current)) := by
  rw [source_body]
  exact OracleProcess.present_bind (I := oracleReadInterface model.toCarriers) operations
    (.call (child captured position 0) .done) _ state

/-- A failed first child keeps its real poststate and event prefix; the
second occurrence is not evaluated. This is not a semantic success case. -/
theorem source_stopped {I : PIR.Signature} {S E : Type}
    (operations : (request : OracleRead) → S →
      PIR.Process I (PIR.Execution S E (model.Value request.kind.answer)))
    (captured : OracleAnchor) (position : Nat) (before after : S)
    (events : List E) (reason : PIR.Stop)
    (failed : operations (child captured position 0) before =
      .done ⟨.stopped reason, after, events⟩) :
    OracleProcess.present operations (source captured position) before =
      .done ⟨.stopped reason, after, events⟩ := by
  rw [source_body]
  simp only [OracleProcess.present, failed, PIR.Process.bind, OracleProcess.sequence]

#print axioms source_body
#print axioms afterFirst
#print axioms completed
#print axioms handle_swap_rejected
#print axioms stopped_reply_rejected
#print axioms source_cut
#print axioms source_stopped
end Tests.QuerySourceContinuation
