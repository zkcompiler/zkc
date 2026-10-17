import Zkc.Source.Structured.OpenMeaning
import ZkcExamples.Structured.SumcheckVerifierProcess
import Mathlib.Data.ZMod.Basic

/-! Deterministic typed handlers shared by source controls. Reply scripts are
external inputs; all protocol work uses the existing participant interpreter. -/
namespace Tests.StructuredSumcheckVerifierSupport
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured.SumcheckVerifierLaws (lowSite highSite challengeSite deliverySite)

inductive Reply (F : Type) where
  | value (value : F)
  | consumedCount
  | ack
  | stop (reason : PIR.Stop)
  deriving DecidableEq, Repr

inductive Event (F : Type) where
  | receive (site : String) (peer : Nat) (value : F)
  | query (site : String) (handle : Nat) (value : F)
  | send (site : String) (peer : Nat) (value : F)
  | stop (site : String) (reason : PIR.Stop)
  deriving DecidableEq, Repr

structure State (F : Type) where
  replies : List (Reply F)
  consumed : Nat := 0
  deriving DecidableEq, Repr

variable {F : Type} [CommRing F] [DecidableEq F]

def scalarReply (site : String) (event : F → Event F) (state : State F) :
    PIR.Execution (State F) (Event F) F :=
  match state.replies with
  | .value value :: rest =>
      ⟨.returned value, ⟨rest, state.consumed + 1⟩, [event value]⟩
  | .consumedCount :: rest =>
      ⟨.returned state.consumed, ⟨rest, state.consumed + 1⟩, [event state.consumed]⟩
  | .stop reason :: rest =>
      ⟨.stopped reason, ⟨rest, state.consumed + 1⟩, [.stop site reason]⟩
  | [] => ⟨.stopped .incomplete, state, [.stop site .incomplete]⟩
  | .ack :: _ => ⟨.stopped .refused, state, [.stop site .refused]⟩

def handler : PIR.Handler (participantInterface F F) (State F) (Event F)
  | .receive (.field _) site peer, state => scalarReply site (.receive site peer) state
  | .query site _ (.cons handle .nil), state => scalarReply site (.query site handle) state
  | .send (ty := .field _) site peer value, state =>
      match state.replies with
      | .ack :: rest => ⟨.returned (), ⟨rest, state.consumed + 1⟩, [.send site peer value]⟩
      | .stop reason :: rest =>
          ⟨.stopped reason, ⟨rest, state.consumed + 1⟩,
            [.send site peer value, .stop site reason]⟩
      | _ => ⟨.stopped .incomplete, state, [.send site peer value, .stop site .incomplete]⟩
  | _, state => ⟨.stopped .refused, state, []⟩

def roundEvents (ctx : ProtocolContext) (handle : Nat) (lo hi cv : F) : List (Event F) :=
  [.receive (lowSite ctx) (ctx.roles 0) lo, .receive (highSite ctx) (ctx.roles 0) hi,
    .query (challengeSite ctx) handle cv, .send (deliverySite ctx) (ctx.roles 0) cv]

end Tests.StructuredSumcheckVerifierSupport
