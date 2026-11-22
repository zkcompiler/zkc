module

public import ZkcFormal.ProcessJudgment
public import VCVio.OracleComp.ProbComp.Basic

@[expose] public section
namespace ZkcFormal.ProbabilisticProcess
open Zkc.Core

/-- Replies and state belong to the service. A missing reply can be distinguished from a
Core halt and from a successful return. -/
abbrev Service (S : Sig) (State : Type) :=
  (op : S.Op) → State → ProbComp (Option (S.Reply op) × State)

inductive Outcome (H A : Type) where
  | returned (a : A)
  | halted (h : H)
  | unavailable
  deriving DecidableEq

/-- Interpret the existing process traversal in VCVio. The state after a call, including
one without a reply, is part of the experiment's result. -/
def run {S : Sig} {H A State : Type} (service : Service S State)
    (p : Process S H A) : State → ProbComp (Outcome H A × State) :=
  let algebra : ProcessJudgment S (State → ProbComp (Outcome H A × State)) := {
    node := fun op next state ↦ do
      let (reply, state') ← service op state
      match reply with
      | none => pure (.unavailable, state')
      | some v => next v state' }
  p.interpret algebra (fun a s ↦ pure (.returned a,s)) (fun h s ↦ pure (.halted h,s))

/-- The type of the reply to the first effect of a process; a process that begins with none has
no reply. -/
def ReplyToFirst {S : Sig} {H A : Type} : Process S H A → Type
  | .call op _ => S.Reply op
  | .done _ | .halt _ => Empty

/-- What follows the reply to the first effect of a process. -/
def afterFirst {S : Sig} {H A : Type} (p : Process S H A) : ReplyToFirst p → Process S H A :=
  match p with
  | .call _ next => next
  | .done _ | .halt _ => nofun

end ZkcFormal.ProbabilisticProcess
