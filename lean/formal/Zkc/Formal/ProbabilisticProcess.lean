module

public import Zkc.Formal.ProcessJudgment
public import VCVio.OracleComp.ProbComp.Basic

@[expose] public section
namespace Zkc.Formal.ProbabilisticProcess
open Core

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

end Zkc.Formal.ProbabilisticProcess
