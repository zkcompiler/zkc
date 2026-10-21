module

public import ZkcArkLib.Sumcheck.Multilinear.Causal
public import Zkc.Source.Structured.Participant

@[expose] public section


namespace ZkcSecurity.Examples.CausalSumcheck

open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open OracleComp OracleSpec Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear

variable {F G S E : Type} {I : PIR.Signature}
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Structured scalar domain; service values are the actual Nat handles. -/
abbrev scalar : Ty := .field scalarDomain
abbrev randomService : Ty := .service ("random." ++ scalarDomain ++ "/0")

abbrev queryAction (site : String) (service : Nat) : (participantInterface F G).Op :=
  .query site scalarDomain (.cons service .nil)

abbrev lowAction (site : String) : (participantInterface F G).Op := .receive scalar site 0

abbrev sendAction (site : String) (r : F) : (participantInterface F G).Op :=
  .send (ty := scalar) site 0 r

structure Sites where
  round : String := "round"
  low : String := "round.0"
  high : String := "round.1"
  guard : String := "guard"
  query : String := "challenge"
  delivery : String := "delivery"

variable (sites : SiteObservations I)
  (actions : PIR.OperationInterpretation (participantInterface F G) I)
  (tables : Evaluation.ComponentTables F G I)

/-- Existing operation semantics, including scalar ownership restriction.
The canonical fragment fixes root self 1, the identity ProtocolContext and an
empty ProtocolTable. Its operations have no protocol-region callbacks. -/
def receive (site : String) : PIR.Proc I F :=
  (protocolOperationWith sites actions tables 1 (.exchange scalar 0 1 site)
    (.cons none .nil) .nil [] {}).bind fun values =>
  (protocolOperationWith sites actions tables 1 (.restrict scalar [1]) values .nil [] {}).bind fun values =>
    match values.get .here with
    | some value => .done value
    | none => .halt .incomplete

/-- The query has an operand; a field/service name alone is not randomness. -/
def draw (site : String) (service : Nat) : PIR.Proc I F :=
  (protocolOperationWith sites actions tables 1 (.restrict randomService [1])
    (.cons (some service) .nil) .nil [] {}).bind fun serviceValues =>
  (protocolOperationWith sites actions tables 1 (.draw 1 scalarDomain site) serviceValues .nil [] {}).bind fun values =>
    match values.get .here with
    | some value => .done value
    | none => .halt .incomplete

def send (site : String) (r : F) : PIR.Proc I Unit :=
  (protocolOperationWith sites actions tables 1 (.exchange scalar 1 0 site)
    (.cons (some r) .nil) .nil [] {}).bind fun _ => .done ()

def mark (site : String) : PIR.Proc I Unit :=
  (protocolOperationWith sites actions tables 1 (.mark site) .nil .nil [] {}).bind fun _ => .done ()

/-- A canonical one-round fragment in the ONE existing Proc, not an imported
    Sumcheck body or a second source interpreter. Trusted tails are actual Proc. -/
def scalarRound (names : Sites) (service : Nat) (claim : F)
    (advance terminal : Message F → F → PIR.Proc I Unit) : PIR.Proc I (List F × F) :=
  (mark sites actions tables names.round).bind fun _ =>
  (receive sites actions tables names.low).bind fun lo =>
  (receive sites actions tables names.high).bind fun hi =>
  (protocolOperationWith sites actions tables 1 (.guard 1 names.guard)
    (.cons (some (decide (claim = lo + hi))) .nil) .nil [] {}).bind fun _ =>
  (mark sites actions tables names.query).bind fun _ =>
  (draw sites actions tables names.query service).bind fun r =>
  (mark sites actions tables names.delivery).bind fun _ =>
  (send sites actions tables names.delivery r).bind fun _ =>
  (advance (lo, hi) r).bind fun _ =>
  (terminal (lo, hi) r).bind fun _ => .done ([r], evaluate (lo, hi) r)

set_option backward.isDefEq.respectTransparency false in
theorem receive_eq (site : String) :
    receive sites actions tables site = actions (lowAction site) := by
  simp [receive, protocolOperationWith, Participant.exchange, Participant.restrict,
    PIR.Proc.interpret, PIR.Proc.bind, PIR.Proc.bind_assoc, PIR.Proc.bind_done,
    Values.get, lowAction]

set_option backward.isDefEq.respectTransparency false in
theorem draw_eq (site : String) (service : Nat) :
    draw sites actions tables site service = actions (queryAction site service) := by
  simp [draw, protocolOperationWith, Participant.query, Participant.restrict,
    RoleFamily.sequence, PIR.Proc.interpret, PIR.Proc.bind, PIR.Proc.bind_assoc,
    PIR.Proc.bind_done, Values.get, queryAction, services]

set_option backward.isDefEq.respectTransparency false in
theorem send_eq (site : String) (r : F) :
    send sites actions tables site r = (actions (sendAction site r)).bind (fun _ => .done ()) := by
  simp [send, protocolOperationWith, Participant.exchange, PIR.Proc.interpret,
    PIR.Proc.bind, PIR.Proc.bind_assoc, sendAction]

theorem mark_eq (site : String) : mark sites actions tables site = sites.mark site := by
  simp only [mark, protocolOperationWith, PIR.Proc.bind_assoc, PIR.Proc.bind]
  have unit_eta : (fun _ : Unit => (PIR.Proc.done () : PIR.Proc I Unit)) = PIR.Proc.done := by
    funext u; cases u; rfl
  rw [unit_eta, PIR.Proc.bind_done, qualify_root]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Scopes use root-local Nat roles P=0 and V=1; @V claim is absent at P. -/
theorem claim_scope (claim : F) :
    maskValues (Value := assignment F G) 0 [[1]] (.cons (some claim) (.nil : Values _ [])) =
      (.cons none .nil : Values (Component (assignment F G)) [scalar]) ∧
    maskValues (Value := assignment F G) 1 [[1]] (.cons (some claim) (.nil : Values _ [])) =
      (.cons (some claim) .nil : Values (Component (assignment F G)) [scalar]) := by
  simp [maskValues, Participant.restrict]

set_option backward.isDefEq.respectTransparency false in
/-- The actual guard is pure rejection. No runtime abort callback is required. -/
theorem guard_is_bare_stop (h : PIR.MonadHandler ProbComp I S E) (s : S) :
    (protocolOperationWith sites actions tables 1 (.guard 1 "guard")
      (.cons (some false) .nil) .nil [] {}).runM h s = pure ⟨.stopped .reject, s, []⟩ := by
  simp [protocolOperationWith, Participant.guard, PIR.Proc.interpret,
    PIR.Proc.bind, PIR.Proc.runM]

set_option backward.isDefEq.respectTransparency false in
theorem scalarRound_eq (names : Sites) (service : Nat) (claim : F)
    (advance terminal : Message F → F → PIR.Proc I Unit) :
    scalarRound sites actions tables names service claim advance terminal =
      (sites.mark names.round).bind (fun _ =>
      (actions (lowAction names.low)).bind (fun lo =>
      (actions (lowAction names.high)).bind (fun hi =>
        if boundary (lo, hi) = claim then
          (sites.mark names.query).bind (fun _ =>
          (actions (queryAction names.query service)).bind (fun r =>
          (sites.mark names.delivery).bind (fun _ =>
          (actions (sendAction names.delivery r)).bind (fun _ =>
          (advance (lo, hi) r).bind (fun _ =>
          (terminal (lo, hi) r).bind (fun _ => .done ([r], evaluate (lo, hi) r)))))))
        else .halt .reject))) := by
  simp only [scalarRound, mark_eq, receive_eq, draw_eq, send_eq]
  congr 1; funext u; congr 1; funext lo; congr 1; funext hi
  by_cases passed : lo + hi = claim
  · have cond : decide (claim = lo + hi) = true := decide_eq_true passed.symm
    simp [protocolOperationWith, Participant.guard, PIR.Proc.interpret,
      PIR.Proc.bind, PIR.Proc.bind_assoc, boundary, cond, ite_eq_left passed]
    rfl
  · have cond : decide (claim = lo + hi) = false := decide_eq_false (Ne.symm passed)
    simp [protocolOperationWith, Participant.guard, PIR.Proc.interpret,
      PIR.Proc.bind, PIR.Proc.bind_assoc, boundary, cond, ite_eq_right passed]

/-- V obtains the two distinct replies in order; HIGH sees LOW's residual state.
    This equation holds before imposing any sampling law. -/
theorem ordered_receives (low high : String) (h : PIR.MonadHandler ProbComp I S E) (s : S) :
    ((receive sites actions tables low).bind fun lo =>
      (receive sites actions tables high).bind fun hi => .done (lo, hi)).runM h s = (do
      let first ← (actions (lowAction low)).runM h s
      first.followM fun lo s => do
        let second ← (actions (lowAction high)).runM h s
        second.followM fun hi s => pure (result (lo, hi) s)) := by
  simp only [receive_eq, PIR.runM_bind]
  apply bind_congr; intro first
  apply congrArg (PIR.Execution.followM first)
  funext lo s
  rw [PIR.runM_bind]
  rfl

/-- Pure scalar source calculations have their exact typed operation meanings. -/
theorem boundary_calculation (lo hi : F) :
    protocolOperationWith sites actions tables 1 (.calculate (.fieldAdd scalarDomain) rfl)
      (.cons (some lo) (.cons (some hi) .nil)) .nil [] {} =
        .done (.cons (some (boundary (lo, hi))) .nil) := rfl


end ZkcSecurity.Examples.CausalSumcheck
