module

public import ZkcArkLibExamples.CausalSumcheck.ExactRound

@[expose] public section


namespace ZkcSecurity.Examples.CausalSumcheck

open OracleComp OracleSpec
open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear Zkc.Polynomial.Multilinear
open scoped ENNReal

variable {F G S E : Type} {I : PIR.Signature}
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- An explicitly retained, elaboration-checked body using the actual primitive.
This is a hand-built control, not the imported library helper. -/
def appendBody : Region dialect [.vector scalarDomain, scalar] [.vector scalarDomain] :=
  .letOp (.exec (.vectorAppend scalarDomain))
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

def appendDefinition : CheckedDefinition :=
  ⟨"example.append", .local, _, _, appendBody.erase, appendBody, appendBody.elaborate_erase⟩

variable (sites : SiteObservations I)
  (actions : PIR.OperationInterpretation (participantInterface F G) I)

def valueTables : Evaluation.ComponentTables F G I :=
  Evaluation.ComponentTables.extend sites ⟨[], []⟩ appendDefinition

/-- Extract the actual returned component; absence stops. -/
def takeComponent {ty : Ty} (values : Values (Component (assignment F G)) [ty]) :
    PIR.Process I (assignment F G ty) :=
  match values.get .here with
  | some value => .done value
  | none => .halt .incomplete

def guardValue (claim lo hi : F) : PIR.Process I Bool :=
  (protocolOperationWith sites actions (valueTables sites) 1
    (.calculate (.fieldAdd scalarDomain) rfl) (.cons (some lo) (.cons (some hi) .nil)) .nil [] {}).bind fun values =>
  (takeComponent values).bind fun sum =>
  (protocolOperationWith sites actions (valueTables sites) 1
    (.calculate (.fieldEqual scalarDomain) rfl)
    (.cons (some claim) (.cons (some sum) .nil)) .nil [] {}).bind takeComponent

def nextClaim (lo hi r : F) : PIR.Process I F :=
  (protocolOperationWith sites actions (valueTables sites) 1
    (.calculate (.fieldConstant scalarDomain 1) rfl) .nil .nil [] {}).bind fun values =>
  (takeComponent values).bind fun one =>
  (protocolOperationWith sites actions (valueTables sites) 1
    (.calculate (.fieldSubtract scalarDomain) rfl)
    (.cons (some one) (.cons (some r) .nil)) .nil [] {}).bind fun values =>
  (takeComponent values).bind fun complement =>
  (protocolOperationWith sites actions (valueTables sites) 1
    (.calculate (.fieldMultiply scalarDomain) rfl)
    (.cons (some complement) (.cons (some lo) .nil)) .nil [] {}).bind fun values =>
  (takeComponent values).bind fun left =>
  (protocolOperationWith sites actions (valueTables sites) 1
    (.calculate (.fieldMultiply scalarDomain) rfl)
    (.cons (some r) (.cons (some hi) .nil)) .nil [] {}).bind fun values =>
  (takeComponent values).bind fun right =>
  (protocolOperationWith sites actions (valueTables sites) 1
    (.calculate (.fieldAdd scalarDomain) rfl)
    (.cons (some left) (.cons (some right) .nil)) .nil [] {}).bind takeComponent

def appendPoint (point : List F) (r : F) : PIR.Process I (List F) :=
  (protocolOperationWith sites actions (valueTables sites) 1
    (.localCall appendDefinition.helper rfl 1 "append")
    (.cons (some point) (.cons (some r) .nil)) .nil [] {}).bind takeComponent

theorem guardValue_eq (claim lo hi : F) :
    guardValue sites actions claim lo hi = .done (decide (claim = lo + hi)) := rfl

theorem nextClaim_eq (lo hi r : F) :
    nextClaim sites actions lo hi r = .done (evaluate (lo, hi) r) := by
  change PIR.Process.done ((((1 : Nat) : F) - r) * lo + r * hi) = _
  simp only [Nat.cast_one]
  rfl

theorem appendPoint_eq (point : List F) (r : F) :
    appendPoint sites actions point r = .done (point ++ [r]) := by
  rfl

/-- Value-returning trusted calculation in source order: append then arithmetic. -/
def calculatedUpdate (point : List F) (pair : Message F) (r : F) : PIR.Process I (List F × F) :=
  (appendPoint sites actions point r).bind fun point =>
  (nextClaim sites actions pair.1 pair.2 r).bind fun claim => .done (point, claim)

theorem calculatedUpdate_eq (point : List F) (pair : Message F) (r : F) :
    calculatedUpdate sites actions point pair r = .done (point ++ [r], evaluate pair r) := by
  simp only [calculatedUpdate, appendPoint_eq, nextClaim_eq, PIR.Process.bind]

/-- Contextual execution equation, so later work consumes the actual values. -/
theorem calculatedUpdate_runM_bind {A : Type} (h : PIR.MonadHandler ProbComp I S E)
    (point : List F) (pair : Message F) (r : F)
    (next : (List F × F) → PIR.Process I A) (s : S) :
    ((calculatedUpdate sites actions point pair r).bind next).runM h s =
      (next (point ++ [r], evaluate pair r)).runM h s := by
  apply (runM_bind_transport h _ next
    (fun s => pure (result (point ++ [r], evaluate pair r) s))
    (fun pc => (next pc).runM h) (fun _ => by rw [calculatedUpdate_eq]; rfl)
    (fun _ _ => rfl) s).trans
  simp only [pure_bind, follow_result]

/-- Canonical structured fragment with actual value flow through calculations.
Advance may stop before append; terminal work receives the computed point/claim. -/
def calculatedRound (names : Sites) (service : Nat) (claim : F)
    (advance : Message F → F → PIR.Process I Unit)
    (terminal : List F → F → PIR.Process I Unit) : PIR.Process I (List F × F) :=
  (mark sites actions (valueTables sites) names.round).bind fun _ =>
  (receive sites actions (valueTables sites) names.low).bind fun lo =>
  (receive sites actions (valueTables sites) names.high).bind fun hi =>
  (guardValue sites actions claim lo hi).bind fun condition =>
  (protocolOperationWith sites actions (valueTables sites) 1 (.guard 1 names.guard)
    (.cons (some condition) .nil) .nil [] {}).bind fun _ =>
  (mark sites actions (valueTables sites) names.query).bind fun _ =>
  (draw sites actions (valueTables sites) names.query service).bind fun r =>
  (mark sites actions (valueTables sites) names.delivery).bind fun _ =>
  (send sites actions (valueTables sites) names.delivery r).bind fun _ =>
  (advance (lo, hi) r).bind fun _ =>
  (calculatedUpdate sites actions [] (lo, hi) r).bind fun pc =>
  (terminal pc.1 pc.2).bind fun _ => .done pc

theorem calculatedRound_eq (names : Sites) (service : Nat) (claim : F)
    (advance : Message F → F → PIR.Process I Unit)
    (terminal : List F → F → PIR.Process I Unit) :
    calculatedRound sites actions names service claim advance terminal =
      scalarRound sites actions (valueTables sites) names service claim advance
        (fun pair r => terminal [r] (evaluate pair r)) := by
  simp only [calculatedRound, guardValue_eq, calculatedUpdate_eq, 
    PIR.Process.bind, List.nil_append, scalarRound]


end ZkcSecurity.Examples.CausalSumcheck
