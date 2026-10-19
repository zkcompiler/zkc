import TestsSecurity.LocalCoupling

/-! Two small typed Region clients instantiate the same local coupling theorem.
The arithmetic uses bits only; no Schnorr or Sumcheck security is asserted. -/
namespace TestsSecurity.LocalCouplingClients

open OracleComp OracleComp.ProgramLogic.Relational
open Zkc.Source ZkcSecurity.VCVio.Coupling
open TestsSecurity.LocalCoupling

inductive Op where
  | receive (site : Nat)
  | draw (site : String) (handle : Nat)
  | send
  | guard
  | check
  | update

abbrev dialect : Dialect where
  Ty := Unit
  Op := Op
  arguments
    | .receive _ | .draw _ _ => []
    | .send => [()]
    | .guard => [(), ()]
    | .check | .update => [(), (), ()]
  results
    | .send | .guard => []
    | _ => [()]
  regions _ := []

def meaning : RegionMeaning dialect interface where
  Value _ := Bit
  operation
    | .receive site, .nil, .nil =>
        .call (.receive site) fun r => .done (.cons r .nil)
    | .draw site handle, .nil, .nil =>
        .call (.draw site handle) fun r => .done (.cons r .nil)
    | .send, .cons r .nil, .nil => .call (.send r) fun _ => .done .nil
    | .guard, .cons low (.cons high .nil), .nil =>
        if low ≠ high then .done .nil else .halt .reject
    | .check, .cons response (.cons challenge (.cons commitment .nil)), .nil =>
        .done (.cons (if response = commitment + challenge then 1 else 0) .nil)
    | .update, .cons challenge (.cons high (.cons low .nil)), .nil =>
        .done (.cons (low + challenge * (high - low)) .nil)

/-- Receive commitment; draw/send challenge; receive response; check. -/
def schnorr : Region dialect [] [()] :=
  .letOp (.receive 0) .nil .nil <|
  .letOp (.draw "challenge" 7) .nil .nil <|
  .letOp .send (.cons .here .nil) .nil <|
  .letOp (.receive 1) .nil .nil <|
  .letOp .check (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    .nil <| .ret (.cons .here .nil)

/-- LOW then HIGH (shared state), guard, draw/send, interpolate. -/
def sumcheck : Region dialect [] [()] :=
  .letOp (.receive 0) .nil .nil <|
  .letOp (.receive 1) .nil .nil <|
  .letOp .guard (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.draw "challenge" 7) .nil .nil <|
  .letOp .send (.cons .here .nil) .nil <|
  .letOp .update (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    .nil <| .ret (.cons .here .nil)

def empty : Environment meaning.Value [] := fun v => nomatch v

theorem schnorr_coupling (selective : Bool) (s : Nat) (flag : Bool) :
    RelTriple ((schnorr.denote meaning empty).runM (handler selective) s)
      ((schnorr.denote meaning empty).runM (representedHandler selective) ⟨s, flag⟩)
      (PIR.Related stateRelated (fun e => [e]) observe) :=
  runM_relTriple stateRelated _ _ _ _ (representation_action_law selective) _ _ _ rfl

theorem sumcheck_coupling (selective : Bool) (s : Nat) (flag : Bool) :
    RelTriple ((sumcheck.denote meaning empty).runM (handler selective) s)
      ((sumcheck.denote meaning empty).runM (representedHandler selective) ⟨s, flag⟩)
      (PIR.Related stateRelated (fun e => [e]) observe) :=
  runM_relTriple stateRelated _ _ _ _ (representation_action_law selective) _ _ _ rfl

/-- Lexical bind also keeps the zero-result send in the execution. -/
def sendThenStop : Region dialect [()] [()] :=
  .bind (.letOp .send (.cons .here .nil) .nil (.ret .nil)) (.stop .abort)

theorem zero_result_before_stop (r : Bit) (s : Nat) :
    (sendThenStop.denote meaning (Values.get (.cons r .nil))).runM (handler false) s =
      pure ⟨.stopped .abort, s + 1, [.sent r]⟩ := by
  simp [sendThenStop, Region.denote, Regions.denote, meaning, Operands.eval,
    Values.get, PIR.Proc.bind, PIR.Proc.runM, handler, PIR.Execution.followM]

end TestsSecurity.LocalCouplingClients
