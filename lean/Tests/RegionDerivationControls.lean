import Tests.RegionDerivation

set_option autoImplicit false
namespace Tests.RegionDerivation

open Zkc.Source PIR

local macro "vals[" xs:term,* "]" : term => do
  let mut result ← `(Values.nil)
  for x in xs.getElems.reverse do
    result ← `(Values.cons $x $result)
  return result

/-- The remaining reply tape is observable residual state. Zero-result sends
and marks still produce ordered effects; they do not consume scalar replies. -/
def handler : Handler interface (List Nat) Action
  | .receive site, [] => ⟨.stopped .incomplete, [], [.receive site]⟩
  | .receive site, reply :: rest => ⟨.returned reply, rest, [.receive site]⟩
  | .draw, [] => ⟨.stopped .incomplete, [], [.draw]⟩
  | .draw, reply :: rest => ⟨.returned reply, rest, [.draw]⟩
  | .send n, state => ⟨.returned (), state, [.send n]⟩
  | .mark n, state => ⟨.returned (), state, [.mark n]⟩

def runSchnorr (selected : Bool) (tape : List Nat) :=
  (((schnorr selected).denote source empty).interpret lower).run handler tape

def runSumcheck (count claim : Nat) (tape : List Nat) :=
  (((sumcheck count).denote source (vals[claim] : Scalars).get).interpret lower).run handler tape

theorem schnorr_success : runSchnorr true [3, 2, 5, 99] =
    ⟨.returned vals[true], [99], [.receive 0, .mark 0, .draw, .mark 3, .send 2, .receive 1]⟩ := by
  unfold runSchnorr
  rw [schnorr_equation]
  rfl

theorem schnorr_independent_response : runSchnorr true [3, 2, 8, 99] =
    ⟨.returned vals[false], [99], [.receive 0, .mark 0, .draw, .mark 3, .send 2, .receive 1]⟩ := by
  unfold runSchnorr
  rw [schnorr_equation]
  rfl

theorem schnorr_callback_stop : runSchnorr false [3, 2, 5, 99] =
    ⟨.stopped .abort, [2, 5, 99], [.receive 0]⟩ := by
  unfold runSchnorr
  rw [schnorr_equation]
  rfl

theorem schnorr_after_draw_stop : runSchnorr true [3, 0, 5, 99] =
    ⟨.stopped .exhausted, [5, 99], [.receive 0, .mark 0, .draw, .mark 1]⟩ := by
  unfold runSchnorr
  rw [schnorr_equation]
  rfl

theorem schnorr_missing_response : runSchnorr true [3, 2] =
    ⟨.stopped .incomplete, [], [.receive 0, .mark 0, .draw, .mark 3, .send 2, .receive 1]⟩ := by
  unfold runSchnorr
  rw [schnorr_equation]
  rfl

def stopSend : Handler interface (List Nat) Action
  | .send n, state => ⟨.stopped .refused, state, [.send n]⟩
  | action, state => handler action state

theorem stopped_send_skips_receive :
    (((schnorr true).denote source empty).interpret lower).run stopSend [3, 2, 5, 99] =
      ⟨.stopped .refused, [5, 99], [.receive 0, .mark 0, .draw, .mark 3, .send 2]⟩ := by
  rw [schnorr_equation]
  rfl

theorem sumcheck_zero (claim : Nat) (tape : List Nat) : runSumcheck 0 claim tape =
    ⟨.returned vals[claim], tape, []⟩ := by
  unfold runSumcheck
  rw [sumcheck_equation]
  rfl

theorem sumcheck_two_rounds : runSumcheck 2 3 [1, 2, 2, 2, 3, 1, 99] =
    ⟨.returned vals[(5 : Nat)], [99],
      [.receive 2, .receive 3, .mark 0, .draw, .mark 3,
       .receive 2, .receive 3, .mark 0, .draw, .mark 2]⟩ := by
  unfold runSumcheck
  rw [sumcheck_equation]
  rfl

theorem sumcheck_guard_stop : runSumcheck 2 4 [1, 2, 2, 99] =
    ⟨.stopped .reject, [2, 99], [.receive 2, .receive 3]⟩ := by
  unfold runSumcheck
  rw [sumcheck_equation]
  rfl

theorem sumcheck_later_guard_stop : runSumcheck 2 3 [1, 2, 2, 1, 3, 99] =
    ⟨.stopped .reject, [99],
      [.receive 2, .receive 3, .mark 0, .draw, .mark 3, .receive 2, .receive 3]⟩ := by
  unfold runSumcheck
  rw [sumcheck_equation]
  rfl

theorem sumcheck_after_draw_stop : runSumcheck 2 3 [1, 2, 0, 99] =
    ⟨.stopped .exhausted, [99], [.receive 2, .receive 3, .mark 0, .draw, .mark 1]⟩ := by
  unfold runSumcheck
  rw [sumcheck_equation]
  rfl

/-- The rule preserves a stopped prefix even when its lexical suffix has a
different stop reason. Suffix proof obligations never assert it executes. -/
theorem bind_stop : Derives
    (Region.bind (.stop .reject : Region dialect [] [Ty.scalar])
      (.stop .abort : Region dialect [Ty.scalar] [Ty.boolean])) empty
    ((Proc.halt .reject : Proc interface Scalars).bind fun _ => .halt .abort) :=
  .bind (.stop _ _) (fun _ => .stop _ _)

theorem bind_stop_needs_no_suffix_law (next : Region dialect [Ty.scalar] [Ty.boolean]) :
    Derives (.bind (.stop .reject : Region dialect [] [Ty.scalar]) next) empty (.halt .reject) := by
  apply Region.Derivation.bindStop
  exact .stop _ _

theorem bind_return_uses_actual_value (n : Nat) : Derives
    (.bind (.ret vals[.here] : Region dialect [Ty.scalar] [Ty.scalar])
      (.ret vals[.here] : Region dialect [Ty.scalar, Ty.scalar] [Ty.scalar]))
    (vals[n] : Scalars).get (.done vals[n]) :=
  .bindReturn (.ret _ _) (.ret _ _)

theorem operation_stop_needs_no_suffix_law
    (next : Region dialect [Ty.scalar, Ty.scalar, Ty.scalar] [Ty.boolean]) :
    Derives (.letOp .guard (Operands.identity _) .nil next)
      (vals[(4 : Nat), (1 : Nat), (2 : Nat)] : Values Value [Ty.scalar, Ty.scalar, Ty.scalar]).get (.halt .reject) := by
  refine Region.Derivation.letOpStop (meaning := source) (operations := lower) .guard _ next .nil ?_
  exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl

/-- A concrete helper result can carry its local facts into a later guard.
The general effectful rule still quantifies over every possible returned tuple. -/
def checkedUpdate : Region dialect [Ty.scalar, Ty.scalar, Ty.scalar, Ty.scalar] [Ty.scalar] :=
  .letOp .update vals[.here, .there .here, .there (.there .here)] .nil
    (.letOp .guard vals[.here, .here, .there (.there (.there (.there .here)))] .nil
      (.ret vals[.here]))

theorem returned_value_fact (a b x : Nat) :
    Derives checkedUpdate (vals[a, b, x, 0] : Values Value [Ty.scalar, Ty.scalar, Ty.scalar, Ty.scalar]).get
      (.done vals[a + x * b]) := by
  unfold checkedUpdate
  refine Region.Derivation.letOpReturn (meaning := source) (operations := lower) .update _
    (values := vals[a + x * b]) .nil ?_ ?_
  · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
  · refine Region.Derivation.letOpReturn (meaning := source) (operations := lower) .guard _
      (values := .nil) .nil ?_ (.ret _ _)
    exact guard_local_law _ _ _ (Nat.add_zero _)

theorem missing_guard_premise_refused :
    ¬ source.OperationLaw lower .guard vals[(4 : Nat), (1 : Nat), (2 : Nat)] .nil (.done .nil) := by
  intro law
  have wrong := law .nil rfl
  cases wrong

theorem wrong_source_refused : ¬ Derives (schnorr false) empty (schnorrProcess true) := by
  intro derivation
  have wrong := congrArg (fun p => (p.run handler [3, 2, 5, 99]).outcome) derivation.sound
  rw [schnorr_equation] at wrong
  cases wrong

theorem wrong_result_order_refused : ¬ Derives
    (.ret vals[.there .here, .here] : Region dialect [Ty.scalar, Ty.scalar] [Ty.scalar, Ty.scalar])
    (vals[(2 : Nat), (5 : Nat)] : Values Value [Ty.scalar, Ty.scalar]).get (.done vals[(2 : Nat), (5 : Nat)]) := by
  intro derivation
  have wrong := derivation.sound
  cases wrong

/-- Exact event order is stronger than equality of final acceptance. -/
theorem reordered_effects_refused : runSchnorr true [3, 2, 5, 99] ≠
    ⟨.returned vals[true], [99], [.receive 0, .draw, .mark 0, .mark 3, .send 2, .receive 1]⟩ := by
  rw [schnorr_success]
  intro wrong
  cases wrong

def guardedCallback : Region dialect [Ty.scalar, Ty.scalar, Ty.scalar] [] :=
  .letOp .guard (Operands.identity _) .nil (.ret .nil)

theorem one_callback_input_succeeds :
    (guardedCallback.denote source
      (vals[(3 : Nat), (1 : Nat), (2 : Nat)] : Values Value [Ty.scalar, Ty.scalar, Ty.scalar]).get).interpret lower = .done .nil := rfl

/-- A summary checked at one callback input cannot certify every invocation. -/
theorem callback_input_summary_refused : ¬ Regions.Derivation source lower
    (.cons guardedCallback .nil) vals[fun _ => .done .nil] := by
  intro derivation
  have wrong := congrArg (fun callbacks => callbacks.get .here vals[(4 : Nat), (1 : Nat), (2 : Nat)]) derivation.sound
  cases wrong

namespace Shape

inductive Op where
  | inspect

abbrev dialect : Dialect where
  Ty := Unit
  Op := Op
  arguments _ := []
  results _ := [()]
  regions _ := [([], [()])]

abbrev Value (_ : Unit) := Nat
abbrev calls : Signature := ⟨Unit, fun _ => Nat⟩
abbrev closed : Signature := ⟨Empty, Empty.elim⟩

def inspect {I : Signature} (p : Proc I (Values Value [()])) : Proc I (Values Value [()]) :=
  match p with
  | .call _ _ => .done vals[(1 : Nat)]
  | _ => .done vals[(0 : Nat)]

def meaning : RegionMeaning dialect calls where
  Value := Value
  operation
    | .inspect, .nil, .cons callback .nil => inspect (callback .nil)

def erase : OperationInterpretation calls closed := fun _ => .done 7

def original : Values (RegionFunction Value calls) [([], [()])] :=
  vals[fun _ => .call () fun n => .done vals[n]]

def translated : Values (RegionFunction Value closed) [([], [()])] :=
  vals[fun _ => .done vals[(7 : Nat)]]

theorem callbacks_translate_exactly : RegionFunctions.translate (dialect := dialect) erase original = translated := rfl

/-- Even exact callback translation does not make an arbitrary operation commute.
The explicit local compatibility premise is unprovable for this shape observer. -/
theorem shape_inspection_law_refused :
    ¬ meaning.OperationLaw erase .inspect .nil translated (.done vals[(0 : Nat)]) := by
  intro law
  have wrong := law original callbacks_translate_exactly
  cases wrong

end Shape
end Tests.RegionDerivation
