module

public import ZkcSecurityExamples.Gkr.SourceValidator
public import ZkcSecurityExamples.Components.GkrFiniteCircuit

public section

open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcSecurity.Examples.Components
open ZkcSecurity.Realizations.Gkr
open Zkc.Polynomial.Multilinear

set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.GkrComponentContracts

def runtime : Source.Invocation ℚ :=
  ⟨GkrCallerRealization.inputs, GkrCallerRealization.honestOutputs,
    GkrCallerRealization.stackedAdd, GkrCallerRealization.stackedMul, 2, 1, 1, 0⟩

def messages : List ℚ := [120, -15, -105, 0, 64, 56, 8, 0, 8, -8, 0, 0, 6, 2, 3, 0]

def circuit : ZkcSecurity.Families.Gkr.Circuit ℚ 1 :=
  ⟨GkrFiniteCircuit.inputTable, GkrFiniteCircuit.addWiring, GkrFiniteCircuit.mulWiring⟩

def outputs : Table ℚ 1 := fun bits => if bits 0 then 30 else 120

def consumerHandler : PIR.Handler (Actions ℚ ℚ) (List ℚ × Nat × Nat) Unit
  | .receive (.field _) _ _, (value :: proof, queries, deliveries) =>
      ⟨.returned value, (proof, queries, deliveries), []⟩
  | .query _ _ _, (proof, queries, deliveries) => ⟨.returned 0, (proof, queries + 1, deliveries), []⟩
  | .send .., (proof, queries, deliveries) => ⟨.returned (), (proof, queries, deliveries + 1), []⟩
  | _, state => ⟨.stopped .refused, state, []⟩

def verifier := GkrVerifier.verifier (F := ℚ) (G := ℚ) {} 0 2 1 outputs
  circuit.inputs circuit.add circuit.mul

theorem represented : Source.Represents circuit 2 outputs runtime := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, by decide, by decide, ?_, ?_, by decide, by decide, by decide⟩
  · simpa [GkrRoundsLayout.encode, List.ofFn_succ, vertex, circuit, GkrFiniteCircuit.inputTable,
      runtime, GkrCallerRealization.inputs] using GkrRoundsLayout.decode_encode (F := ℚ) GkrFiniteCircuit.inputTable
  · simpa [GkrRoundsLayout.encode, List.ofFn_succ, vertex, outputs, runtime,
      GkrCallerRealization.honestOutputs] using GkrRoundsLayout.decode_encode outputs
  · intro layer bounded
    have cases : layer = 0 ∨ layer = 1 := by omega
    have decoded := GkrRoundsLayout.decode_encode (F := ℚ) (GkrFiniteCircuit.addWiring layer)
    rcases cases with rfl | rfl <;>
      simpa [GkrRoundsLayout.encode, List.ofFn_succ, vertex, Fin.cons, Fin.cases, Fin.induction,
        Fin.induction.go, circuit, GkrFiniteCircuit.addWiring,
        CircuitEncoding.block, runtime, GkrCallerRealization.stackedAdd] using decoded
  · intro layer bounded
    have cases : layer = 0 ∨ layer = 1 := by omega
    have decoded := GkrRoundsLayout.decode_encode (F := ℚ) (GkrFiniteCircuit.mulWiring layer)
    rcases cases with rfl | rfl <;>
      simpa [GkrRoundsLayout.encode, List.ofFn_succ, vertex, Fin.cons, Fin.cases, Fin.induction,
        Fin.induction.go, circuit, GkrFiniteCircuit.mulWiring,
        CircuitEncoding.block, runtime, GkrCallerRealization.stackedMul] using decoded

def occurrenceHandler : PIR.Handler (Occurrence.signature (uniformCarriers ℚ ℚ))
    (List ℚ × Nat × Nat) Unit
  | .action (.receive (.field _) _ _), (value :: proof, queries, deliveries) =>
      ⟨.returned value, (proof, queries, deliveries), []⟩
  | .action (.query _ _ _), (proof, queries, deliveries) => by
      change PIR.Execution (List ℚ × Nat × Nat) Unit ℚ
      exact ⟨.returned 0, (proof, queries + 1, deliveries), []⟩
  | .action (.send ..), (proof, queries, deliveries) =>
      ⟨.returned (), (proof, queries, deliveries + 1), []⟩
  | .enter _, state => ⟨.returned (), state, []⟩
  | .leave _, state => ⟨.returned (), state, []⟩
  | _, state => ⟨.stopped .refused, state, []⟩

theorem admitted : runtime.Admitted := Source.represents_admitted _ _ _ _ represented

example : ¬ Source.Represents circuit 2 (fun bits => outputs bits + 1) runtime := by
  intro substituted
  have same := Option.some.inj (represented.outputsDecoded.symm.trans substituted.outputsDecoded)
  have atZero := congrFun same (fun _ => false)
  norm_num [outputs] at atZero

example : outputs = circuit.wires 2 0 := GkrFiniteCircuit.outputs.symm

/-- The entire verifier consumes both layers, both Sumcheck calls per layer,
and both combination polynomials; the unread suffix remains untouched. -/
example : verifier.run consumerHandler (messages ++ [99], 0, 0) =
    ⟨.returned (some true), ([99], 7, 7), []⟩ := by cbv

example : (SourceValidator.body (G := ℚ) runtime).run occurrenceHandler (messages ++ [99], 0, 0) =
    ⟨.returned (.cons (some true) .nil), ([99], 7, 7), []⟩ := by
  rw [SourceValidator.admitted_body runtime admitted]
  -- This handler ignores occurrence labels. Keep them abstract instead of
  -- evaluating the source inventory merely to discard their strings.
  generalize HonestProducerSource.currentSites = sites
  cbv

example : verifier.run consumerHandler (121 :: messages.tail, 0, 0) =
    ⟨.stopped .reject, (messages.drop 3, 1, 1), []⟩ := by cbv

example : verifier.run consumerHandler ([], 0, 0) =
    ⟨.stopped .refused, ([], 1, 1), []⟩ := by cbv

/-- A substituted first-layer line value is rejected in the next layer,
even though the first layer's zero-wiring check admits that substitution. -/
example : verifier.run consumerHandler (messages.take 6 ++ [9, 0] ++ messages.drop 8, 0, 0) =
    ⟨.stopped .reject, (messages.drop 11, 4, 4), []⟩ := by cbv

example : (GkrVerifier.verifier (F := ℚ) (G := ℚ) {} 0 2 1
    (fun bits => if bits 0 then 31 else 121) circuit.inputs circuit.add circuit.mul).run
      consumerHandler (messages, 0, 0) =
    ⟨.stopped .reject, (messages.drop 3, 1, 1), []⟩ := by cbv

example : (verifier.run (fun _ state => ⟨.stopped .exhausted, state, [()]⟩)
    (messages, 0, 0)) = ⟨.stopped .exhausted, (messages, 0, 0), [()]⟩ := by cbv

example : SourceValidator.body (G := ℚ) {runtime with width := 5} = .halt .reject := by
  kernel_rfl

end TestsSecurity.GkrComponentContracts
