module

public import ZkcArkLib.Fri.PhasesSampling
public import ZkcExamples.Structured.FriScalarLoop

@[expose] public section

/-! The abstract scalar sampler interpreted at the retained verifier's real
draw and delivery operations. Ordinals are chronological. A refused draw
or delivery preserves the prefix that was actually executed. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.RetainedQueries
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured FriScalarLoop
open Phases
attribute [local implicit_reducible] samplingOperations SamplingOperation.Reply

/-- Only the scalar operations are reached at this placement. -/
def operations (model : DomainModel) (service : Nat) :
    PIR.OperationInterpretation (samplingOperations 5) (OracleProtocol.Interface model)
  | .scalar index =>
      ((OracleProtocol.iterationObservations model).enter loop.site index).bind
        fun _ ↦ draw model service
  | .revealScalar index x =>
      (deliver model x).bind fun _ ↦ (OracleProtocol.iterationObservations model).leave loop.site index
  | .block _ | .revealBlock .. => .halt .refused

theorem positions_eq (model : DomainModel) (service : Nat) :
    positions model service = ((scalarQueries 5 8 0).interpret (operations model service)).bind
      fun ys ↦ .done (List.ofFn ys) := by
  have next (xs : Positions) (i : Nat) :
      (OracleProtocol.iterationObservations model).within loop.site i (step model service xs) =
        ((operations model service) (.scalar i)).bind fun x ↦
          ((operations model service) (.revealScalar i x)).bind fun _ ↦ .done (List.append (α := Fin 32) xs [x]) := by
    rw [IterationObservations.within_eq]
    simp only [step, bind, pure, operations, PIR.Process.bind_assoc, PIR.Process.bind]
    rfl
  unfold positions
  simp_rw [next]
  exact collectScalarQueries (operations model service) 8 0 []

theorem source_body (model : DomainModel) (service : Nat) :
    FriSourceBodies.protocol1Body.denote
      ((FriSource.verifierAlgebra model).meaning (FriSource.verifierTable model) context 1)
      (Values.cons (OracleProtocol.concrete model .index 8)
        (.cons (OracleProtocol.concrete model (.service contract) service) .nil)).get =
      (marks model ["", "", "s2", "", "", "s5", "s6", "s8", "", loop.site]).bind fun _ ↦
        ((scalarQueries 5 8 0).interpret (operations model service)).bind
          fun ys ↦ .done (packed model (List.ofFn ys)) := by
  rw [body, program, positions_eq]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

open FriSource FriSourceBodies FriSourceViews
attribute [local implicit_reducible] protocol1Signature

/-- The installed child executes under the actual nested role map. Both the
service and the count survive input masking, as does the returned list. -/
theorem installed (model : DomainModel) (service : Nat) :
    invokeProtocol (verifierTable model) protocol1Signature context 1
      (.cons (OracleProtocol.concrete model .index 8)
        (.cons (OracleProtocol.concrete model (.service contract) service) .nil)) =
      (marks model ["", "", "s2", "", "", "s5", "s6", "s8", "", loop.site]).bind fun _ ↦
        ((scalarQueries 5 8 0).interpret (operations model service)).bind
          fun ys ↦ .done (packed model (List.ofFn ys)) := by
  refine ((verifierAlgebra model).invokeBody unit.protocolsLinked protocol1Definition protocol1_member
    context 1 _).trans ?_
  let args : Values (Component (verifierValue model)) protocol1Signature.inputs :=
    .cons (OracleProtocol.concrete model .index 8)
      (.cons (OracleProtocol.concrete model (.service contract) service) .nil)
  let maskResult (p : PIR.Process (OracleProtocol.Interface model)
      (Values (Component (verifierValue model)) protocol1Signature.outputs)) :=
    p.bind fun results ↦ .done (maskValues 1 (context.mapScopes protocol1Signature.outputScopes) results)
  refine (congrArg maskResult ((NormalForm.normalizeActions_process
    ((verifierAlgebra model).meaning (verifierTable model) context 1) protocol1Body args.get).trans
    (source_body model service))).trans ?_
  dsimp only [maskResult]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

end ZkcSecurity.ArkLib.Fri.RetainedQueries
