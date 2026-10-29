module

public import ZkcExamples.Construction.GkrSourceProtocol
public import Zkc.Construction.Uniform.ScalarHandles

@[expose] public section

/-! Capability-label naturality of the retained scalar GKR presentation.
The actual nominal participant uses the source-order capability selected by
its checked ABI. These equations only forget that label in the scalar API;
they preserve every helper failure, branch, message and loop count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.GkrSourceHandles
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceProtocol
open Uniform.ScalarHandles
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G]
  [Module F G] [DecidableEq G]

private theorem interpret_branch {I J : PIR.Signature} {A : Type}
    (operations : PIR.OperationInterpretation I J) (condition : Prop) [Decidable condition]
    (yes no : PIR.Process I A) :
    (if condition then yes else no).interpret operations =
      if condition then yes.interpret operations else no.interpret operations := by
  split <;> rfl

/-- Closed helpers have no capability effects, even when they stop. -/
theorem helper_handle (entry : Helper) (args : Values (assignment F G) entry.inputs)
    (replacement : Nat) :
    (helper entry args).interpret (replace replacement) = helper entry args := by
  unfold helper GkrRoundsReading.closed
  rw [closed_invoke_plain]
  simp only [PIR.Process.interpret_comp]
  congr 1
  funext impossible
  exact nomatch impossible

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem round_handle (ctx : ProtocolContext) (original replacement : Nat)
    (state : List F × F) :
    (GkrVerifier.round (G := G) ctx original state).interpret (replace replacement) =
      GkrVerifier.round ctx replacement state := by
  simp only [GkrVerifier.round, GkrVerifier.roundFirst, GkrVerifier.roundSecond,
    GkrVerifier.roundCheck, GkrVerifier.roundChallenge, interpret_branch,
    PIR.Process.interpret, replace, PIR.Process.bind]
  rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem rounds_handle (ctx : ProtocolContext) (original replacement count : Nat)
    (point : List F) (claim : F) :
    (rounds (G := G) ctx original count point claim).interpret (replace replacement) =
      rounds ctx replacement count point claim := by
  simp only [rounds, interpret_branch, Zkc.Source.interpret_repeat, round_handle, PIR.Process.interpret]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem coefficients_handle (ctx : ProtocolContext) (width replacement : Nat)
    (initial : List F) :
    (coefficients (G := G) ctx width initial).interpret (replace replacement) =
      coefficients ctx width initial := by
  simp only [coefficients, interpret_branch, Zkc.Source.interpret_repeat, GkrVerifier.lineCoefficient,
    PIR.Process.interpret, replace, PIR.Process.bind]
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem output_handle (ctx : ProtocolContext) (original replacement count : Nat)
    (point : List F) :
    (output (G := G) ctx original count point).interpret (replace replacement) =
      output ctx replacement count point := by
  simp only [output, interpret_branch, Zkc.Source.interpret_repeat, GkrVerifier.outputRound,
    GkrVerifier.outputDelivery, PIR.Process.interpret, replace, PIR.Process.bind]
  rfl

private theorem afterCoefficients_handle (ctx : ProtocolContext)
    (index original replacement selector : Nat) (add mul : List F)
    (current combined : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr"])
    (split : Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"])
    (first : F) (line : List F) :
    (afterCoefficients ctx index original selector add mul current combined split first line).interpret
      (replace replacement) =
      afterCoefficients ctx index replacement selector add mul current combined split first line := by
  simp only [afterCoefficients, PIR.Process.interpret_bind, helper_handle (F := F) (G := G), interpret_branch,
    PIR.Process.interpret, replace, PIR.Process.bind]

private theorem layer_handle (ctx : ProtocolContext)
    (index original replacement selector width : Nat) (add mul point : List F) (claim : F) :
    (layer (G := G) ctx index original selector width add mul point claim).interpret
      (replace replacement) =
      layer ctx index replacement selector width add mul point claim := by
  simp only [layer, PIR.Process.interpret_bind, helper_handle (F := F) (G := G), rounds_handle,
    afterCoefficients_handle, coefficients_handle, PIR.Process.interpret, replace, PIR.Process.bind]

private theorem layers_handle (ctx : ProtocolContext)
    (original replacement selector width count : Nat) (add mul : List F) (state : List F × F) :
    (layers (G := G) ctx original selector width count add mul state).interpret
      (replace replacement) = layers ctx replacement selector width count add mul state := by
  simp only [layers, interpret_branch, Finite.interpret_fold, layer_handle, PIR.Process.interpret]

theorem verifier_handle (inputs outputs add mul : List F)
    (count selector width original replacement : Nat) :
    (verifier (G := G) inputs outputs add mul count selector width original).interpret
      (replace replacement) = verifier inputs outputs add mul count selector width replacement := by
  simp only [verifier, PIR.Process.interpret_bind, helper_handle (F := F) (G := G), interpret_branch,
    output_handle, layers_handle, PIR.Process.interpret]

theorem source_handle (inputs outputs add mul : List F)
    (count selector width original replacement : Nat) :
    (sourceVerifier (G := G) inputs outputs add mul count selector width original).interpret
      (replace replacement) = sourceVerifier inputs outputs add mul count selector width replacement := by
  simp only [source_equation, PIR.Process.interpret_bind, verifier_handle, PIR.Process.interpret]

end ZkcExamples.Construction.GkrSourceHandles
