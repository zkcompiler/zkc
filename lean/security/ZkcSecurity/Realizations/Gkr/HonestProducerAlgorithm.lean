module

public import ZkcSecurity.Realizations.Gkr.HonestProducerRoundAlgorithm
public import ZkcExamples.Structured.GkrVerifierProcess
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcSecurity.Realizations.Gkr.HonestProducerPacketAlgorithm
public import Zkc.Polynomial.Multilinear.CoefficientRows
public import Zkc.Polynomial.Multilinear.LineCoefficients
public import ZkcSecurity.Realizations.Gkr.Circuit
public import ZkcSecurity.Realizations.Gkr.Encoding
public import Zkc.Source.TypedABI

@[expose] public section

/-! The complete computed GKR producer, defined from the independent circuit.
This module needs no source helper correctness premise. The separate
HonestProducerSource bridge identifies it with checked source computation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerSource
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers Generated.Presentations.Gkr.Root
open ZkcSecurity.Examples.Components
open HonestProducerRounds HonestProducerPackets

variable {F G : Type} [Field F] [DecidableEq F]

noncomputable def line {width : Nat} (below : Table F width) (left right : List F) : List F :=
  row (width + 1) (linePolynomial width below (coordinates width left) (coordinates width right))

/-- Mathematical presentation of a complete layer, with all real interactions
retained. The separate source bridge must justify replacing each actual local
computation by these independent values. -/
noncomputable def layer (ctx : ProtocolContext) {width : Nat}
    (circuit : Families.Gkr.Circuit F width) (remaining index : Nat) (point : List F) :
    PIR.Process (participantInterface F G) (List F) :=
  let reference := Circuit.factors circuit remaining index (coordinates width point)
  (execute (GkrVerifier.leftContext ctx) width (n := width) reference (encode reference) []).bind fun left =>
  (execute (GkrVerifier.rightContext ctx) width (n := 0)
    ((Nat.zero_add width).symm ▸ left.reference) left.raw []).bind fun right =>
  let coefficients := line (circuit.wires remaining (index + 1)) left.point right.point
  .call (.send (ty := .field scalarDomain) (GkrVerifier.lineConstantSite ctx) (ctx.roles 1)
    ((coefficients)[0]?.getD 0)) fun _ =>
  (sendTail ctx (tail coefficients 0 width)).bind fun _ =>
  .call (.receive (.field scalarDomain) (GkrVerifier.lineDeliverySite ctx) (ctx.roles 1)) fun challenge =>
  .done (linePoints left.point right.point challenge)

def output (ctx : ProtocolContext) : Nat → List F → PIR.Process (participantInterface F G) (List F)
  | 0, point => .done point
  | count + 1, point =>
    .call (.receive (.field scalarDomain) (GkrVerifier.outputDeliverySite ctx) (ctx.roles 1)) fun r =>
    output ctx count (point ++ [r])

noncomputable def layers (ctx : ProtocolContext) (encoding : CircuitEncoding F) :
    Nat → Nat → List F → PIR.Process (participantInterface F G) (List F)
  | _, 0, point => .done point
  | index, count + 1, point =>
    (layer ctx encoding.circuit (encoding.layers - index - 1) index point).bind fun next =>
    layers ctx encoding (index + 1) count next

noncomputable def producer (ctx : ProtocolContext) (encoding : CircuitEncoding F) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  (output ctx encoding.width []).bind fun point =>
  (layers ctx encoding 0 encoding.layers point).bind fun _ => .done (.cons none .nil)

variable [AddCommGroup G] [Module F G] [DecidableEq G]

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem layer_yields (ctx : ProtocolContext) {width : Nat}
    (circuit : Families.Gkr.Circuit F width) (remaining index : Nat) (point : List F) :
    PIR.Yields (fun result => result.length = width) (layer (G := G) ctx circuit remaining index point) := by
  unfold layer
  apply (execute_yields (G := G) (GkrVerifier.leftContext ctx) width _ _ [] (encode_decodes _)
    (Circuit.factors_admissible _ _ _ _)).bind
  rintro left ⟨decoded, allowed, suffix, pointEq, size, _⟩
  have leftLength : left.point.length = width := by simp_all
  apply (execute_yields (G := G) (GkrVerifier.rightContext ctx) width _ _ []
    (cast_decodes _ _ _ decoded) (cast_admissible _ _ allowed)).bind
  rintro right ⟨_, _, rightSuffix, rightEq, rightSize, _⟩
  have rightLength : right.point.length = width := by simp_all
  simp only [PIR.Yields]
  intro _
  apply (show PIR.Yields (fun _ => True) (sendTail (G := G) ctx
    (tail (line (circuit.wires remaining (index + 1)) left.point right.point) 0 width)) from by
      induction tail (line (circuit.wires remaining (index + 1)) left.point right.point) 0 width with
      | nil => trivial
      | cons value rest ih => exact fun _ => ih).bind
  intro _ _ r
  simp only [PIR.Yields, linePoints_length, leftLength, rightLength, min_self]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem output_yields (ctx : ProtocolContext) (count : Nat) (point : List F) :
    PIR.Yields (fun result => result.length = point.length + count) (output (G := G) ctx count point) := by
  induction count generalizing point with
  | zero => simp [output, PIR.Yields]
  | succ count ih =>
    intro r
    apply (ih (point ++ [r])).mono
    intro result size
    simp only [List.length_append, List.length_singleton] at size
    omega

end ZkcSecurity.Realizations.Gkr.HonestProducerSource
