module

public import Zkc.Source.Structured.UnitViews
public import Zkc.Source.Structured.ClosedProjection
public import Zkc.Source.TypedABI
public import ZkcExamples.Structured.PolynomialRestrictionData
public import ZkcExamples.Structured.PolynomialRestrictionBodies
public import ZkcExamples.Structured.PolynomialRestrictionMath

@[expose] public section

/-! Exact original helper and caller binding. The checked unit is reconstructed
from printed typed bodies; its admission phases are kernel equations against
the native structured export, including the actual caller return context. -/

set_option autoImplicit false
namespace ZkcExamples.Structured.PolynomialRestrictionBinding
open Zkc.Source Zkc.Source.Structured
open PolynomialRestrictionBodies PolynomialRestrictionMath
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

structured_closed_views PolynomialRestrictionData.snapshot
  helpers [restrict, evaluate] protocols [caller] root entryBody

theorem restrict_associated : BodyIn subject.payload.definitions restrictHelper restrictBody :=
  BodyIn.of_mem restrict_member (by rfl) restrict_exact

theorem evaluate_associated : BodyIn subject.payload.definitions evaluateHelper evaluateBody :=
  BodyIn.of_mem evaluate_member (by rfl) evaluate_exact

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def restrictArguments (p : Bilinear F) (r : F) :
    Values (assignment F G) restrictHelper.inputs :=
  .cons p.c00 (.cons p.c10 (.cons p.c01 (.cons p.c11 (.cons r .nil))))

def affineValues (p : Affine F) : Values (assignment F G) restrictHelper.outputs :=
  .cons p.constant (.cons p.linear .nil)

theorem restrict_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (p : Bilinear F) (r : F) :
    restrictBody.denote (Evaluation.meaning sites table) (restrictArguments p r).get =
      .done (affineValues (restrictFirst p r)) := rfl

/-- This invokes the retained original helper, not an unbound replacement. -/
theorem restrict_invocation {I : PIR.Signature} (sites : SiteObservations I)
    (p : Bilinear F) (r : F) :
    invoke (Evaluation.payloadMeanings (F := F) (G := G) sites program.payload) restrictHelper (restrictArguments p r) =
      .done (affineValues (restrictFirst p r)) :=
  (Evaluation.payload_invoke_body_view_as sites program.payload restrictDefinition restrict_member restrictHelper
    (by rfl) restrictBody restrict_exact (restrictArguments p r)).trans
      (restrict_body _ _ p r)

theorem evaluate_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (p : Affine F) (r : F) :
    evaluateBody.denote (Evaluation.meaning sites table)
      (Values.cons p.constant (.cons p.linear (.cons r .nil))).get =
      .done (.cons (p.evaluate r) .nil) := rfl

theorem evaluate_invocation {I : PIR.Signature} (sites : SiteObservations I)
    (p : Affine F) (r : F) :
    invoke (Evaluation.payloadMeanings (F := F) (G := G) sites program.payload) evaluateHelper
      (.cons p.constant (.cons p.linear (.cons r .nil))) =
      .done (.cons (p.evaluate r) .nil) :=
  (Evaluation.payload_invoke_body_view_as sites program.payload evaluateDefinition evaluate_member evaluateHelper
    (by rfl) evaluateBody evaluate_exact
    (.cons p.constant (.cons p.linear (.cons r .nil)))).trans (evaluate_body _ _ p r)

def callerArguments (p : Bilinear F) (x y frame : F) :
    Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr",
      .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr",
      .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons p.c00 (.cons p.c10 (.cons p.c01 (.cons p.c11
    (.cons x (.cons y (.cons frame .nil))))))

def callerResult (p : Bilinear F) (x y frame : F) :
    Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr",
      .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons (restrictFirst p x).constant (.cons (restrictFirst p x).linear
    (.cons (p.evaluate x y) (.cons frame .nil)))

set_option smartUnfolding true in
/-- Full Process equality retains both source marks, coefficients, future
evaluation, and caller-owned frame under arbitrary site observations. -/
theorem caller_observed {I : PIR.Signature} (sites : SiteObservations I)
    (p : Bilinear F) (x y frame : F) :
    Evaluation.payloadDenote (F := F) (G := G) sites program.payload (callerArguments p x y frame) =
      (sites.mark "").bind (fun _ => (sites.mark "").bind
        (fun _ => .done (callerResult p x y frame))) := by
  change entryBody.denote (Evaluation.meaning sites
    (Evaluation.payloadMeanings sites program.payload)) (callerArguments p x y frame).get = _
  simp only [entryBody, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.results, Operands.eval, Regions.denote, callerArguments,
    Environment.prepend, TypedABI.get_cons_here, TypedABI.get_cons_there,
    PIR.Process.bind, PIR.Process.bind_assoc]
  have restriction := restrict_invocation (G := G) sites p x
  simp only [restrictArguments, restrictHelper] at restriction
  rw [restriction]
  simp only [PIR.Process.bind, affineValues, Environment.prepend, Environment.push,
    TypedABI.get_cons_here, TypedABI.get_cons_there]
  rw [evaluate_invocation (G := G) sites (restrictFirst p x) y]
  simp only [PIR.Process.bind, restriction_evaluation]
  rfl

theorem caller_execution (p : Bilinear F) (x y frame : F) :
    program.payload.denote F G (callerArguments p x y frame) =
      .done (callerResult p x y frame) :=
  caller_observed SiteObservations.closed p x y frame

end ZkcExamples.Structured.PolynomialRestrictionBinding
