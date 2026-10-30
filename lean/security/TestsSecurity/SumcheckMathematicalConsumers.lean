import Tests.SumcheckMathematicalInstallation
import ZkcSecurity.Bindings.Sumcheck.SourceRound
import ZkcSecurity.Bindings.Sumcheck.Table.TableComponentNominal
import ZkcSecurityTools.ComponentDerivation

set_option autoImplicit false
noncomputable section
namespace TestsSecurity.SumcheckMathematicalConsumers
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open SumcheckReferenceInstallation
open Tests.MultilinearReferences

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField

variable {Frame H O E P : Type} {Raw : E → Type} {n : Nat}

/-- Both real libraries consume precisely the same mathematical installation.
The remaining parameters are the actual role/context, handler or query cuts,
frame and mathematical hypotheses, rather than source/ABI equations. -/
def bothSampled (selected : RetainedSource) :=
  SourceRound.source_sampled model (Frame := Frame) (n := n) (E := E) (P := P) (Raw := Raw)
    (source selected).payload.definitions (source selected).payload.linked
    (Tests.SumcheckMathematicalInstallation.bodies selected)
    (Occurrence.table model (source selected).payload)

abbrev bothHonest (selected : RetainedSource) :=
  SourceRound.source_honest model (H := H) (O := O) (n := n)
    (source selected).payload.definitions (source selected).payload.linked
    (Tests.SumcheckMathematicalInstallation.bodies selected)
    (Occurrence.table model (source selected).payload)

abbrev bothProvers (selected : RetainedSource) :=
  Prover.body_reference model (source selected).payload.definitions (source selected).payload.linked
    (Tests.SumcheckMathematicalInstallation.bodies selected)
    (Occurrence.table model (source selected).payload)

/-- A false scalar does not prevent table decoding or manufacture Yes. The
complete private frame belongs to the same prefix representation. -/
theorem false_claim_represented (xs : List (model.Field field)) (scalar : model.Field field)
    (frame : Frame) (count : Nat) (shape : xs.length = 2^count) (wrong : scalar ≠ xs.sum) :
    (TableComponent.Nominal.layout (F := model.Field field) (Frame := Frame) field).representation.No
      (TableComponent.PrefixState.initial xs count scalar frame shape) := by
  apply (TableComponent.Layout.no_iff _ _).mpr
  exact wrong

/-- Dropping or changing the private residual cannot satisfy the consumer's
full postcondition, even if every public source output has been copied. -/
theorem lost_private_residual (table : Zkc.Polynomial.Multilinear.Table (model.Field field) (n+1))
    (point : List (model.Field field)) (original changed : Frame) (different : changed ≠ original)
    (values : Values (Component model.Value) SumcheckVerifierBodies.repeatState) :
    ¬ SourceRound.residual model table point original (values, changed) := by
  rintro ⟨lo, hi, r, same, _⟩
  exact different (congrArg Prod.snd same)

/-- A source rejection is a soundness stop but cannot prove honest return.
This handler refuses the first actual receive, before any challenge is drawn. -/
def rejectingHandler : PIR.Handler (Occurrence.signature model.toCarriers) Unit Unit :=
  fun _ _ => ⟨.stopped .reject, (), []⟩

omit fieldLaw in
theorem actual_rejection (selected : RetainedSource) (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx 1 2) (index handle : Nat)
    (point : List (model.Field field)) (scalar : model.Field field) :
    ((Tests.SumcheckMathematicalInstallation.callback selected).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (tables model (source selected).payload.definitions) (ctx.roles 1)
        (Occurrence.table model (source selected).payload) ctx Occurrence.iterations)
      (Syntax.pattern.environment model (inputs model index (some point) (some scalar) (some handle))).get).run
        (rejectingHandler model) () = ⟨.stopped .reject, (), []⟩ := by
  rw [Tests.SumcheckMathematicalInstallation.actual_round model selected ctx distinct index]
  rfl

example (_selected : RetainedSource) (_ctx : ProtocolContext)
    (_distinct : NormalForm.RosterDistinct _ctx 1 2) (_index _handle : Nat)
    (_point : List (model.Field field)) (_scalar : model.Field field) : True := by
  fail_if_success
    have : ((Tests.SumcheckMathematicalInstallation.callback _selected).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (tables model (source _selected).payload.definitions) (_ctx.roles 1)
        (Occurrence.table model (source _selected).payload) _ctx Occurrence.iterations)
      (Syntax.pattern.environment model (inputs model _index (some _point) (some _scalar) (some _handle))).get).run
        (rejectingHandler model) () = ⟨.returned (state model (some _point) (some _scalar)), (), []⟩ := by
      rw [actual_rejection model _selected _ctx _distinct _index _handle _point _scalar]
  trivial

/-- The installed actual-round law supplies no polynomial collision theorem.
Its reached-history raw-query bound remains an ordinary mathematical goal. -/
example {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
    (_absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (_charge : List E → E → ENNReal) (_ctx : ProtocolContext) (_handle : Nat)
    (_cuts : SourceRound.Cuts model _absorb _ctx _handle) (_history : List E)
    (_table : Zkc.Polynomial.Multilinear.Table (model.Field field) (n+1))
    (_point : List (model.Field field)) (_scalar : model.Field field) (_frame : Frame)
    (_wrong : _scalar ≠ (TableReference.data (model.Field field)).total _table) : True := by
  fail_if_success
    have : Derivation _absorb (ZkcSecurity.Obligations.boundedEscape _charge)
        (fun _ => SourceRound.residual model _table _point _frame) _history
        ((reference model _ctx (some _handle) (some _point) (some _scalar)).bind
          fun values => .done (values, _frame)) := by
      solve
      | assemble_component_property
          [SourceRound.adversarial model _absorb (ZkcSecurity.Obligations.boundedEscape _charge)
            _ctx _handle _cuts _table _point _scalar _frame _history _wrong]
          unfolding [] repeating [] reporting "Sumcheck reached raw query requires its mathematical cut"
          from Syntax.form
  trivial

#print axioms bothSampled
#print axioms bothHonest
#print axioms bothProvers
#print axioms false_claim_represented
#print axioms lost_private_residual
#print axioms actual_rejection
#print axioms SourceRound.conditional_escape
#print axioms SourceRound.source_sampled
#print axioms SourceRound.source_honest
#print axioms SourceRound.producer_polynomial
#print axioms SourceRound.residual_no
#print axioms SourceRound.source_honest_represented
end TestsSecurity.SumcheckMathematicalConsumers
