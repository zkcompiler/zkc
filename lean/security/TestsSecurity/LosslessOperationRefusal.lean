module

public import ZkcSecurity.Bindings.Transcript.PublicSourceSupport
public import TestsSecurity.RootConnectionControls

@[expose] public section

/-! Refusals for local lossless authority. Handle-bearing receives, lossy
malformed decoders and an unsupported reply branch cannot gain authority.
The source/output relation remains the existing complete nominal relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.LosslessOperationRefusal
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir

variable (model : DomainModel) (origin : Origin)

example : ¬ Original.LosslessInterface (NominalDomain.interface (carriers := model.toCarriers)) :=
  NominalDomain.not_losslessInterface model origin

example : ¬ Original.LosslessOperation NominalDomain.interface
    (.receive (.service "random.f/0") origin : NominalDomain.Operation model.toCarriers) :=
  NominalDomain.handleReceive_not_lossless model _ origin rfl

/-- Recursive products do not hide a service capability. -/
def nestedService : Ty := .sequence (.product "capability-record" "value"
  (.cons .boolean (.cons (.service "random.f/0") .nil)))

example : ¬ Original.LosslessOperation NominalDomain.interface
    (.receive nestedService origin : NominalDomain.Operation model.toCarriers) :=
  NominalDomain.handleReceive_not_lossless model _ origin rfl

example : SourceSupport.region PublicSourceSupport.operation
    (Region.letOp (.exchange nestedService 0 1 "capability") (.cons .here .nil) .nil
      (.ret (.cons .here .nil)) : Region protocolDialect [nestedService] [nestedService]) = false := rfl

/-- Recognizing a logical oracle sort grants no ordinary proof-message codec. -/
def logicalOracle : Ty := .oracle (.table (.field "koala-bear") (some 16))

example : ¬ Original.LosslessOperation NominalDomain.interface
    (.receive logicalOracle origin : NominalDomain.Operation model.toCarriers) :=
  NominalDomain.handleReceive_not_lossless model _ origin rfl

example : ¬ Original.LosslessOperation NominalDomain.interface
    (.receive (.sequence logicalOracle) origin : NominalDomain.Operation model.toCarriers) :=
  NominalDomain.handleReceive_not_lossless model _ origin rfl

/-- A claim-shaped product cannot acquire ordinary data transport for its anchor. -/
def oracleClaim : Ty := .product "oracle-claim" "claim"
  (.cons .boolean (.cons logicalOracle .nil))

example : ¬ Original.LosslessOperation NominalDomain.interface
    (.receive oracleClaim origin : NominalDomain.Operation model.toCarriers) :=
  NominalDomain.handleReceive_not_lossless model _ origin rfl

example : SourceSupport.region PublicSourceSupport.operation
    (Region.letOp (.exchange logicalOracle 0 1 "anchor") (.cons .here .nil) .nil
      (.ret (.cons .here .nil)) : Region protocolDialect [logicalOracle] [logicalOracle]) = false := rfl

/-- Every typed continuation is certified, including a branch that a chosen
example reply does not visit. No sampled-path assumption supplies authority. -/
def hiddenService : PIR.Process (NominalDomain.signature model.toCarriers) Unit :=
  .call (.receive .boolean origin) fun value =>
    if value then .done ()
    else .call (.receive (.service "random.f/0") origin) fun _ => .done ()

theorem hidden_service_refused : ¬ Original.LosslessOn NominalDomain.interface (hiddenService model origin) := by
  intro supported
  exact NominalDomain.handleReceive_not_lossless model _ origin rfl (supported.2 false).1

abbrev collapsedSignature : PIR.Signature := ⟨Unit, fun _ => Bool⟩

def collapsedReceive : Interface collapsedSignature (Domain.Event model.toCarriers)
    (Domain.Payload model.toCarriers) Domain.Raw :=
  fun _ => .receive (.message origin)
    (fun event => (NominalDomain.received .boolean origin event).map (fun _ => true))

/-- This decoder really accepts payloads, but collapses their Boolean replies.
A local certificate must reject it even when operation names look nominal. -/
theorem collapsed_receive_refused : ¬ Original.LosslessOperation (collapsedReceive model origin) () := by
  intro lossless
  have injective := (lossless.receive .boolean (.message origin) _ (fun _ => true) rfl
    (fun payload => by rw [NominalDomain.received_message])).1.injective
  have impossible : false = true := injective rfl
  cases impossible

/-- Wrong-sort decoder equations are refused even with equal host carriers. -/
theorem wrong_sort_refused (ty foreign : Ty) (data : ty.isHandle = false) (different : ty ≠ foreign) :
    ¬ ∃ reply : model.Value foreign → model.Value ty,
      ∀ payload : Domain.Payload model.toCarriers,
        NominalDomain.received ty origin (.message origin payload) = (payload.value foreign).map reply := by
  rintro ⟨reply, decoded⟩
  have impossible := decoded ⟨ty, data, NominalDomain.modelValue model ty⟩
  simp [NominalDomain.received_message, Domain.Payload.value, different] at impossible

/-- CompleteReturns still rejects altered residuals with identical acceptance. -/
example (accepted : Bool) (left right : model.Field "f") (changed : left ≠ right)
    (history : Domain.History model.toCarriers) :
    ¬ Original.CompleteReturns RootConnectionControls.signature RootConnectionControls.context 1
      RootConnectionControls.artifact (RootConnectionControls.source model accepted left history)
      (RootConnectionControls.result model accepted right history) :=
  RootConnectionControls.wrong_residual model accepted left right changed history

example (accepted : Bool) (residual : model.Field "f")
    (before reached : Domain.History model.toCarriers) (changed : before ≠ reached) :
    ¬ Original.CompleteReturns RootConnectionControls.signature RootConnectionControls.context 1
      RootConnectionControls.artifact (RootConnectionControls.source model accepted residual before)
      (RootConnectionControls.result model accepted residual reached) :=
  RootConnectionControls.wrong_history model accepted residual before reached changed

#print axioms NominalDomain.losslessOperation
#print axioms NominalDomain.handleReceive_not_lossless
#print axioms NominalDomain.not_losslessInterface
#print axioms hidden_service_refused
#print axioms collapsed_receive_refused
#print axioms wrong_sort_refused

end TestsSecurity.LosslessOperationRefusal
