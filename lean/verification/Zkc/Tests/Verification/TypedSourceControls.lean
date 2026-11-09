module

public import Zkc.Tests.Verification.TypedSourceReading

@[expose] public section

/-! Finite request, actual nominal decoder and private-route refusal controls. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option Elab.async false
namespace TestsSecurity.TypedSourceReading
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir Tests.IndexServices
variable {carriers : Carriers}

theorem scalar_data : PublicSourceSupport.check Scalar.program = true := by kernel_rfl

theorem block_data : PublicSourceSupport.check Block.program = true := by kernel_rfl

theorem repeated_data : PublicSourceSupport.check Repeated.program = true := by kernel_rfl


-- Keep the predicate's source parameter abstract while installing support;
-- elaborating the same concrete source as an expected recursive predicate
-- would eagerly evaluate its captured protocol table.
theorem supported_lossless (model : DomainModel) (routing : Original.Routing) {A : Type}
    (source : PIR.Process (Occurrence.signature model.toCarriers) A)
    (supported : OperationSupport PublicSourceSupport.sourceOperation source) :
    ZkcSecurity.FiatShamir.Original.LosslessOn NominalDomain.interface
      (DomainSourceReading.presentation routing source {}) :=
  PublicSourceSupport.lossless model routing source supported {}


/-- The checked actual source gets lossless support without assuming data
representation for arbitrary handle-bearing proof inputs. -/
theorem checked_lossless (model : DomainModel) (program : Program)
    (checked : PublicSourceSupport.check program = true) (routing : Original.Routing)
    (role : Nat) (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    ZkcSecurity.FiatShamir.Original.LosslessOn NominalDomain.interface
      (DomainSourceReading.presentation routing (Occurrence.participant model program role inputs) {}) :=
  supported_lossless model routing _ (PublicSourceSupport.participant program checked model role inputs)

-- Exact field specialization is retained at malformed origins too.
example (state : Original.State carriers) (origin : Origin) (field : String) :
    DomainSourceReading.queryRequest state origin (.draw field) =
      DomainSourceReading.queryField state origin field :=
  DomainSourceReading.queryRequest_draw state origin field

example (state : Original.State carriers) :
    DomainSourceReading.queryRequest state (Scalar.context.query "q" (.sampleIndex 8))
      (.sampleIndex 0) = .halt .refused := by kernel_rfl
example (state : Original.State carriers) :
    DomainSourceReading.queryRequest state (Scalar.context.query "q" (.sampleIndex 7))
      (.sampleIndex 8) = .halt .refused := by kernel_rfl
example (state : Original.State carriers) :
    DomainSourceReading.queryRequest state (Block.context.query "q" (.sampleIndices 8 2))
      (.sampleIndices 8 3) = .halt .refused := by kernel_rfl
example (state : Original.State carriers) :
    DomainSourceReading.queryRequest state { Scalar.context.query "q" (.sampleIndex 8) with request := none }
      (.sampleIndex 8) = .halt .refused := by kernel_rfl
example (state : Original.State carriers) :
    DomainSourceReading.service (Scalar.routing .validator) state "label_706f736974696f6e"
      "other.contract" (.sampleIndex 8) 17 = .halt .refused := by kernel_rfl
example (state : Original.State carriers) :
    DomainSourceReading.service (Scalar.routing .validator) state "label_706f736974696f6e"
      contract (.sampleIndex 8) 18 = .halt .refused := by kernel_rfl

-- A mismatched closing boundary refuses rather than losing the reached frame.
example (state : Original.State carriers) :
    DomainSourceReading.operations (Scalar.routing .validator) (.leave ⟨"wrong", 0⟩)
      { state with frames := [⟨"actual", 1⟩] } = .halt .refused := by kernel_rfl

-- Actual finite decoding retains ranges and exact ordered block length.
example (bound : Nat) (positive : 0 < bound) (raw : Fin (Request.replyBound bound)) :
    raw.val < bound := by simpa only [Request.replyBound_of_positive positive] using raw.isLt
example (bound count : Nat) (raw : Fin count → Fin (Request.replyBound bound)) :
    (List.ofFn fun i => (raw i).val).length = count := Request.decoded_block_count bound count raw

-- Equal host carriers do not confer nominal equality, even recursively.
example (model : DomainModel) (origin : Origin) :
    NominalDomain.received (carriers := model.toCarriers) (.polynomial "second") origin
      (.message origin ⟨.polynomial "first", rfl, NominalDomain.modelValue model _⟩) = none :=
  NominalDomain.received_wrong_type _ _ _ (by
    change (Ty.polynomial "first") ≠ Ty.polynomial "second"
    decide)
example (model : DomainModel) (origin : Origin) :
    ¬ ZkcSecurity.FiatShamir.Original.LosslessOperation NominalDomain.interface
      (.receive (.sequence (.service "private")) origin : NominalDomain.Operation model.toCarriers) :=
  NominalDomain.handleReceive_not_lossless model _ origin rfl

-- The local source route is real, but this public presentation must refuse it.
def privateRouting : Original.Routing :=
  ⟨Local.Source.snapshot, Local.context, .producer, 17, [], [], [],
    [⟨31, Local.port, Local.template⟩]⟩
example : privateRouting.locals ≠ [] := by decide +kernel
example (state : Original.State carriers) :
    DomainSourceReading.service privateRouting state "s0" contract (.sampleIndex 3) 31 =
      .halt .refused := by kernel_rfl
example : privateRouting.localRequest [] "s0" (.sampleIndex 3) 31 ≠ none := by decide +kernel

example (state : Original.State carriers) :
    DomainSourceReading.queryRequest state (Scalar.context.query "q" (.sampleIndex 8))
      ⟨"indices", [8], .index⟩ = .halt .refused := by kernel_rfl
example (state : Original.State carriers) :
    DomainSourceReading.receiveRequest (Block.routing .producer) state .index
      "label_64656c6976657279_0" 1 = .halt .refused := by kernel_rfl
example (model : DomainModel) (expected actual : Origin) (different : actual ≠ expected) :
    NominalDomain.received (carriers := model.toCarriers) .index expected
      (.message actual (.index 3)) = none :=
  NominalDomain.received_wrong_origin _ expected actual _ different

end TestsSecurity.TypedSourceReading
