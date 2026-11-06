module

public import Tests.IndexServicesExecution
public import ZkcSecurity.Bindings.Transcript.PublicSourceSupport

@[expose] public section

/-! Controls for the ordinary typed-service source presentation. The tiny roots
are retained actual source exports. These checks do not install Oracle source
semantics, a probability model, or whole-root connection certificates. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option Elab.async false
namespace TestsSecurity.TypedSourceReading
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir
open Tests.IndexServices

variable {carriers : Carriers}

/-- The installed law covers every source result and reply-dependent suffix,
including stopped suffixes and nonempty initial frames/history. -/
theorem arbitrary_continuation {A : Type} (routing : Original.Routing)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = []) (site : String) (operation : ServiceOp)
    (arguments : Values carriers.Value operation.arguments)
    (next : carriers.Value operation.result → PIR.Process (Occurrence.signature carriers) A)
    (state : Original.State carriers) :
    DomainReduction.Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.fold routing (.call (.action (.query site operation arguments)) next) state)
      (DomainSourceReading.presentation routing
        (.call (.action (.query site operation arguments)) next) state) :=
  DomainSourceReading.reading routing replacement profile noLocal _ state

def scalarReplacement : Replacement := Scalar.context.replacement?.get (by decide +kernel)
def blockReplacement : Replacement := Block.context.replacement?.get (by decide +kernel)

theorem scalar_reading (model : DomainModel) (mode : Domain.Mode) (role : Nat)
    (inputs : Values (Component model.Value) Scalar.program.payload.entry.inputs)
    (state : Original.State model.toCarriers) :
    DomainReduction.Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.fold (Scalar.routing mode) (Occurrence.participant model Scalar.program role inputs) state)
      (DomainSourceReading.presentation (Scalar.routing mode)
        (Occurrence.participant model Scalar.program role inputs) state) :=
  DomainSourceReading.reading (Scalar.routing mode) scalarReplacement (by kernel_rfl) rfl _ state

theorem block_reading (model : DomainModel) (mode : Domain.Mode) (role : Nat)
    (inputs : Values (Component model.Value) Block.program.payload.entry.inputs)
    (state : Original.State model.toCarriers) :
    DomainReduction.Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.fold (Block.routing mode) (Occurrence.participant model Block.program role inputs) state)
      (DomainSourceReading.presentation (Block.routing mode)
        (Occurrence.participant model Block.program role inputs) state) :=
  DomainSourceReading.reading (Block.routing mode) blockReplacement (by kernel_rfl) rfl _ state


/-- Exact endpoint equality includes the entire source output, frames/history,
all refusal outcomes and the unread proof suffix, for every monadic provider. -/
theorem scalar_endpoint (model : DomainModel) (mode : Domain.Mode) (role : Nat)
    (inputs : Values (Component model.Value) Scalar.program.payload.entry.inputs)
    (state : Original.State model.toCarriers) {m : Type → Type} [Monad m]
    (query : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      m (Domain.Raw event)) (proof : Domain.Proof model.toCarriers) :
    ZkcSecurity.Endpoint.Domain.readExecution (carriers := model.toCarriers) query
      (Original.fold (Scalar.routing mode) (Occurrence.participant model Scalar.program role inputs) state)
      proof =
    transform (NominalDomain.interface (carriers := model.toCarriers)) query
      (DomainSourceReading.presentation (Scalar.routing mode)
        (Occurrence.participant model Scalar.program role inputs) state) state.history proof :=
  DomainSourceReading.endpoint (carriers := model.toCarriers)
    (A := Values (Component model.Value) Scalar.program.payload.entry.outputs) (m := m)
    (Scalar.routing mode) scalarReplacement (by kernel_rfl) rfl
    (Occurrence.participant model Scalar.program role inputs) state query proof

end TestsSecurity.TypedSourceReading
