module

public import ZkcSecurity.Realizations.Gkr.RootSource
public import ZkcExamples.Construction.GkrProof

public section
noncomputable section

/-! Exact compiled execution transports through the same current source body
as the all-input root soundness theorem. -/
namespace ZkcSecurity.Realizations.Gkr.Source
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open ZkcExamples.Structured ZkcExamples.Construction
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Current compiled execution is already connected to this source body.
No well-formedness premise is needed until the mathematical reading is used. -/
theorem compiled_binding {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (runtime : Invocation F) (initial : History F G) (proof : Proof F G) :
    GkrProof.compiledVerifier challenge runtime.inputs runtime.outputs runtime.add runtime.mul
      runtime.layers runtime.selector runtime.width initial proof =
      transform GkrProof.context challenge (body runtime) initial proof := by
  simpa only [GkrProof.verifier, GkrProof.process, GkrProof.verifierInputs,
    body, actualVerifier, GkrSourceAdmission.participant, GkrSourceAdmission.inputs,
    GkrSourceProtocol.sourceVerifier, GkrSourceProtocol.sourceInputs] using
    GkrProof.compiled_transform challenge runtime.inputs runtime.outputs runtime.add runtime.mul
      runtime.layers runtime.selector runtime.width runtime.handle initial proof


end ZkcSecurity.Realizations.Gkr.Source
