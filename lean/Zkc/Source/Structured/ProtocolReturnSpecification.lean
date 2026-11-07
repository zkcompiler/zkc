module

public import Zkc.Source.Structured.ProtocolDerivation
public import Zkc.Source.RegionReturnProjection

@[expose] public section

/-! Install a successful-return specification at a linked protocol declaration.
The source supplies both boundary masks and the captured call table. The rule
preserves stopped records and does not assert termination or losslessness. -/
set_option autoImplicit false
namespace Zkc.Source.Structured
attribute [local implicit_reducible] CheckedProtocol.signature
variable {V : Ty → Type} {I : PIR.Signature}
  {M : Type → Type} [Monad M] [LawfulMonad M] {S E : Type}
  {handler : PIR.MonadHandler M I S E} {invariant : S → Prop}

/-- The body law describes its unmasked result. The declaration owns the
output mask, just as it owns the mask on the inputs supplied to that law. -/
theorem ProtocolAlgebra.invokeReturns (algebra : ProtocolAlgebra V I)
    {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (definition : CheckedProtocol) (member : definition ∈ definitions)
    (context : ProtocolContext) (self : Nat) (args : Values (Component V) definition.inputs)
    (expected : Values (Component V) definition.outputs)
    (body : Region.ReturnsSatisfying handler invariant
      (algebra.meaning (definitions.foldl algebra.extend []) context self) definition.body
      (maskValues self (context.mapScopes definition.inputScopes) args).get
      (fun out ↦ out = expected)) :
    PIR.Process.ReturnsUnder handler invariant
      (invokeProtocol (definitions.foldl algebra.extend []) definition.signature context self args)
      (maskValues self (context.mapScopes definition.outputScopes) expected) := by
  rw [algebra.invokeBody linked definition member]
  unfold ProtocolAlgebra.denote
  rw [NormalForm.normalizeActions_process]
  exact PIR.Process.ReturnsUnder.bind body (PIR.Process.ReturnsUnder.done _)

end Zkc.Source.Structured
