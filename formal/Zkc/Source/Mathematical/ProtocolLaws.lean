import Zkc.Source.Mathematical.ProtocolMeaning

/-! Local equations for canonical graph/protocol meaning.

These laws unfold the intrinsic interpreter itself. They apply to an admitted
installed vocabulary without replacing its program, operation meanings or wire
reply carriers. A whole-program placement theorem requires additional work.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Protocol
open Zkc.Source

variable {Role : Type} [DecidableEq Role] {vocabulary : Vocabulary}
  {parties : List Role} {capabilities : List (Capability Role vocabulary.Service)}
  {scope : List (Signature Role vocabulary)}
  (meaning : Graph.Interpretation vocabulary.toAlgebra)

theorem Program.denote_pure (self : Role) (calls : CallMeaning (capabilities := capabilities) meaning self scope)
    (path : List LocatedExecution.Frame) {Γ results captures outputs start finish}
    (capture : Operands Γ captures) (region : Graph.Region parties vocabulary.toAlgebra captures outputs)
    (next : Program parties vocabulary capabilities scope (outputs ++ Γ) results start finish)
    (env : Environment meaning.Value self Γ) :
    (Program.pure capture region next).denote meaning self calls path env =
      next.denote meaning self calls path
        (env.prepend (region.denote meaning self (fun v => (Operands.eval env capture).get v))) := rfl

/-- At the receiver, the next environment contains the arbitrary wire reply.
The sender expression is neither evaluated nor substituted for that reply. -/
theorem Program.denote_receive {Γ results ty site finish}
    (schema : vocabulary.Wire ty) (sender receiver : Role)
    (sending : sender ∈ parties) (receiving : receiver ∈ parties) (different : sender ≠ receiver)
    (value : Reference Γ ⟨[sender], ty⟩)
    (next : Program parties vocabulary capabilities scope
      (⟨messageRoles parties sender receiver, ty⟩ :: Γ) results (site + 1) finish)
    (calls : CallMeaning (capabilities := capabilities) meaning receiver scope)
    (path : List LocatedExecution.Frame) (env : Environment meaning.Value receiver Γ) :
    (Program.message schema sender receiver sending receiving different value next).denote
      meaning receiver calls path env =
        .call (.receive ⟨path, site⟩ schema sender) (fun reply =>
          next.denote meaning receiver calls path (env.push (fun _ => reply))) := by
  simp only [Program.denote, Program.denoteChecked, dif_neg (Ne.symm different), dite_true]

/-- A query keeps its exact root and location, even if another occurrence
returns the same value. -/
theorem Program.denote_query {Γ results signature site finish}
    (owner : Role) (participates : owner ∈ parties) (capability : Var capabilities signature)
    (permitted : owner ∈ signature.roles)
    (arguments : Inputs Γ (vocabulary.serviceArguments signature.service))
    (available : owner ∈ Inputs.available parties arguments)
    (next : Program parties vocabulary capabilities scope
      (⟨[owner], vocabulary.serviceResult signature.service⟩ :: Γ) results (site + 1) finish)
    (calls : CallMeaning (capabilities := capabilities) meaning owner scope)
    (path : List LocatedExecution.Frame) (env : Environment meaning.Value owner Γ) :
    (Program.query owner participates capability permitted arguments available next).denote
      meaning owner calls path env =
        .call (.query ⟨path, site⟩ signature.root signature.service
          (Inputs.read parties arguments env available)) (fun reply =>
            next.denote meaning owner calls path (env.push (fun _ => reply))) := by
  simp only [Program.denote, Program.denoteChecked, dite_true]

end Zkc.Source.Mathematical.Protocol
