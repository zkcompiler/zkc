module

@[expose] public section

namespace Zkc.Frontend

/-- A projection of an opaque type can be checked at the concrete instantiation (SP12). -/
inductive WaitReason where
  | message (text : String)
  | context (description : String) (cause : WaitReason)
  | opaqueProjection
  deriving Inhabited, BEq, Repr

instance : Coe String WaitReason := ⟨WaitReason.message⟩

def WaitReason.render : WaitReason → String
  | .context description cause => s!"{description}: {cause.render}"
  | .message text => text
  | .opaqueProjection => "a type member of a type member of a module parameter, in the opaque typing (SP12)"

instance : ToString WaitReason := ⟨WaitReason.render⟩

/-- Whether the computation must be repeated at the concrete module. -/
def WaitReason.isOpaqueProjection : WaitReason → Bool
  | .opaqueProjection => true
  | .context _ cause => cause.isOpaqueProjection
  | .message _ => false

end Zkc.Frontend
