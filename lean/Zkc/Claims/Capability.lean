module

public import Zkc.Claims.Registry

@[expose] public section

/-! Capabilities are separate typed exports, not a prerequisite of every
ordinary proposition. Their validity predicate is published by the registry. -/

set_option autoImplicit false
namespace Zkc.Claims
universe u v

structure Capability (Meaning : Type u) where
  Payload : Type v
  Valid : Payload → Meaning → Prop

structure Capability.Export {Meaning : Type u} (capability : Capability.{u, v} Meaning) (meaning : Meaning) where
  payload : capability.Payload
  proof : capability.Valid payload meaning

end Zkc.Claims
