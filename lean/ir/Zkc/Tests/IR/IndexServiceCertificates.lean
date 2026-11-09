module

public import Zkc.Tests.IR.IndexServices
public import Zkc.Tools.IR.ConstructionBindings.Admission

@[expose] public section

/-! Whole-root typed service certificates for the retained tiny source roots.
All proposals are checked through the existing public connection boundary. -/
-- Whole-root connection proposals retain large kernel terms. Check the roots
-- in source order so independent proofs do not compete for memory.
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace Tests.IndexServices
open Zkc.Source Zkc.Source.Structured Zkc.Construction

namespace Scalar
theorem validator_connected : ConnectionAdmission.Required program context .validator Validator.participant := by
  derive_source_connection
theorem producer_connected : ConnectionAdmission.Required program context .producer Producer.participant := by
  derive_source_connection
end Scalar
namespace Block
theorem validator_connected : ConnectionAdmission.Required program context .validator Validator.participant := by
  derive_source_connection
theorem producer_connected : ConnectionAdmission.Required program context .producer Producer.participant := by
  derive_source_connection
end Block
namespace Local
theorem validator_connected : ConnectionAdmission.Required program context .validator Validator.participant := by
  derive_source_connection
theorem producer_connected : ConnectionAdmission.Required program context .producer Producer.participant := by
  derive_source_connection
end Local
namespace Repeated
theorem validator_connected : ConnectionAdmission.Required program context .validator Validator.participant := by
  derive_source_connection
theorem producer_connected : ConnectionAdmission.Required program context .producer Producer.participant := by
  derive_source_connection
end Repeated
end Tests.IndexServices
