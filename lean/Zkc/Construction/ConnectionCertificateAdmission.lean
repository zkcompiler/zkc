module

public import Zkc.Construction.ConnectionAdmission
public import Zkc.Construction.ConnectionRouteCoverageRoot

@[expose] public section

/-! Install a checked typed certificate at the method-independent source
boundary. The fixed meaning does not import this implementation adapter. -/
set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured ConnectionRoot

namespace SourceConnection
/-- Typed derivations are one way to establish the fixed connection meaning. -/
theorem ofRootCertificate {program : Program} {routing : Original.Routing} {role : Nat}
    {artifact : Participant} (root : RootCertificate program routing role artifact)
    (canonical : canonicalABI program role artifact = .ok root.inputs.abi) :
    Connected program routing role root.inputs.abi artifact where
  snapshot := root.snapshot
  roleValid := root.roleValid
  canonical := canonical
  coverage model physical := ⟨root.routeCoverage model physical⟩
  simulation model physical := ⟨root.simulation model physical⟩

end SourceConnection

namespace ConnectionAdmission
theorem ofRootCertificate {program : Program} {context : Context} {mode : Domain.Mode}
    {artifact : Participant} {routing : Original.Routing}
    (root : RootCertificate program routing (role context mode) artifact)
    (selected : select program context mode artifact = .ok ⟨root.inputs.abi, routing⟩) :
    Required program context mode artifact :=
  ofConnected selected (SourceConnection.ofRootCertificate root (select_canonical selected))

end ConnectionAdmission
end Zkc.Construction
