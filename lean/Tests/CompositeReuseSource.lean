import Zkc.Source.Structured.UnitViews
import Zkc.Source.Structured.ContractComposition
import Tests.Generated.CompositeReuseData
import Tests.Generated.CompositeReuseBodies

/-! Exact admission of maintained source and its printer-owned typed bodies. -/
set_option autoImplicit false
set_option smartUnfolding false
namespace Tests.CompositeReuseSource
open Zkc.Source Zkc.Source.Structured
open Tests.Generated.CompositeReuseBodies

structured_views Tests.Generated.CompositeReuseData.snapshot
  helpers [] protocols [shift, outer, third]

end Tests.CompositeReuseSource
