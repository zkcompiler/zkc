import Zkc.Protocols.ScalarBytecode.Messages

set_option autoImplicit false

namespace Tests.ScalarBytecode.Messages
open Zkc.Source.PublicDimensions Zkc.Protocols.AlgebraicRounds.ParameterFamily Zkc.Protocols.ScalarBytecode.Messages

-- Public rounds and degree actually change the instance and payload width.
example : sumcheckFamily.inst (env2 2 2) = ⟨2,2⟩ := by decide
example : sumcheckFamily.inst (env2 4 3) = ⟨4,3⟩ := by decide
example : sumcheckFamily.inst (env2 2 2) ≠ sumcheckFamily.inst (env2 4 3) := by decide

end Tests.ScalarBytecode.Messages
