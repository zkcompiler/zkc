import Zkc.Protocols.ScalarBytecode.AdaptiveProver
import Tests.ScalarBytecode.HonestPolynomial
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Tests.ScalarBytecode.AdaptiveProver
open Zkc.Protocols.ScalarBytecode.AdaptiveProver

def actualR : Nat := 829048626563406359
def schema : Zkc.Source.MessageSchema.Schema := ⟨10,20,30,Zkc.Protocols.ScalarBytecode.Parameters.modulus,.param 0,.add (.param 1) (.lit 1)⟩
example : Zkc.Source.MessageSchema.form schema [2,2] 1 = some context := by decide

def badProgram : Zkc.Source.LocalArithmetic.Program := .emit (.input 2) (.emit (.input 2) (.emit (.lit Zkc.Protocols.ScalarBytecode.Parameters.modulus) .done))
def badRaw : Zkc.Source.MessageSchema.Raw := ⟨10,20,30,1,[1654834368763198252,1654834368763198252,Zkc.Protocols.ScalarBytecode.Parameters.modulus]⟩
example : (Zkc.Source.LocalArithmetic.checkedRun badProgram (view 1654834368763198252) []).isSome = true := by decide
example : Zkc.Source.MessageSchema.check context badRaw = none := by decide
example : ((Zkc.Protocols.ScalarBytecode.Parameters.modulus : Nat) : ZMod Zkc.Protocols.ScalarBytecode.Parameters.modulus) = 0 := by simp
example : b0 actualR = 1981970131170254984 := by decide

-- Exact frozen cheat arithmetic: local consistency is weaker than final truth.
example : Tests.ScalarBytecode.HonestPolynomial.round2 (F := ZMod Zkc.Protocols.ScalarBytecode.Parameters.modulus) 1 3 0 actualR (b0 actualR) actualR 0 := by
  unfold Tests.ScalarBytecode.HonestPolynomial.round2
  decide

-- Removing only the first equation in a MODEL admits the adapted honest shape
-- for any later challenge; this is not an admitted source mutation.
example (r t : ZMod Zkc.Protocols.ScalarBytecode.Parameters.modulus) : Tests.ScalarBytecode.HonestPolynomial.round2 0 3 0 r r r 0 ∧ Tests.ScalarBytecode.HonestPolynomial.final r r 0 r t :=
  (Tests.ScalarBytecode.HonestPolynomial.actual_honest_checks r t).2

-- What the adapted shape sends when the challenge is the one it was fitted
-- to: every coordinate is that challenge until the final one.
#guard (Zkc.Source.LocalArithmetic.checkedRun badProgram (view 1654834368763198252) []).map (·.sent) =
  some [1654834368763198252, 1654834368763198252, 2305843009213697249]

-- What the honest program sends on the actual challenge.
#guard (Zkc.Source.LocalArithmetic.checkedRun program (view actualR) []).map (·.sent) =
  some [1981970131170254984, 829048626563406359, 0]

end Tests.ScalarBytecode.AdaptiveProver
