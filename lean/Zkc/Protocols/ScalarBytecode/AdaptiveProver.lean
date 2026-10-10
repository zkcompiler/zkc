import Zkc.Protocols.ScalarBytecode.Parameters
import Zkc.Source.MessageSchema
import Zkc.Source.LocalArithmetic

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.AdaptiveProver
def inv2 : Nat := 1152921504606848625
def b0 (r : Nat) : Nat := ((2*r+1)*inv2)%Zkc.Protocols.ScalarBytecode.Parameters.modulus
def view (r : Nat) : Zkc.Source.LocalArithmetic.View := fun k => if k = 2 then some r else none
def program : Zkc.Source.LocalArithmetic.Program :=
  .emit (.mod (.mul (.add (.mul (.lit 2) (.input 2)) (.lit 1)) (.lit inv2)) Zkc.Protocols.ScalarBytecode.Parameters.modulus)
    (.emit (.input 2) (.emit (.lit 0) .done))
def context : Zkc.Source.MessageSchema.Contract := ⟨10,20,30,Zkc.Protocols.ScalarBytecode.Parameters.modulus,2,1,3⟩
def raw (r : Nat) : Zkc.Source.MessageSchema.Raw := ⟨10,20,30,1,[b0 r,r,0]⟩

theorem block_run (r : Nat) (m : Zkc.Source.LocalArithmetic.Memory) :
    Zkc.Source.LocalArithmetic.checkedRun program (view r) m = some ⟨(raw r).values,m⟩ := by
  simp [Zkc.Source.LocalArithmetic.checkedRun, Zkc.Source.LocalArithmetic.Program.check, Zkc.Source.LocalArithmetic.Expr.check, Zkc.Source.LocalArithmetic.Program.eval,
    Zkc.Source.LocalArithmetic.Expr.eval, program, view, raw, b0]

theorem output_valid (r : Nat) (hr : r < Zkc.Protocols.ScalarBytecode.Parameters.modulus) : Zkc.Source.MessageSchema.Valid context (raw r) := by
  have hb : b0 r < Zkc.Protocols.ScalarBytecode.Parameters.modulus := Nat.mod_lt _ (by decide : 0 < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
  simp only [Zkc.Protocols.ScalarBytecode.Parameters.modulus] at hb hr
  simp [Zkc.Source.MessageSchema.Valid, context, raw, Zkc.Protocols.ScalarBytecode.Parameters.modulus, hb, hr]

-- The output of the Zkc.Source.LocalArithmetic block is now connected to the actual T5 checker,
-- for every canonical challenge representative, without an honest premise.
theorem checked_egress (r : Nat) (hr : r < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (m : Zkc.Source.LocalArithmetic.Memory) :
    Zkc.Source.LocalArithmetic.checkedRun program (view r) m = some ⟨(raw r).values,m⟩ ∧
    Zkc.Source.MessageSchema.check context (raw r) = some ⟨raw r,output_valid r hr⟩ := by
  exact ⟨block_run r m,Zkc.Source.MessageSchema.check_complete context (raw r) (output_valid r hr)⟩

end Zkc.Protocols.ScalarBytecode.AdaptiveProver
