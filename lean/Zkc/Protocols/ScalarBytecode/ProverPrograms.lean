import Zkc.Protocols.ScalarBytecode.Codec
import Zkc.Protocols.ScalarBytecode.AdaptiveProver

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.ProverPrograms
/-- Fixed source identity, domain bytes and two supplied local programs. No native extraction correctness is claimed. -/
def sourceASCII : Zkc.Realization.ByteEncoding.Bytes := [⟨115, by decide⟩,⟨104, by decide⟩,⟨97, by decide⟩,⟨50, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩,⟨58, by decide⟩,⟨53, by decide⟩,⟨51, by decide⟩,⟨51, by decide⟩,⟨55, by decide⟩,⟨100, by decide⟩,⟨101, by decide⟩,⟨99, by decide⟩,⟨50, by decide⟩,⟨50, by decide⟩,⟨52, by decide⟩,⟨49, by decide⟩,⟨101, by decide⟩,⟨102, by decide⟩,⟨53, by decide⟩,⟨48, by decide⟩,⟨57, by decide⟩,⟨99, by decide⟩,⟨100, by decide⟩,⟨101, by decide⟩,⟨49, by decide⟩,⟨100, by decide⟩,⟨54, by decide⟩,⟨55, by decide⟩,⟨48, by decide⟩,⟨56, by decide⟩,⟨56, by decide⟩,⟨51, by decide⟩,⟨57, by decide⟩,⟨49, by decide⟩,⟨56, by decide⟩,⟨101, by decide⟩,⟨48, by decide⟩,⟨48, by decide⟩,⟨52, by decide⟩,⟨48, by decide⟩,⟨102, by decide⟩,⟨51, by decide⟩,⟨99, by decide⟩,⟨100, by decide⟩,⟨97, by decide⟩,⟨52, by decide⟩,⟨51, by decide⟩,⟨52, by decide⟩,⟨99, by decide⟩,⟨98, by decide⟩,⟨101, by decide⟩,⟨52, by decide⟩,⟨48, by decide⟩,⟨55, by decide⟩,⟨100, by decide⟩,⟨102, by decide⟩,⟨100, by decide⟩,⟨50, by decide⟩,⟨52, by decide⟩,⟨57, by decide⟩,⟨98, by decide⟩,⟨99, by decide⟩,⟨100, by decide⟩,⟨57, by decide⟩,⟨97, by decide⟩,⟨51, by decide⟩,⟨102, by decide⟩,⟨100, by decide⟩,⟨97, by decide⟩]
def domainASCII : Zkc.Realization.ByteEncoding.Bytes := [⟨115, by decide⟩,⟨117, by decide⟩,⟨109, by decide⟩,⟨99, by decide⟩,⟨104, by decide⟩,⟨101, by decide⟩,⟨99, by decide⟩,⟨107, by decide⟩,⟨46, by decide⟩,⟨99, by decide⟩,⟨49, by decide⟩]
def honestFirst : List Nat := [0, 3, 0]
def honestProgram : Zkc.Source.LocalArithmetic.Program := .emit (.input 2) (.emit (.input 2) (.emit (.lit 0) (.done)))
def cheatFirst : List Nat := [1, 3, 0]
def cheatProgram : Zkc.Source.LocalArithmetic.Program := .emit (.mod (.mul (.add (.mul (.lit 2) (.input 2)) (.lit 1)) (.lit 1152921504606848625)) 2305843009213697249) (.emit (.input 2) (.emit (.lit 0) (.done)))
theorem adaptive_program_exact : cheatProgram = Zkc.Protocols.ScalarBytecode.AdaptiveProver.program := rfl
theorem honest_meaning (r : Nat) (m : Zkc.Source.LocalArithmetic.Memory) : Zkc.Source.LocalArithmetic.checkedRun honestProgram (Zkc.Protocols.ScalarBytecode.AdaptiveProver.view r) m = some ⟨[r,r,0],m⟩ := by
  simp [Zkc.Source.LocalArithmetic.checkedRun, Zkc.Source.LocalArithmetic.Program.check, Zkc.Source.LocalArithmetic.Expr.check, Zkc.Source.LocalArithmetic.Program.eval, Zkc.Source.LocalArithmetic.Expr.eval, honestProgram, Zkc.Protocols.ScalarBytecode.AdaptiveProver.view]

end Zkc.Protocols.ScalarBytecode.ProverPrograms
