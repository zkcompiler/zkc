import Zkc.Protocols.BackendProfiles.Certificates
import Zkc.Protocols.BackendProfiles.Compilation

set_option autoImplicit false

namespace Zkc.Protocols.BackendProfiles.Horner
open Zkc.Compiler.Readback Zkc.Protocols.BackendProfiles

-- One new target accepted by Zkc.Compiler.Blocks's unchanged Horner law checker: the alias
-- changes the native/SSA shape and needs a new instance, not a new law.
def source {V : Type} : Zkc.Compiler.Blocks.Block V :=
  [(4,.apply "field.mul" (.input 1) (.input 3)),
   (5,.apply "field.mul" (.input 3) (.input 3)),
   (6,.apply "field.mul" (.input 2) (.input 5)),
   (7,.apply "field.add" (.input 4) (.input 6)),
   (8,.apply "field.add" (.input 0) (.input 7))]

theorem alias_law {F : Type} [Semiring F] [DecidableEq F]
    (literal : Literal → F) (truth : F → Bool) :
    Zkc.Compiler.Blocks.EquivalentOn Zkc.Compiler.Blocks.arithmetic truth (fun _ => True) source
      (embedBlock literal Zkc.Protocols.BackendProfiles.Certificates.aliasRequest.expected) [8] [8] := by
  apply Zkc.Compiler.Blocks.checked_horner
  rfl

theorem alias_native_replacement {F A O S E : Type} [Semiring F] [DecidableEq F]
    (literal : Literal → F) (truth : F → Bool)
    (handler : A → S → F × S × List E) (env : Nat → F)
    (next : List F → Zkc.Compiler.Blocks.Program F A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Zkc.Compiler.Blocks.Key F) F → Zkc.Compiler.Blocks.Key F → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Zkc.Compiler.Blocks.Key F) F) (valid : Zkc.Modules.ImmutableCache.Valid Zkc.Compiler.Blocks.arithmetic cache) :
    (Zkc.Transformations.Memoization.runMemo Zkc.Compiler.Blocks.arithmetic store cache
      (Zkc.Compiler.Blocks.lower handler (nativeModule Zkc.Protocols.BackendProfiles.Certificates.aliasRequest literal truth env next) s)).1 =
      Zkc.Compiler.Blocks.runProgram Zkc.Compiler.Blocks.arithmetic handler (Zkc.Compiler.Blocks.moduleCall truth source [8] env next) s := by
  exact accepted_replacement Zkc.Protocols.BackendProfiles.Certificates.aliasRequest Zkc.Protocols.BackendProfiles.Certificates.alias_readback_checked literal truth Zkc.Compiler.Blocks.arithmetic handler
    source [8] (fun _ => True) (alias_law literal truth) env trivial next s store cache valid

end Zkc.Protocols.BackendProfiles.Horner
