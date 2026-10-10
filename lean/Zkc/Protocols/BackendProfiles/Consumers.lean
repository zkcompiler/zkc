import Zkc.Protocols.BackendProfiles.Correctness
import Zkc.Protocols.BackendProfiles.Horner

set_option autoImplicit false

namespace Zkc.Protocols.BackendProfiles.Consumers
open Lean Zkc.Protocols.BackendProfiles Zkc.Compiler.Readback

variable {V A O S E : Type}

theorem scalar_program (literal : Zkc.Protocols.BackendProfiles.Literal → V) (truth : V → Bool)
    (env : Nat → V) (next : List V → Zkc.Compiler.Blocks.Program V A O) :
    nativeModule Zkc.Protocols.BackendProfiles.Certificates.scalarRequest literal truth env next =
      Zkc.Compiler.Blocks.moduleCall truth (embedBlock literal Zkc.Protocols.BackendProfiles.Certificates.scalarAnchor.body) Zkc.Protocols.BackendProfiles.Certificates.scalarAnchor.exports env next :=
  admitted_program Zkc.Protocols.BackendProfiles.Certificates.scalarAnchor Zkc.Protocols.BackendProfiles.Certificates.scalarJson Zkc.Protocols.BackendProfiles.Certificates.scalarAdmitted literal truth env next

theorem fri_program (literal : Zkc.Protocols.BackendProfiles.Literal → V) (truth : V → Bool)
    (env : Nat → V) (next : List V → Zkc.Compiler.Blocks.Program V A O) :
    nativeModule Zkc.Protocols.BackendProfiles.Certificates.friRequest literal truth env next =
      Zkc.Compiler.Blocks.moduleCall truth (embedBlock literal Zkc.Protocols.BackendProfiles.Certificates.friAnchor.body) Zkc.Protocols.BackendProfiles.Certificates.friAnchor.exports env next :=
  admitted_program Zkc.Protocols.BackendProfiles.Certificates.friAnchor Zkc.Protocols.BackendProfiles.Certificates.friJson Zkc.Protocols.BackendProfiles.Certificates.friAdmitted literal truth env next

-- A real upstream algebraic admission, followed by the new JSON certificate.
-- The representation checker itself does not establish this source relation.
theorem alias_source_refinement [Semiring V] [DecidableEq V]
    (literal : Zkc.Protocols.BackendProfiles.Literal → V) (truth : V → Bool)
    (handler : A → S → V × S × List E)
    (env : Nat → V) (next : List V → Zkc.Compiler.Blocks.Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Zkc.Compiler.Blocks.Key V) V → Zkc.Compiler.Blocks.Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Zkc.Compiler.Blocks.Key V) V)
    (valid : Zkc.Modules.ImmutableCache.Valid Zkc.Compiler.Blocks.arithmetic cache) :
    (Zkc.Transformations.Memoization.runMemo Zkc.Compiler.Blocks.arithmetic store cache
      (Zkc.Compiler.Blocks.lower handler (nativeModule Zkc.Protocols.BackendProfiles.Certificates.aliasAdmitted.request literal truth env next) s)).1 =
    Zkc.Compiler.Blocks.runProgram Zkc.Compiler.Blocks.arithmetic handler
      (Zkc.Compiler.Blocks.moduleCall truth Zkc.Protocols.BackendProfiles.Horner.source [8] env next) s := by
  exact Horner.alias_native_replacement literal truth handler env next s store cache valid


end Zkc.Protocols.BackendProfiles.Consumers
