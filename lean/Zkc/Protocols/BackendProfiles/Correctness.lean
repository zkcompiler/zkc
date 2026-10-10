import Zkc.Protocols.BackendProfiles.Admission
import Zkc.Protocols.BackendProfiles.Compilation

set_option autoImplicit false

namespace Zkc.Protocols.BackendProfiles
open Lean (Json)
open Zkc.Realization.JsonArrays Zkc.Compiler.Readback

variable {V A O : Type}

-- This is about the actual indexed JSON value. No premise that an arbitrary
-- schema parser is correct occurs in the statement or its proof.
theorem admitted_program (a : Anchor) (raw : Json) (p : Admitted a raw)
    (literal : Zkc.Protocols.BackendProfiles.Literal → V) (truth : V → Bool) (env : Nat → V)
    (next : List V → Zkc.Compiler.Blocks.Program V A O) :
    nativeModule p.request literal truth env next =
      Zkc.Compiler.Blocks.moduleCall truth (embedBlock literal a.body) a.exports env next := by
  have h := accepted_facts a raw p.label p.request p.checked
  have hb : p.request.expected = a.body := congrArg Anchor.body h.2.2.1.symm
  have he : p.request.expectedExports = a.exports := congrArg Anchor.exports h.2.2.1.symm
  rw [accepted_program p.request h.2.2.2, hb, he]

theorem admitted_interpretation (a : Anchor) (raw : Json) (p : Admitted a raw) :
    raw = toJson (requestWire p.label p.request) ∧
    p.label = a.occurrence ∧ p.request.profile = a.profile ∧
    p.request.inputs = a.inputs := by
  have h := accepted_facts a raw p.label p.request p.checked
  exact ⟨accepted_representation a raw p.label p.request p.checked,
    congrArg Anchor.occurrence h.2.2.1.symm,
    congrArg Anchor.profile h.2.2.1.symm,
    congrArg Anchor.inputs h.2.2.1.symm⟩

-- Equality can be consumed by any specified interpreter/observer, including
-- one that retains logical call order or failures. It says nothing about a
-- physical observation omitted by that interpretation.
theorem admitted_observation {X : Type} (a : Anchor) (raw : Json) (p : Admitted a raw)
    (literal : Zkc.Protocols.BackendProfiles.Literal → V) (truth : V → Bool) (env : Nat → V)
    (next : List V → Zkc.Compiler.Blocks.Program V A O) (observe : Zkc.Compiler.Blocks.Program V A O → X) :
    observe (nativeModule p.request literal truth env next) =
      observe (Zkc.Compiler.Blocks.moduleCall truth (embedBlock literal a.body) a.exports env next) :=
  congrArg observe (admitted_program a raw p literal truth env next)

end Zkc.Protocols.BackendProfiles
