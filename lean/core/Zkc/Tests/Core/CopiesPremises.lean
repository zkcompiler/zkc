import Zkc.Tests.Core.Copies
import Zkc.Tests.Core.Reflexivity
import Zkc.Core.Admission

/-! The premises of the theorem of the check of copies, on programs.

The theorem (`Admitted.protocols_cohere`): a protocol that passes the check, at a
side that supports its requirements and on arguments of which its input agreements hold, never
stops `incomplete`. For an arbitrary model the kernel evaluates three programs of
`Zkc/Tests/Core/Copies.lean`:

- `agreedChoice` passes the check and is admitted. On two equal flags it returns. On two
  different flags, of which its input agreement does not hold, it stops `incomplete`: the
  premise on the arguments is needed.
- `apartChoice` is refused by the check, and on two different flags it stops `incomplete`:
  what the check refuses is a program that stops.
- `relayed` passes the check, and the side of roles 1 and 2 does not support its requirement
  (`relayed_receivers`). For that side the count of role 1 is received from outside it; when
  it is the count of role 2 the loop runs, and when it differs the side stops `incomplete`:
  the premise on the side is needed.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace CopiesPremises

open CopiesTests

kernel_refl agreed_elaborates : (elaborate agreedChoice).isOk equals true
kernel_refl agreed_admitted : (admit agreedChoice).isOk equals true
noncomputable def agreedElaborated : Typed := Typed.ofRaw agreedChoice agreed_elaborates
typed_literal agreedTyped := agreedElaborated

kernel_refl apart_elaborates : (elaborate apartChoice).isOk equals true
kernel_refl apart_refused : (admit apartChoice).isOk equals false
noncomputable def apartElaborated : Typed := Typed.ofRaw apartChoice apart_elaborates
typed_literal apartTyped := apartElaborated

kernel_refl relayed_elaborates : (elaborate relayed).isOk equals true
noncomputable def relayedElaborated : Typed := Typed.ofRaw relayed relayed_elaborates
typed_literal relayedTyped := relayedElaborated

abbrev agreedProtocol :
    Var agreedTyped.protocols
      ⟨2, [⟨.bool, 0⟩, ⟨.bool, 1⟩], [],
        ⟨[⟨.bool, ⟨0, ⟨0, rfl⟩⟩, [⟨1, ⟨1, rfl⟩⟩]⟩], []⟩, false⟩ :=
  ⟨0, rfl⟩

abbrev apartProtocol :
    Var apartTyped.protocols ⟨2, [⟨.bool, 0⟩, ⟨.bool, 1⟩], [], .none, false⟩ :=
  ⟨0, rfl⟩

abbrev relayedProtocol : Var relayedTyped.protocols ⟨3, [], [], .none, false⟩ := ⟨0, rfl⟩

/-- The meaning of a protocol of a typed package for a side. -/
noncomputable abbrev meaning (model : Model) (typed : Typed) {header : ProtocolHeader}
    (protocol : Var typed.protocols header) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get protocol []

abbrev both : Side := fun _ => true
abbrev receivers : Side := fun role => Nat.beq role 1 || Nat.beq role 2

theorem agreed_together (model : Model) :
    meaning model agreedTyped agreedProtocol both (.cons true (.cons true .nil)) = .done .nil :=
  kernel_rfl%

theorem agreed_apart (model : Model) :
    meaning model agreedTyped agreedProtocol both (.cons false (.cons true .nil)) =
      .halt .incomplete := kernel_rfl%

theorem apart_stops (model : Model) :
    meaning model apartTyped apartProtocol both (.cons false (.cons true .nil)) =
      .halt .incomplete := kernel_rfl%

/-- A process after the reply to its first effect, when that is the receipt of a number. -/
def afterReceive {model : Model} {A : Type} (process : PIR.Process (Effects model) A)
    (reply : Nat) : Option (PIR.Process (Effects model) A) :=
  match process with
  | .call (.receive _ .nat) next => some (next reply)
  | _ => none

theorem relayed_same (model : Model) :
    afterReceive (meaning model relayedTyped relayedProtocol receivers .nil) 5 =
      some (.done .nil) := kernel_rfl%

theorem relayed_differs (model : Model) :
    afterReceive (meaning model relayedTyped relayedProtocol receivers .nil) 7 =
      some (.halt .incomplete) := kernel_rfl%

end CopiesPremises
