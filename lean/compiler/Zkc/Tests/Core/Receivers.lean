import Zkc.Tests.Core.Runs
import Zkc.Tests.Core.Roles

/-! The receivers of a draw are listed once each, in any order.

A callee of three roles draws at its third role, and its first and second roles are the
receivers. A caller applies it under a role map that puts the two receivers in the other order
in the caller's roster. Expansion maps the receivers through the role map, so the draw of the
expanded entry lists its receivers out of order.

- The package is admitted, and so is its expansion: the expanded entry is well formed.
- The programs of the three roles, run against each other, return what the grouped run returns.
- A draw that lists a receiver twice is refused.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Concrete Zkc.Core.Execute Zkc.Core.Runs

namespace Receivers

/-- The law of the type row 0. -/
def law : Operation :=
  ⟨⟨Name.ofString "law.uniform", [.type (.nominal 0)]⟩, ⟨[], [.nominal 0], .sampling⟩⟩

/-- A package of protocols of three roles without inputs, with the type `bls12-381.fr` and its
law. -/
abbrev packageOf (protocols : List Raw.Protocol) : Raw.Package :=
  ⟨[⟨Name.ofString "bls12-381.fr", []⟩], [], [], [law], [], protocols, none⟩

/-- The third role draws; the first and the second hear the coin and return it. -/
abbrev coin : Raw.Protocol :=
  ⟨false, 3, [], [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩], [],
    .step (.draw 2 [0, 1] 0 0 []) (.ret [1, 2])⟩

/-- The callee's roles 0, 1 and 2 run as the caller's roles 2, 0 and 1. -/
abbrev outer : Raw.Protocol :=
  ⟨false, 3, [], [⟨.nominal 0, 2⟩, ⟨.nominal 0, 0⟩], [],
    .step (.apply 0 [2, 0, 1] 0 []) (.ret [0, 1])⟩

abbrev reordered : Raw.Package := packageOf [coin, outer]

kernel_refl elaborates : (elaborate reordered).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw reordered elaborates

-- The draw of the expanded entry: the owner is the caller's role 1, and the receivers are the
-- images of the callee's roles 0 and 1, in the callee's order.
kernel_refl expanded :
    typed.expandedProtocols.toOption.map (·.map (·.body)) equals
      some [Raw.ProtocolRegion.step (.draw 1 [2, 0] 0 0 []) (.ret [1, 2])]

-- A draw that names a receiver twice.
kernel_refl receiver_twice :
    (match elaborate (packageOf [⟨false, 3, [], [], [], .step (.draw 2 [0, 0] 0 0 []) (.ret [])⟩])
      with
      | .error refusal => some refusal
      | .ok _ => none) equals
      some ⟨.residual .repeatedReceiver, some (.protocol 0), []⟩

#eval show IO Unit from do
  let typed ← match elaborateWritten reordered with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  for roles in [[0, 1, 2], [2, 1, 0], [1, 0, 2]] do
    let heard ← IO.ofExcept (joint typed [] [7] roles)
    let returned := heard.roles.all fun
      | (_, .returned _) => true
      | _ => false
    unless heard.agrees && returned do
      throw (IO.userError s!"roles in the order {roles}: grouped {heard.grouped.describe}; own {heard.roles.map fun (_, own) => own.describe}")

end Receivers
