import Zkc.Tests.Core.Runs

/-! Every receiver of a draw hears every coin, in the executor.

Two packages of three roles with the law of `bls12-381.fr`, built here.

- In the first, role 0 draws once and roles 1 and 2 are the receivers. The programs of the
  three roles, run against each other, return what the grouped run returns: both receivers
  hear the coin. An executor that carried the coin as one message, which the first receiver
  consumed, left the second receiver waiting.
- In the second, role 0 draws twice at one site, in a loop of two iterations, and each role
  collects its two coins. The owner's program performs both draws before a receiver moves.
  Each receiver hears the two coins in the order announced, not the later one twice, and
  the two coins differ.
- The outcome does not depend on the order in which the processes take their turns.
- The receivers without the owner wait for a coin that nobody announces.

These run in Lean's interpreter, not in the kernel.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Concrete Zkc.Core.Execute Zkc.Core.Runs

namespace PublicCoins

/-- The law of the type row 0. -/
def law : Operation :=
  ⟨⟨Name.ofString "law.uniform", [.type (.nominal 0)]⟩, ⟨[], [.nominal 0], .sampling⟩⟩

/-- A package of one protocol of three roles without inputs, with the type `bls12-381.fr`
and its law. -/
def packageOf (outputs : List Located) (body : Raw.ProtocolRegion) : Raw.Package :=
  ⟨[⟨Name.ofString "bls12-381.fr", []⟩], [], [], [law], [], [⟨false, 3, [], outputs, [], body⟩],
    none⟩

/-- Role 0 draws once; roles 1 and 2 are the receivers. Each role returns its coin. -/
def once : Raw.Package :=
  packageOf [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩, ⟨.nominal 0, 2⟩] <|
    .step (.draw 0 [1, 2] 0 0 []) <|
    .ret [0, 1, 2]

/-- Role 0 draws twice at one site, in a loop of two iterations; roles 1 and 2 are the
receivers. Each role collects its two coins. -/
def twice : Raw.Package :=
  packageOf
      [⟨.seq (.nominal 0) (some 2), 0⟩, ⟨.seq (.nominal 0) (some 2), 1⟩,
        ⟨.seq (.nominal 0) (some 2), 2⟩] <|
    .step (.repeat [0, 1, 2] (.static 2) [] []
        [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩, ⟨.nominal 0, 2⟩]
        (.step (.draw 0 [1, 2] 0 0 []) (.ret [3, 4, 5]))) <|
    .ret [0, 1, 2]

/-- The grouped run of a package and the runs of the programs of the given roles against
each other, in the order given. -/
def run (raw : Raw.Package) (roles : List Nat) : IO Joint := do
  let typed ← match elaborateWritten raw with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  IO.ofExcept (joint typed [] [7] roles)

/-- Every role's own program returned. -/
def allReturned (run : Joint) : Bool :=
  run.roles.all fun
    | (_, .returned _) => true
    | _ => false

/-- Every role's own program waits for a message. -/
def allWait (run : Joint) : Bool :=
  run.roles.all fun
    | (_, .failed message) => message == "waits for a message that is never sent"
    | _ => false

def describe (run : Joint) : String :=
  s!"grouped {run.grouped.describe}; own {run.roles.map fun (_, own) => own.describe}"

#eval show IO Unit from do
  -- One draw, two receivers in two processes: both hear the coin.
  for roles in [[0, 1, 2], [2, 1, 0], [1, 0, 2]] do
    let heard ← run once roles
    unless heard.agrees && allReturned heard do
      throw (IO.userError s!"one draw, roles in the order {roles}: {describe heard}")
  -- Two draws at one site before a receiver moves: each receiver hears both, in order.
  for roles in [[0, 1, 2], [2, 1, 0], [1, 0, 2]] do
    let heard ← run twice roles
    unless heard.agrees && allReturned heard do
      throw (IO.userError s!"two draws, roles in the order {roles}: {describe heard}")
    -- The two coins differ, so hearing the later coin twice would not agree.
    match heard.grouped with
    | .returned (.sequence [first, second] :: _) =>
        if first == second then throw (IO.userError "the two coins are equal")
    | _ => throw (IO.userError s!"two draws: {describe heard}")
  -- Without the owner nobody announces a coin: the receivers wait.
  let alone ← run once [1, 2]
  unless allWait alone do
    throw (IO.userError s!"the receivers alone: {describe alone}")

end PublicCoins
