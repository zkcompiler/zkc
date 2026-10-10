import Tools.Interactive.ExtensionReference

/-! Executable sampling equations, independent of native Plonky3/rand/Merlin.
These functions interpret supplied bytes; they do not assert those bytes are
uniform or establish Fiat–Shamir security. -/
set_option autoImplicit false
namespace Tools.Interactive.Sampling

def littleValue (bytes : ByteArray) : Nat :=
  bytes.toList.foldr (fun b n => b.toNat + 256 * n) 0

def coordinates (bytes : ByteArray) : List ExtensionReference.Base :=
  (List.range (bytes.size / 4)).filterMap fun i =>
    let n := littleValue (bytes.extract (4*i) (4*i+4)) % 2^31
    if n < Bindings.koalaBearModulus then some (n : ExtensionReference.Base) else none

def extension (xs : List ExtensionReference.Base) : Option ExtensionReference.Scalar :=
  let a := (xs.take 8).toArray
  if h : a.size = 8 then some ⟨⟨a, h⟩⟩ else none

def validBound (bound : Nat) : Bool :=
  0 < bound && bound < 2^64 && bound &&& (bound - 1) == 0

def index (bytes : ByteArray) (bound : Nat) : Result Nat := do
  ensure (bytes.size == 64) "transcript-challenge-width"
  ensure (validBound bound) "query-bound"
  return littleValue (bytes.extract 0 8) % bound

end Tools.Interactive.Sampling
