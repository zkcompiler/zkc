import Std

set_option autoImplicit false

namespace Zkc.Transformations.EncodingReuse
-- A pure encoder, a fixed provider transition, and a role-local continuation.
-- Bytes are lists of arbitrary symbols so no byte codec law is smuggled in.
-- Output records the provider state, challenge, ordered absorbed messages and
-- final proof. Proof publication happens once, after the continuation returns.
def direct {F S B : Type} (encode : F → List B)
    (absorb : S → List B → S) (draw : S → S × F)
    (initial : S) (claim : F) (first : List F) (next : F → List F) :=
  let s := first.foldl (fun s x => absorb s (encode x))
    (absorb initial (encode claim))
  let result := draw s
  (result.1, result.2, encode claim :: first.map encode,
    (first ++ next result.2).flatMap encode)

def cached {F S B : Type} (encode : F → List B)
    (absorb : S → List B → S) (draw : S → S × F)
    (initial : S) (claim : F) (first : List F) (next : F → List F) :=
  let encodedFirst := first.map encode
  let s := encodedFirst.foldl absorb (absorb initial (encode claim))
  let result := draw s
  (result.1, result.2, encode claim :: encodedFirst,
    encodedFirst.flatten ++ (next result.2).flatMap encode)

-- Universal in message length, field representation, local continuation and
-- provider state law. This is deterministic same-provider preservation, not
-- an assertion that an actual toy hash supplies fresh uniform randomness.
theorem cache_encoding_preserves {F S B : Type} (encode : F → List B)
    (absorb : S → List B → S) (draw : S → S × F)
    (initial : S) (claim : F) (first : List F) (next : F → List F) :
    cached encode absorb draw initial claim first next =
      direct encode absorb draw initial claim first next := by
  simp [cached, direct, List.foldl_map, List.flatMap]

-- Abstract count of encoder INVOCATIONS in the operational algorithms.
-- Not a count obtained from reducing the denotational tuple above.
def directEncodes (m k : Nat) := 1 + m + (m + k)
def cachedEncodes (m k : Nat) := 1 + m + k
theorem encoder_saving (m k : Nat) :
    directEncodes m k = cachedEncodes m k + m := by
  simp [directEncodes, cachedEncodes]; omega

end Zkc.Transformations.EncodingReuse
