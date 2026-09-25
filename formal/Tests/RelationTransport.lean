import Tools.RelationReference

/-! Codec controls for actual canonical relation transport. These fixtures do
not prove a byte codec roundtrip for all inputs or external importer adequacy.
The algebraic assignment/binding theorems live in Zkc.Relation.Reference.
-/

set_option autoImplicit false

namespace Tests.RelationTransport

open Lean Tools.Relation.Transport Tools.Interactive.ScalarReference

-- Independent exact-modulus controls; no native field catalog is consulted.
example : Domain.bls.modulus =
    52435875175126190479447740508185965837690552500527637822603658699938581184513 := by decide
example : Domain.ristretto.modulus =
    7237005577332262213973186563042994240857116359379907606001950938285454250989 := by decide
example : Domain.koalaBear.modulus = 2130706433 := by decide

example : natural (.str "0") 65536 "bad" = .ok 0 := by decide +kernel
example : natural (.str "65536") 65536 "bad" = .ok 65536 := by decide +kernel
example : natural (.str "65537") 65536 "bad" = .error "bad" := by decide +kernel
example : natural (.str "01") 65536 "bad" = .error "bad" := by decide +kernel
example : natural (.str "+1") 65536 "bad" = .error "bad" := by decide +kernel
example : natural (.str "-1") 65536 "bad" = .error "bad" := by decide +kernel
example : natural (toJson (1 : Nat)) 65536 "bad" = .error "bad" := by decide +kernel
example : scalar .koalaBear (.str "2130706433") = .error "relation-coefficient" := by decide +kernel
example : scalar .koalaBear (.str "2130706432") = .ok (-1) := by decide +kernel

private def fixture : Json := .arr #[.str "zkc.relation.r1cs/1", .str "koala-bear",
  .str "4", .str "1", .str "1", .arr #[.arr #[
    .arr #[.arr #[.str "3", .str "1"]],
    .arr #[.arr #[.str "3", .str "1"]],
    .arr #[.arr #[.str "1", .str "1"]]]]]

private def strings (ns : Array Nat) : Json := .arr (ns.map fun n => .str (toString n))

private def run (x z : Array Nat) : Except String Bool := do
  let result ← evaluate (← decode fixture) (strings x) (strings z)
  result.getObjValAs? Bool "satisfied"

#guard ((decode fixture).map (fun r => encode r == fixture)) == .ok true
#guard ((parse fixture.compress >>= decode).map (fun r => encode r == fixture)) == .ok true
#guard run #[4, 7] #[1, 4, 7, 2] == .ok true
#guard run #[4, 7] #[1, 4, 7, 3] == .ok false
#guard run #[4, 7] #[0, 4, 7, 2] == .ok false
#guard run #[0, 0] #[0, 0, 0, 0] == .ok false
#guard run #[7, 4] #[1, 4, 7, 2] == .ok false
#guard run #[4, 7] #[1, 4, 7, 2130706431] == .ok true
#guard run #[4] #[1, 4, 7, 2] == .error "relation-assignment-shape"

private def withForms (forms : Json) : Json :=
  .arr #[.str "zkc.relation.r1cs/1", .str "koala-bear", .str "4", .str "1", .str "1",
    .arr #[forms]]
private def term (i c : String) : Json := .arr #[.str i, .str c]
private def refused (json : Json) : Except String Unit := (decode json).map (fun _ => ())

#guard refused (withForms (.arr #[.arr #[term "1" "0"], .arr #[], .arr #[]])) ==
  .error "relation-zero-coefficient"
#guard refused (withForms (.arr #[.arr #[term "1" "1", term "1" "2"], .arr #[], .arr #[]])) ==
  .error "relation-column-order"
#guard refused (withForms (.arr #[.arr #[term "2" "1", term "1" "2"], .arr #[], .arr #[]])) ==
  .error "relation-column-order"
#guard refused (withForms (.arr #[.arr #[term "4" "1"], .arr #[], .arr #[]])) ==
  .error "relation-column-index"
#guard refused (withForms (.arr #[.arr #[], .arr #[]])) == .error "relation-row"
#guard refused (withForms (.arr #[.arr #[.arr #[.str "1"]], .arr #[], .arr #[]])) ==
  .error "relation-term"
#guard refused (.arr #[.str "zkc.relation.r1cs/1", .str "bn128", .str "1", .str "0",
  .str "0", .arr #[]]) == .error "relation-field"
#guard refused (.arr #[.str "zkc.relation.r1cs/1", .str "koala-bear", .str "1", .str "1",
  .str "0", .arr #[]]) == .error "relation-dimension"

-- Escapes of ordinary ASCII are valid JSON; malformed Unicode is refused.
#guard ((parse "[\"\\u0031\"]").map (· == .arr #[.str "1"])) == .ok true
#guard (parse "[\"\\ud800\"]").isOk == false
#guard (parse "[\"\\udc00\"]").isOk == false
#guard (parse "[\"\\ud800\\u0030\"]").isOk == false
#guard (parse "[\"\\ud83d\\ude00\"]").isOk
#guard (parse "[[[[[[[[[]]]]]]]]]").map (fun _ => ()) == .error "relation-depth-limit"
#guard (parse "[1e999999]").map (fun _ => ()) == .error "relation-json"
#guard (parse "{\"a\":\"1\"}").map (fun _ => ()) == .error "relation-json"
#guard (parse "[\"1\",]").isOk == false
#guard (parse "[\"1]").isOk == false

end Tests.RelationTransport
