import Zkc.Source.Structured.Import
import Zkc.Source.Structured.CatalogueJustification

/-! Controls for catalogue rows and their admission.

The BLS12-381 environment is consistent and justified. Rows of other
characteristics are ordinary data: a characteristic-two prime field and a
binary extension field over it pass the consistency check and the
justification predicate, and admission refuses a unit over them only because
the environment does not list them. -/

set_option autoImplicit false

namespace Tests.StructuredCatalogue
open Zkc.Source.Structured

private def code {α : Type} : Except String α → String
  | .ok _ => ""
  | .error error => error

private def digest : String := "sha256:" ++ String.ofList (List.replicate 64 '0')

-- The environment is consistent, its exported rows agree with it, and it is
-- justified: the BLS12-381 scalar modulus is prime.
example : code blsCatalogue.check = "" := by decide +kernel
example : code (blsRows.agrees admittedCatalogue) = "" := by decide +kernel
example : blsCatalogue.Justified := blsCatalogue_justified

/-- A characteristic-two prime field and a degree-128 binary extension of it. -/
private def binaryRows : Catalogue where
  nominals := [
    { identity := "gf2", sort := .field, members := [],
      capabilities := ["Field", "CommRing", "PrimeField"], modulus := some 2 },
    { identity := "gf2-128", sort := .field, members := [("BaseField", "gf2")],
      capabilities := ["Field", "CommRing", "ExtensionField"], modulus := some 2 }]
  services := [{ contract := "random.gf2-128/0", sampled := "gf2-128", methods := ["draw"] }]

-- Well-formed rows that the environment does not list.
example : code binaryRows.check = "" := by decide +kernel
example : code (binaryRows.agrees admittedCatalogue) = "structured-catalogue-unknown" := by
  decide +kernel

theorem binaryRows_justified : binaryRows.Justified := by
  intro row member
  simp only [binaryRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    exact ⟨fun modulus same _ => (by cases same; exact Nat.prime_two),
      fun absent => (by simp at absent)⟩

/-- An extension field of odd characteristic without `PrimeField`; its modulus
is the characteristic of its base field. -/
private def extensionRows : Catalogue where
  nominals := [
    { identity := "koala", sort := .field, members := [],
      capabilities := ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "TwoAdicField"],
      modulus := some 2130706433 },
    { identity := "koala.quartic", sort := .field, members := [("BaseField", "koala")],
      capabilities := ["Field", "CommRing", "ExtensionField", "CharacteristicNotTwo"],
      modulus := some 2130706433 }]
  services := []

example : code extensionRows.check = "" := by decide +kernel
example : code (extensionRows.agrees admittedCatalogue) = "structured-catalogue-unknown" := by
  decide +kernel

/-! Consistency refusals, one per condition. -/

private def fieldRow (identity : String) (capabilities : List String := ["Field"])
    (members : List (String × String) := []) (modulus : Option Nat := some 5) : Nominal :=
  ⟨identity, .field, members, capabilities, modulus⟩

private def rows (nominals : List Nominal) (services : List Service := []) : Catalogue :=
  ⟨nominals, services, []⟩

example : code (rows [fieldRow "1field"]).check = "structured-catalogue-identity" := by decide +kernel
example : code (rows [fieldRow "f" (modulus := some 1)]).check =
    "structured-catalogue-modulus" := by decide +kernel
example : code (rows [⟨"g", .group, [], ["Group"], some 5⟩]).check =
    "structured-catalogue-modulus" := by decide +kernel
example : code (rows [fieldRow "f", fieldRow "f"]).check = "structured-catalogue-duplicate" := by
  decide +kernel
example : code (rows [fieldRow "f" ["Field", "Field"]]).check =
    "structured-catalogue-duplicate" := by decide +kernel
example : code (rows [fieldRow "f" (members := [("Scalar", "f")])]).check =
    "structured-catalogue-member" := by decide +kernel
example : code (rows [fieldRow "f" (members := [("BaseField", "absent")])]).check =
    "structured-catalogue-member" := by decide +kernel
example : code (rows [fieldRow "f" ["ScalarAction"]]).check = "structured-catalogue-capability" := by
  decide +kernel
example : code (rows [fieldRow "f" ["Field", "PairingField"]]).check =
    "structured-catalogue-pairing" := by decide +kernel
example : code (rows [⟨"g", .group, [], ["Group"], none⟩] [⟨"random.g/0", "g", ["draw"]⟩]).check =
    "structured-catalogue-service" := by decide +kernel
example : code (rows [fieldRow "f"] [⟨"random.f/0", "f", ["draw", "index"]⟩]).check =
    "structured-catalogue-service" := by decide +kernel
example : code (rows [fieldRow "f" ["Field", "IndexRandomness"]]
    [⟨"random.f/0", "f", ["draw", "index"]⟩]).check = "" := by decide +kernel

-- A row that differs from the environment's row for its identity.
example : code ((rows [fieldRow blsScalar (modulus := some blsModulus)]).agrees
    admittedCatalogue) = "structured-catalogue-mismatch" := by decide +kernel

/-! Admission of whole units. -/

private def unit (type : Ty) (catalogue : Catalogue) : Snapshot :=
  ⟨digest, "main", [], [], [], [.function ⟨"main", .protocol, .publicDef, [type], [type],
    some ⟨["P"], [["P"]], [["P"]]⟩, [], none, .block [] (.ret [0])⟩], [⟨"main", []⟩], catalogue⟩

example : code (check (unit (.field blsScalar) blsRows)) = "" := by decide +kernel
-- The binary unit is well formed; the environment does not list its rows.
example : code (check (unit (.field "gf2-128") binaryRows)) = "structured-catalogue-unknown" := by
  decide +kernel
-- Every identity resolves against the exported rows.
example : code (check (unit (.field blsScalar) (rows []))) = "structured-domain-unknown" := by
  decide +kernel
example : code (check (unit (.group blsScalar) blsRows)) = "structured-domain-sort" := by
  decide +kernel
-- Exported rows the environment lists, at a sort instance it does not admit.
example : code (check (unit (.group blsGroupTwo) blsRows)) = "structured-type-unadmitted" := by
  decide +kernel

-- A field constant is below the modulus of its field's row.
private def constantUnit (text : String) : Snapshot :=
  ⟨digest, "main", [], [], [], [.function ⟨"main", .protocol, .publicDef, [], [.field blsScalar],
    some ⟨["P"], [], [["P"]]⟩, [], none,
    .block [.instruction (.fieldConstant blsScalar text) [] [.field blsScalar] [] ""] (.ret [0])⟩],
    [⟨"main", []⟩], blsRows⟩

example : code (check (constantUnit
    "52435875175126190479447740508185965837690552500527637822603658699938581184512")) = "" := by
  decide +kernel
example : code (check (constantUnit
    "52435875175126190479447740508185965837690552500527637822603658699938581184513")) =
    "structured-field-canonical" := by decide +kernel
end Tests.StructuredCatalogue
