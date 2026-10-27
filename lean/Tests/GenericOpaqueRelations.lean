import Zkc.Source.Structured.OpaqueRegistry
import Zkc.Source.Structured.Import
import Zkc.Source.Structured.DomainContract
import Mathlib.Algebra.Ring.Int.Defs
import Tests.Generated.GenericOpaqueData

open Zkc.Source Zkc.Source.Structured
namespace Tests.GenericOpaqueRelations

private def identity : OpaqueFamilyIdentity := ⟨"vendor.layer/0", "layer", "0"⟩

private def instanceFor (domain : String) (count unused : Nat) :
    OpaqueInstance (assignment Int Int) :=
  ⟨[.field domain, .field domain], [.boolean], ["statement", "witness"],
    fun args => args.get .here = args.get (.there .here) + (count + unused : Nat)⟩

/-- The natural arguments affect meaning even though neither occurs in the ABI. -/
private def family : OpaqueFamily (assignment Int Int) where
  identity := identity
  instantiate arguments := match arguments with
    | [.field domain, .natural count, .natural unused] => do
      if domain != scalarDomain && domain != "koala-bear" then none else do
        let count ← Zkc.Source.Format.canonicalDecimal count
        let unused ← Zkc.Source.Format.canonicalDecimal unused
        some (instanceFor domain count unused)
    | _ => none

private def registry : OpaqueRegistry (assignment Int Int) := ⟨[family], by simp⟩
private def relation (domain : String := scalarDomain) (count : String := "2")
    (unused : String := "7") : Relation :=
  ⟨"Layer", .privateDef, identity.kind, identity.key, identity.revision,
    [.field domain, .field domain], [.boolean], ["statement", "witness"], none,
    [.field domain, .natural count, .natural unused]⟩

private def binding : registry.Binding relation :=
  ⟨instanceFor scalarDomain 2 7, by rfl, rfl, rfl, rfl, by decide +kernel, rfl⟩
private def aliasBinding : registry.Binding { relation with name := "Alias" } :=
  ⟨instanceFor scalarDomain 2 7, by rfl, rfl, rfl, rfl, by decide +kernel, rfl⟩

example (point value : Int) :
    binding.Holds (.cons point (.cons value .nil)) ↔ point = value + 9 := by rfl
example (point value : Int) :
    aliasBinding.Holds (.cons point (.cons value .nil)) ↔ binding.Holds (.cons point (.cons value .nil)) := by rfl

-- The selected family is fixed before evidence. No second proof record can
-- replace its predicate with True, False or a different layer identity.
example (evidence : registry.Binding relation) (point value : Int) :
    evidence.Holds (.cons point (.cons value .nil)) ↔ point = value + 9 := by
  exact (evidence.unique_meaning binding _).trans (by rfl)

private def phantomBinding : registry.Binding (relation scalarDomain "2" "8") :=
  ⟨instanceFor scalarDomain 2 8, by rfl, rfl, rfl, rfl, by decide +kernel, rfl⟩
example : binding.Holds (.cons 9 (.cons 0 .nil)) ∧
    ¬ phantomBinding.Holds (.cons 9 (.cons 0 .nil)) := by
  change (9 : Int) = 0 + 9 ∧ ¬ ((9 : Int) = 0 + 10)
  decide +kernel

-- The theorem uses constructor data produced from the actual full source
-- export. Canonical import and registry admission are checked separately below.
private def sourceRelation : Relation :=
  Tests.Generated.GenericOpaqueData.snapshot.relations[0]
private def sourceBinding : registry.Binding sourceRelation :=
  ⟨instanceFor scalarDomain 2 7, by rfl, rfl, rfl, rfl, by decide +kernel, rfl⟩
example (point value : Int) :
    sourceBinding.Holds (.cons point (.cons value .nil)) ↔ point = value + 9 := by rfl

private def sourceEnvironment : RegisteredRelations (assignment Int Int)
    Tests.Generated.GenericOpaqueData.snapshot.relations :=
  .ofChecked registry (by decide +kernel)

example (point value : Int) :
    sourceEnvironment.meanings ⟨0, by decide⟩ (.cons point (.cons value .nil)) ↔
      point = value + 9 :=
  (sourceEnvironment.meanings_exact _ sourceBinding _).trans (by rfl)

private def controls : List (String × Bool) := [
  ("two-domains", registry.check [relation, relation "koala-bear"]),
  ("two-naturals", registry.check [relation, relation scalarDomain "3"]),
  ("unused-static-retained", relation.opaqueIdentity != (relation scalarDomain "2" "8").opaqueIdentity),
  ("alias", registry.check [relation, { relation with name := "Alias" }]),
  ("missing-registry", !(OpaqueRegistry.empty (Value := assignment Int Int)).check [relation]),
  ("missing-family", !registry.check [{ relation with key := "unknown" }]),
  ("wrong-domain", !registry.check [relation "not-installed"]),
  ("wrong-typed-argument", !(registry.resolve { relation with staticArguments :=
    [.domain "Field" scalarDomain, .natural "2", .natural "7"] }).isSome),
  ("reordered-arguments", !(registry.resolve { relation with staticArguments :=
    [.natural "2", .field scalarDomain, .natural "7"] }).isSome),
  ("noncanonical-natural", !(registry.resolve (relation scalarDomain "02")).isSome),
  ("wrong-runtime-domain", !(registry.resolve { relation with inputs := [.field "koala-bear", .field "koala-bear"] }).isSome),
  ("wrong-purpose", !(registry.resolve { relation with purposes := ["parameter", "witness"] }).isSome),
  ("wrong-signature", !(registry.resolve { relation with inputs := [.boolean] }).isSome),
  ("duplicate-family", !(OpaqueRegistry.ofFamilies [family, { family with instantiate := fun _ => none }]).isOk),
  ("duplicate-family-signature", !(OpaqueRegistry.ofFamilies [family,
    ⟨identity, fun _ => some ⟨[.boolean], [.boolean], ["parameter"], fun _ => True⟩⟩]).isOk),
  ("duplicate-family-meaning", !(OpaqueRegistry.ofFamilies [family,
    ⟨identity, fun _ => some ⟨[.field scalarDomain, .field scalarDomain], [.boolean],
      ["statement", "witness"], fun _ => False⟩⟩]).isOk),
  ("conflicting-alias-signature", (checkRelationIdentities [relation,
    { relation with name := "Alias", inputs := [.boolean] }]).isOk == false),
  ("conflicting-alias-purpose", (checkRelationIdentities [relation,
    { relation with name := "Alias", purposes := ["parameter", "witness"] }]).isOk == false),
  ("formula-excluded", !(registry.resolve { relation with kind := "zkc.language.formula/0", formula := some "body" }).isSome),
  ("captured-excluded", !(registry.resolve { relation with kind := "zkc.relation.r1cs/0" }).isSome)]

/-- Read the actual full native export, run canonical structural admission, then
admit every opaque row against this previously defined registry. -/
def run (path : System.FilePath := "bridges/structured/fixtures/generic-opaque.json") : IO Unit := do
  let mut failed := 0
  for (name, passed) in controls do
    if !passed then
      IO.println s!"FAIL: {name}"
      failed := failed + 1
  if failed != 0 then throw (IO.userError s!"{failed} opaque registry controls failed")
  let bytes ← IO.FS.readFile path
  let snapshot ← IO.ofExcept (Format.parse bytes >>= Format.snapshot)
  let _program ← IO.ofExcept (check snapshot)
  unless snapshot.source == Tests.Generated.GenericOpaqueData.snapshot.source &&
      snapshot.relations.length == Tests.Generated.GenericOpaqueData.snapshot.relations.length &&
      (snapshot.relations.zip Tests.Generated.GenericOpaqueData.snapshot.relations).all
        (fun (actual, retained) => actual.name == retained.name &&
          actual.opaqueIdentity == retained.opaqueIdentity && actual.inputs == retained.inputs &&
          actual.outputs == retained.outputs && actual.purposes == retained.purposes) do
    throw (IO.userError "strictly read source differs from retained registry proof data")
  unless snapshot.relations.length == 5 && snapshot.contracts.length == 1 do
    throw (IO.userError "full source relation inventory differs")
  unless registry.check snapshot.relations do
    throw (IO.userError "full source export failed registered meaning admission")
  unless (snapshot.relations.map (·.opaqueIdentity)).eraseDups.length == 4 do
    throw (IO.userError "alias or phantom-static identity differs")
  unless !(OpaqueRegistry.empty (Value := assignment Int Int)).check snapshot.relations do
    throw (IO.userError "missing registry accepted full source")
  let some first := snapshot.relations.head? | throw (IO.userError "missing relation")
  unless !registry.check [{ first with purposes := ["parameter", "witness"] }] do
    throw (IO.userError "exported signature purpose mutation admitted")
  unless !(check { snapshot with relations := [{ first with staticArguments :=
      [.field "not-installed", .natural "2", .natural "7"] }] }).isOk do
    throw (IO.userError "static-only domain mutation admitted structurally")
  IO.println s!"generic opaque relations: {controls.length} controls; full source export, strict reader and registered admission passed"

end Tests.GenericOpaqueRelations
