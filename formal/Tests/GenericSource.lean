import Tools.Interactive.GenericSource

set_option autoImplicit false

namespace Tests.GenericSource
open Tools.Interactive Zkc.Source.Requirements

private def fold (promise : String) : Generic.Definition :=
  ⟨"Fold", [("F", .field)], [.relation promise [.root "F"]],
   [("a", ⟨"table", some (.root "F")⟩), ("r", ⟨"field", some (.root "F")⟩)],
   [⟨"table", some (.root "F")⟩],
   [⟨"step", "poly.fold", [.root "F"], [], ["a", "r"], ["out"], false⟩], ["out"], []⟩

example : (Generic.checkDefinition (fold "CommRing")).isOk = true := by native_decide
example : (Generic.checkDefinition (fold "PrimeField")).isOk = true := by native_decide
example : (Generic.checkDefinition (fold "CharacteristicNotTwo")).isOk = false := by native_decide

-- Congruence is directional only through installed members; equality does not
-- identify unrelated members of the same commitment scheme.
example : (Requirements.check [.equal (.root "C") (.root "D")]
    [.equal (.project (.root "C") "ValueField") (.project (.root "D") "ValueField")]).isOk = true := by native_decide
example : (Requirements.check []
    [.equal (.project (.root "C") "ValueField") (.project (.root "C") "PointField")]).isOk = false := by native_decide
example : (Requirements.check [.relation "Field" [.root "F"]]
    [.relation "PrimeField" [.root "F"]]).isOk = false := by native_decide
example : (Requirements.check [.relation "Encodes.field" [.root "E", .root "F"],
    .equal (.root "E") (.root "D")]
    [.relation "Encodes.field" [.root "D", .root "F"]]).isOk = true := by native_decide
example : (Requirements.check [.relation "Encodes.field" [.root "E", .root "F"]]
    [.relation "Encodes.field" [.root "F", .root "E"]]).isOk = false := by native_decide

private def rngAlias : Generic.Definition :=
  ⟨"Reuse", [("F", .field)], [.relation "Field" [.root "F"]],
   [("rng", ⟨"rng", some (.root "F")⟩)], [],
   [⟨"a", "random.draw", [.root "F"], [], ["rng"], ["x", "next"], false⟩,
    ⟨"b", "random.draw", [.root "F"], [], ["rng"], ["y", "last"], false⟩], [], []⟩
example : (Generic.checkDefinition rngAlias).isOk = false := by native_decide

example : (Generic.signature [("G", .group)] "curve.scale" [.root "G"]).toOption.bind
    (fun s => s.inputs[1]?.bind Generic.ValueType.domain) =
    some (.project (.root "G") "Scalar") := by native_decide

example : (Generic.valueType [("G", .group)] "field:G").isOk = false := by native_decide
example : (Generic.predicate [("E", .codec), ("F", .field)] "Encodes.field"
    [.root "F", .root "E"]).isOk = false := by native_decide
example : (Bindings.attributes true "field.constant" [toString (fieldModulus + 1)]).isOk = true := by native_decide
example : (Bindings.attributes false "field.constant" [toString (fieldModulus + 1)]).isOk = false := by native_decide
example : (Bindings.attributes true "curve.at" ["1048576"]).isOk = true := by native_decide
example : (Bindings.attributes true "curve.at" ["1048577"]).isOk = false := by native_decide
example : (Bindings.attributes false "curve.at" ["1048577"]).isOk = false := by native_decide

end Tests.GenericSource
