// Closed, Host-admitted relation bundle assets. The digest names an admitted
// zkc.relation-bundle/0 carrier; the static table index selects one of its
// tables. The Host separately admits the bundle body under that identity.
def RelationF : ZKC_Root<"F", FieldDomain>;
def RelationTable : ZKC_Root<"Table", NatParameter>;
// Dense row-major assertion residuals of one present table: the witness,
// configuration and public-data operands carry that table's groups by
// authority in declaration order, and public data starts with every bundle
// public slot. Inactive assertion slots are zero. No interaction, presence
// or satisfaction claim is made.
def OpRelationTableRows : ZKC_Operation<"relation.table_rows",
    [RelationF, RelationTable],
    [ZKC_Apply<TypeVector, [RelationF]>, ZKC_Apply<TypeVector, [RelationF]>,
     ZKC_Apply<TypeVector, [RelationF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [RelationF]>], [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Polynomial view of one present table on the multiplicative domain of its
// own height. These operations derive facts and substitute the table's arena;
// they select no quotient combination, challenge, commitment or proof.
// Widths, public slots, arena inputs, assertions and quotient chunks of length
// height for a two-adic height admitted by the table.
def OpRelationTableShape : ZKC_Operation<"relation.table_shape",
    [RelationF, RelationTable], [ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Kind, flattened column and row rotation of one ordered arena input.
def OpRelationTableInput : ZKC_Operation<"relation.table_input",
    [RelationF, RelationTable],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Half-open active row interval of one assertion.
def OpRelationTableScope : ZKC_Operation<"relation.table_scope",
    [RelationF, RelationTable],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Assertion expressions, in assertion order, at one assignment of every arena
// input. A base-field table may be substituted in its extension field.
def OpRelationTablePoint : ZKC_Operation<"relation.table_point",
    [RelationF, RelationTable], [ZKC_Apply<TypeVector, [RelationF]>],
    [ZKC_Apply<TypeVector, [RelationF]>], [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// The same substitution at `rows` row-major assignments of every arena input:
// row-major results with one column per assertion, in assertion order.
def OpRelationTablePoints : ZKC_Operation<"relation.table_points",
    [RelationF, RelationTable],
    [ZKC_Apply<TypeVector, [RelationF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [RelationF]>], [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Interaction view of one table. These operations expose the declared height
// policy and the interaction records; they apply no scope, multiplicity range,
// balance, challenge or reduction, and claim no satisfaction.
// Optional flag, height authority, minimum, maximum and power-of-two flag of
// the declared policy, independent of presence and of any height.
def OpRelationTablePolicy : ZKC_Operation<"relation.table_policy",
    [RelationF, RelationTable], [],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Interaction count and record row width at a height admitted by the declared policy.
def OpRelationTableInteractions : ZKC_Operation<"relation.table_interactions",
    [RelationF, RelationTable], [ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Kind, channel, side, locality flag and key, active rows, arity, bound flag
// and bound, tuple degree and count degree of one interaction.
def OpRelationTableInteraction : ZKC_Operation<"relation.table_interaction",
    [RelationF, RelationTable],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
// Interaction records at `rows` row-major assignments of every arena input:
// per row, each interaction's tuple outputs and then its count output, in
// interaction order. No scope or multiplicity range is applied.
def OpRelationTableRecordPoints : ZKC_Operation<"relation.table_record_points",
    [RelationF, RelationTable],
    [ZKC_Apply<TypeVector, [RelationF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [RelationF]>], [ZKC_Holds<CapabilityField, [RelationF]>]> {
  let parameters = RelationAssetIdentity;
}
