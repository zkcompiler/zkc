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
