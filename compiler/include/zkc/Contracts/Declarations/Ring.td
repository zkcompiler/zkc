// Closed, Host-admitted expression assets. The digest is a normative reference;
// expression bytes travel separately from the bounded executable artifact.
def RingF : ZKC_Root<"F", FieldDomain>;
def OpRingPoint : ZKC_Operation<"ring.point", [RingF],
    [ZKC_Apply<TypeVector, [RingF]>], [ZKC_Apply<TypeVector, [RingF]>],
    [ZKC_Holds<CapabilityField, [RingF]>]> {
  let parameters = RingAssetIdentity;
}
def OpRingRows : ZKC_Operation<"ring.rows", [RingF],
    [ZKC_Apply<TypeVector, [RingF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [RingF]>], [ZKC_Holds<CapabilityField, [RingF]>]> {
  let parameters = RingAssetIdentity;
}
def OpRingCoefficients : ZKC_Operation<"ring.coefficients", [RingF],
    [ZKC_Apply<TypeVector, [RingF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [RingF]>], [ZKC_Holds<CapabilityField, [RingF]>]> {
  let parameters = RingAssetIdentity;
}
def OpRingAffineSum : ZKC_Operation<"ring.affine_sum", [RingF],
    [ZKC_Apply<TypeVector, [RingF]>, ZKC_Apply<TypeVector, [RingF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [RingF]>], [ZKC_Holds<CapabilityField, [RingF]>]> {
  let parameters = RingAssetIdentity;
}
