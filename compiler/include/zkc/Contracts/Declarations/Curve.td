// Logical contracts and curated exports owned by this domain.
def OpCurveNegG : ZKC_Root<"G", GroupDomain>;
def OpCurveNegScalar : ZKC_Project<OpCurveNegG, GroupScalar>;
def OpCurveNeg : ZKC_Operation<"curve.neg", [OpCurveNegG, OpCurveNegScalar],
    [ZKC_Apply<TypeGroup, [OpCurveNegG]>],
    [ZKC_Apply<TypeGroup, [OpCurveNegG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveNegG]>]> {
  int ordinal = 84;
}
def ExportCurveNeg : ZKC_OperationExport<"zkc::curve", "neg",
    OpCurveNeg, ["group"]>;

def OpCurveNonidentityG : ZKC_Root<"G", GroupDomain>;
def OpCurveNonidentityScalar : ZKC_Project<OpCurveNonidentityG, GroupScalar>;
def OpCurveNonidentity : ZKC_Operation<"curve.nonidentity", [OpCurveNonidentityG, OpCurveNonidentityScalar],
    [ZKC_Apply<TypeGroup, [OpCurveNonidentityG]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityScalarAction, [OpCurveNonidentityG]>]> {
  int ordinal = 85;
}
def ExportCurveNonidentity : ZKC_OperationExport<"zkc::curve", "nonidentity",
    OpCurveNonidentity, ["group"]>;

def OpCurveMsmG : ZKC_Root<"G", GroupDomain>;
def OpCurveMsmScalar : ZKC_Project<OpCurveMsmG, GroupScalar>;
def OpCurveMsm : ZKC_Operation<"curve.msm", [OpCurveMsmG, OpCurveMsmScalar],
    [ZKC_Apply<TypeVector, [OpCurveMsmScalar]>, ZKC_Apply<TypeGroups, [OpCurveMsmG]>],
    [ZKC_Apply<TypeGroup, [OpCurveMsmG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveMsmG]>]> {
  int ordinal = 86;
  let facets = [ZKC_Contraction<0, 1>];
}
def ExportCurveMsm : ZKC_OperationExport<"zkc::curve", "msm",
    OpCurveMsm, ["vector", "groups"]>;

def OpCurveScaleEachG : ZKC_Root<"G", GroupDomain>;
def OpCurveScaleEachScalar : ZKC_Project<OpCurveScaleEachG, GroupScalar>;
def OpCurveScaleEach : ZKC_Operation<"curve.scale_each", [OpCurveScaleEachG, OpCurveScaleEachScalar],
    [ZKC_Apply<TypeVector, [OpCurveScaleEachScalar]>, ZKC_Apply<TypeGroups, [OpCurveScaleEachG]>],
    [ZKC_Apply<TypeGroups, [OpCurveScaleEachG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveScaleEachG]>]> {
  int ordinal = 87;
  let facets = [ZKC_Diagonal<0, 1, 0>];
}
def ExportCurveScaleEach : ZKC_OperationExport<"zkc::curve", "scale_each",
    OpCurveScaleEach, ["vector", "groups"]>;

def OpCurveVectorAddG : ZKC_Root<"G", GroupDomain>;
def OpCurveVectorAddScalar : ZKC_Project<OpCurveVectorAddG, GroupScalar>;
def OpCurveVectorAdd : ZKC_Operation<"curve.vector_add", [OpCurveVectorAddG, OpCurveVectorAddScalar],
    [ZKC_Apply<TypeGroups, [OpCurveVectorAddG]>, ZKC_Apply<TypeGroups, [OpCurveVectorAddG]>],
    [ZKC_Apply<TypeGroups, [OpCurveVectorAddG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveVectorAddG]>]> {
  int ordinal = 88;
}
def ExportCurveVectorAdd : ZKC_OperationExport<"zkc::curve", "vector_add",
    OpCurveVectorAdd, ["groups0", "groups1"]>;

def OpCurveVectorScaleG : ZKC_Root<"G", GroupDomain>;
def OpCurveVectorScaleScalar : ZKC_Project<OpCurveVectorScaleG, GroupScalar>;
def OpCurveVectorScale : ZKC_Operation<"curve.vector_scale", [OpCurveVectorScaleG, OpCurveVectorScaleScalar],
    [ZKC_Apply<TypeGroups, [OpCurveVectorScaleG]>, ZKC_Apply<TypeField, [OpCurveVectorScaleScalar]>],
    [ZKC_Apply<TypeGroups, [OpCurveVectorScaleG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveVectorScaleG]>]> {
  int ordinal = 89;
}
def ExportCurveVectorScale : ZKC_OperationExport<"zkc::curve", "vector_scale",
    OpCurveVectorScale, ["groups", "field"]>;

def OpCurveSplitG : ZKC_Root<"G", GroupDomain>;
def OpCurveSplitScalar : ZKC_Project<OpCurveSplitG, GroupScalar>;
def OpCurveSplit : ZKC_Operation<"curve.split", [OpCurveSplitG, OpCurveSplitScalar],
    [ZKC_Apply<TypeGroups, [OpCurveSplitG]>],
    [ZKC_Apply<TypeGroups, [OpCurveSplitG]>, ZKC_Apply<TypeGroups, [OpCurveSplitG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveSplitG]>]> {
  int ordinal = 90;
}
def ExportCurveSplit : ZKC_OperationExport<"zkc::curve", "split",
    OpCurveSplit, ["groups"]>;

def OpCurveConcatG : ZKC_Root<"G", GroupDomain>;
def OpCurveConcatScalar : ZKC_Project<OpCurveConcatG, GroupScalar>;
def OpCurveConcat : ZKC_Operation<"curve.concat", [OpCurveConcatG, OpCurveConcatScalar],
    [ZKC_Apply<TypeGroups, [OpCurveConcatG]>, ZKC_Apply<TypeGroups, [OpCurveConcatG]>],
    [ZKC_Apply<TypeGroups, [OpCurveConcatG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveConcatG]>]> {
  int ordinal = 91;
}
def ExportCurveConcat : ZKC_OperationExport<"zkc::curve", "concat",
    OpCurveConcat, ["groups0", "groups1"]>;

def OpPairingCheckF : ZKC_Root<"F", FieldDomain>;
def OpPairingCheckPairingG1 : ZKC_Project<OpPairingCheckF, FieldPairingG1>;
def OpPairingCheckPairingG2 : ZKC_Project<OpPairingCheckF, FieldPairingG2>;
def OpPairingCheck : ZKC_Operation<"pairing.check", [OpPairingCheckF, OpPairingCheckPairingG1, OpPairingCheckPairingG2],
    [ZKC_Apply<TypeGroups, [OpPairingCheckPairingG1]>, ZKC_Apply<TypeGroups, [OpPairingCheckPairingG2]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityPairingField, [OpPairingCheckF]>]> {
  int ordinal = 92;
}
def ExportPairingCheck : ZKC_OperationExport<"zkc::curve", "pairing_check",
    OpPairingCheck, ["groups0", "groups1"]>;

def OpCurveGeneratorG : ZKC_Root<"G", GroupDomain>;
def OpCurveGeneratorScalar : ZKC_Project<OpCurveGeneratorG, GroupScalar>;
def OpCurveGenerator : ZKC_Operation<"curve.generator", [OpCurveGeneratorG, OpCurveGeneratorScalar],
    [],
    [ZKC_Apply<TypeGroup, [OpCurveGeneratorG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveGeneratorG]>]> {
  int ordinal = 127;
  let facets = [PublicReplay];
}
def ExportCurveGenerator : ZKC_OperationExport<"zkc::curve", "generator",
    OpCurveGenerator, []>;

def OpCurveAddG : ZKC_Root<"G", GroupDomain>;
def OpCurveAddScalar : ZKC_Project<OpCurveAddG, GroupScalar>;
def OpCurveAdd : ZKC_Operation<"curve.add", [OpCurveAddG, OpCurveAddScalar],
    [ZKC_Apply<TypeGroup, [OpCurveAddG]>, ZKC_Apply<TypeGroup, [OpCurveAddG]>],
    [ZKC_Apply<TypeGroup, [OpCurveAddG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveAddG]>]> {
  int ordinal = 128;
  let facets = [PublicReplay];
}
def ExportCurveAdd : ZKC_OperationExport<"zkc::curve", "add",
    OpCurveAdd, ["group0", "group1"]>;

def OpCurveScaleG : ZKC_Root<"G", GroupDomain>;
def OpCurveScaleScalar : ZKC_Project<OpCurveScaleG, GroupScalar>;
def OpCurveScale : ZKC_Operation<"curve.scale", [OpCurveScaleG, OpCurveScaleScalar],
    [ZKC_Apply<TypeGroup, [OpCurveScaleG]>, ZKC_Apply<TypeField, [OpCurveScaleScalar]>],
    [ZKC_Apply<TypeGroup, [OpCurveScaleG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveScaleG]>]> {
  int ordinal = 129;
  let facets = [PublicReplay];
}
def ExportCurveScale : ZKC_OperationExport<"zkc::curve", "scale",
    OpCurveScale, ["group", "field"]>;

def OpCurveEqualG : ZKC_Root<"G", GroupDomain>;
def OpCurveEqualScalar : ZKC_Project<OpCurveEqualG, GroupScalar>;
def OpCurveEqual : ZKC_Operation<"curve.equal", [OpCurveEqualG, OpCurveEqualScalar],
    [ZKC_Apply<TypeGroup, [OpCurveEqualG]>, ZKC_Apply<TypeGroup, [OpCurveEqualG]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityScalarAction, [OpCurveEqualG]>]> {
  int ordinal = 130;
  let facets = [PublicReplay];
}
def ExportCurveEqual : ZKC_OperationExport<"zkc::curve", "equal",
    OpCurveEqual, ["group0", "group1"]>;

def OpCurveEmptyG : ZKC_Root<"G", GroupDomain>;
def OpCurveEmptyScalar : ZKC_Project<OpCurveEmptyG, GroupScalar>;
def OpCurveEmpty : ZKC_Operation<"curve.empty", [OpCurveEmptyG, OpCurveEmptyScalar],
    [],
    [ZKC_Apply<TypeGroups, [OpCurveEmptyG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveEmptyG]>]> {
  int ordinal = 131;
  let facets = [PublicReplay];
}
def ExportCurveEmpty : ZKC_OperationExport<"zkc::curve", "empty",
    OpCurveEmpty, []>;

def OpCurveAppendG : ZKC_Root<"G", GroupDomain>;
def OpCurveAppendScalar : ZKC_Project<OpCurveAppendG, GroupScalar>;
def OpCurveAppend : ZKC_Operation<"curve.append", [OpCurveAppendG, OpCurveAppendScalar],
    [ZKC_Apply<TypeGroups, [OpCurveAppendG]>, ZKC_Apply<TypeGroup, [OpCurveAppendG]>],
    [ZKC_Apply<TypeGroups, [OpCurveAppendG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveAppendG]>]> {
  int ordinal = 132;
  let facets = [PublicReplay];
}
def ExportCurveAppend : ZKC_OperationExport<"zkc::curve", "append",
    OpCurveAppend, ["groups", "group"]>;

def OpCurveAtG : ZKC_Root<"G", GroupDomain>;
def OpCurveAtScalar : ZKC_Project<OpCurveAtG, GroupScalar>;
def OpCurveAt : ZKC_Operation<"curve.at", [OpCurveAtG, OpCurveAtScalar],
    [ZKC_Apply<TypeGroups, [OpCurveAtG]>],
    [ZKC_Apply<TypeGroup, [OpCurveAtG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveAtG]>]> {
  int ordinal = 133;
  let parameters = ExtentParameter;
  let facets = [PublicReplay];
}
def ExportCurveAt : ZKC_OperationExport<"zkc::curve", "at",
    OpCurveAt, ["groups"]>;

def OpCurveGetG : ZKC_Root<"G", GroupDomain>;
def OpCurveGetScalar : ZKC_Project<OpCurveGetG, GroupScalar>;
def OpCurveGet : ZKC_Operation<"curve.get", [OpCurveGetG, OpCurveGetScalar],
    [ZKC_Apply<TypeGroups, [OpCurveGetG]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeGroup, [OpCurveGetG]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveGetG]>]> {
  int ordinal = 134;
  let facets = [PublicReplay];
}
def ExportCurveGet : ZKC_OperationExport<"zkc::curve", "get",
    OpCurveGet, ["groups", "index"]>;

def OpCurveLengthG : ZKC_Root<"G", GroupDomain>;
def OpCurveLengthScalar : ZKC_Project<OpCurveLengthG, GroupScalar>;
def OpCurveLength : ZKC_Operation<"curve.length", [OpCurveLengthG, OpCurveLengthScalar],
    [ZKC_Apply<TypeGroups, [OpCurveLengthG]>],
    [ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityScalarAction, [OpCurveLengthG]>]> {
  int ordinal = 135;
  let facets = [PublicReplay];
}
def ExportCurveLength : ZKC_OperationExport<"zkc::curve", "length",
    OpCurveLength, ["groups"]>;

def OpCurveCommitG : ZKC_Root<"G", GroupDomain>;
def OpCurveCommitScalar : ZKC_Project<OpCurveCommitG, GroupScalar>;
def OpCurveCommit : ZKC_Operation<"curve.commit", [OpCurveCommitG, OpCurveCommitScalar],
    [ZKC_Apply<TypeGroups, [OpCurveCommitG]>, ZKC_Apply<TypeNonce, [OpCurveCommitScalar]>],
    [ZKC_Apply<TypeGroups, [OpCurveCommitG]>, ZKC_Apply<TypeNonce, [OpCurveCommitScalar]>], [ZKC_Holds<CapabilityScalarAction, [OpCurveCommitG]>]> {
  int ordinal = 136;
}
def ExportCurveCommit : ZKC_OperationExport<"zkc::curve", "commit",
    OpCurveCommit, ["groups", "nonce"]>;

def OpCurveResponseF : ZKC_Root<"F", FieldDomain>;
def OpCurveResponse : ZKC_Operation<"curve.response", [OpCurveResponseF],
    [ZKC_Apply<TypeField, [OpCurveResponseF]>, ZKC_Apply<TypeField, [OpCurveResponseF]>, ZKC_Apply<TypeNonce, [OpCurveResponseF]>],
    [ZKC_Apply<TypeField, [OpCurveResponseF]>], [ZKC_Holds<CapabilityField, [OpCurveResponseF]>]> {
  int ordinal = 137;
}
def ExportCurveResponse : ZKC_OperationExport<"zkc::curve", "response",
    OpCurveResponse, ["field0", "field1", "nonce"]>;

def OperatorCurveAdd4 : ZKC_Operator<"+", [TypeGroup, TypeGroup], OpCurveAdd, [0, 1]>;
def OperatorCurveNeg5 : ZKC_Operator<"-", [TypeGroup], OpCurveNeg, [0]>;
def OperatorCurveScale6 : ZKC_Operator<"*", [TypeGroup, TypeField], OpCurveScale, [0, 1]>;
def OperatorCurveScale7 : ZKC_Operator<"*", [TypeField, TypeGroup], OpCurveScale, [1, 0]>;
