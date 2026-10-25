#ifndef ZKC_MATHEMATICAL_DECLARATIONS
#define ZKC_MATHEMATICAL_DECLARATIONS
include "zkc/Contracts/Declarations/Schema.td"
// Ordinals are part of source catalog identity. Append new meanings; do not
// reorder existing entries when moving declarations between files.
def FieldConstantLaws : ZKC_ScalarLaws<"FieldRing", "FieldConstant"> {
  let total = 1;
}
def FieldAddLaws : ZKC_ScalarLaws<"FieldRing", "FieldBinary"> {
  let associative = 1; let commutative = 1; let total = 1;
  let leftIdentity = "Zero"; let rightIdentity = "Zero";
}
def FieldSubtractLaws : ZKC_ScalarLaws<"FieldRing", "FieldBinary"> {
  let total = 1; let rightIdentity = "Zero";
}
def FieldMultiplyLaws : ZKC_ScalarLaws<"FieldRing", "FieldBinary"> {
  let associative = 1; let commutative = 1; let total = 1;
  let leftIdentity = "One"; let rightIdentity = "One";
  let annihilator = "Zero";
}
def GroupAddLaws : ZKC_ScalarLaws<"GroupModule", "GroupBinary"> {
  let associative = 1; let commutative = 1; let total = 1;
  let leftIdentity = "GroupIdentity"; let rightIdentity = "GroupIdentity";
}
def GroupScaleLaws : ZKC_ScalarLaws<"GroupModule", "GroupAction"> {
  let total = 1; let rightIdentity = "One"; let scalarAction = 1;
}
def ElementAccessLaws : ZKC_ScalarLaws<"Access", "ElementAccess"> {
  let access = "Element";
}
def MatrixAccessLaws : ZKC_ScalarLaws<"Access", "MatrixAccess"> {
  let access = "MatrixCell";
}

def MathFieldAdd : ZKC_MathematicalIdentity<"FieldAdd", 0> { let laws = FieldAddLaws; }
def MathFieldMultiply : ZKC_MathematicalIdentity<"FieldMultiply", 1> { let laws = FieldMultiplyLaws; }
def MathFieldEqual : ZKC_MathematicalIdentity<"FieldEqual", 2>;
def MathGroupIdentity : ZKC_MathematicalIdentity<"GroupIdentity", 3>;
def MathGroupAdd : ZKC_MathematicalIdentity<"GroupAdd", 4> { let laws = GroupAddLaws; }
def MathGroupScale : ZKC_MathematicalIdentity<"GroupScale", 5> { let laws = GroupScaleLaws; }
def MathGroupEqual : ZKC_MathematicalIdentity<"GroupEqual", 6>;
def MathPairing : ZKC_MathematicalIdentity<"Pairing", 7>;
def MathIndexConstant : ZKC_MathematicalIdentity<"IndexConstant", 8>;
def MathIndexEqual : ZKC_MathematicalIdentity<"IndexEqual", 9>;
def MathIndexLess : ZKC_MathematicalIdentity<"IndexLess", 10>;
def MathContainerAt : ZKC_MathematicalIdentity<"ContainerAt", 11> { let laws = ElementAccessLaws; }
def MathMatrixAt : ZKC_MathematicalIdentity<"MatrixAt", 12> { let laws = MatrixAccessLaws; }
def MathBooleanConstant : ZKC_MathematicalIdentity<"BooleanConstant", 13>;
def MathBooleanAnd : ZKC_MathematicalIdentity<"BooleanAnd", 14>;
def MathBooleanOr : ZKC_MathematicalIdentity<"BooleanOr", 15>;
def MathBooleanXor : ZKC_MathematicalIdentity<"BooleanXor", 16>;
def MathBooleanEqual : ZKC_MathematicalIdentity<"BooleanEqual", 17>;
def MathBooleanNotEqual : ZKC_MathematicalIdentity<"BooleanNotEqual", 18>;
def MathSelect : ZKC_MathematicalIdentity<"Select", 19>;
def MathFieldConstant : ZKC_MathematicalIdentity<"FieldConstant", 20> { let laws = FieldConstantLaws; }
def MathFieldSubtract : ZKC_MathematicalIdentity<"FieldSubtract", 21> { let laws = FieldSubtractLaws; }
def MathArrayFromElements : ZKC_MathematicalIdentity<"ArrayFromElements", 22>;
def MathArrayAt : ZKC_MathematicalIdentity<"ArrayAt", 23>;
def MathPolynomialConstant : ZKC_MathematicalIdentity<"PolynomialConstant", 24>;
def MathPolynomialFromCoefficients : ZKC_MathematicalIdentity<"PolynomialFromCoefficients", 25>;
def MathPolynomialMLE : ZKC_MathematicalIdentity<"PolynomialMLE", 26>;
def MathPolynomialAdd : ZKC_MathematicalIdentity<"PolynomialAdd", 27>;
def MathPolynomialMultiply : ZKC_MathematicalIdentity<"PolynomialMultiply", 28>;
def MathPolynomialFix : ZKC_MathematicalIdentity<"PolynomialFix", 29>;
def MathPolynomialSum : ZKC_MathematicalIdentity<"PolynomialSum", 30>;
def MathPolynomialEvaluate : ZKC_MathematicalIdentity<"PolynomialEvaluate", 31>;
def MathPolynomialCoefficients : ZKC_MathematicalIdentity<"PolynomialCoefficients", 32>;
def MathPolynomialEvaluateDomain : ZKC_MathematicalIdentity<"PolynomialEvaluateDomain", 33>;
def MathPolynomialInterpolate : ZKC_MathematicalIdentity<"PolynomialInterpolate", 34>;
def MathPolynomialFixTable : ZKC_MathematicalIdentity<"PolynomialFixTable", 35>;

// Source spellings and ordering are retained independently of native keys.
def IntrinsicContainerAt : ZKC_MathematicalIntrinsic<"container.at", MathContainerAt, "Collection", 0>;
def IntrinsicMatrixAt : ZKC_MathematicalIntrinsic<"matrix.at", MathMatrixAt, "Collection", 1>;
def IntrinsicIndexConstant : ZKC_MathematicalIntrinsic<"index.constant", MathIndexConstant, "Index", 2, 1>;
def IntrinsicIndexEqual : ZKC_MathematicalIntrinsic<"index.equal", MathIndexEqual, "Index", 3, 0, 0, 1>;
def IntrinsicIndexLess : ZKC_MathematicalIntrinsic<"index.less", MathIndexLess, "Index", 4, 0, 0, 1>;
def IntrinsicFieldAdd : ZKC_MathematicalIntrinsic<"field.add", MathFieldAdd, "Field", 5, 0, 0, 1>;
def IntrinsicFieldSubtract : ZKC_MathematicalIntrinsic<"field.sub", MathFieldSubtract, "Field", 6, 0, 0, 1>;
def IntrinsicFieldMultiply : ZKC_MathematicalIntrinsic<"field.mul", MathFieldMultiply, "Field", 7, 0, 0, 1>;
def IntrinsicFieldEqual : ZKC_MathematicalIntrinsic<"field.equal", MathFieldEqual, "Field", 8, 0, 0, 1>;
def IntrinsicGroupIdentity : ZKC_MathematicalIntrinsic<"curve.identity", MathGroupIdentity, "Group", 9, 0, 0, 1>;
def IntrinsicGroupAdd : ZKC_MathematicalIntrinsic<"curve.add", MathGroupAdd, "Group", 10, 0, 0, 1>;
def IntrinsicGroupScale : ZKC_MathematicalIntrinsic<"curve.scale", MathGroupScale, "Group", 11, 0, 0, 1>;
def IntrinsicGroupEqual : ZKC_MathematicalIntrinsic<"curve.equal", MathGroupEqual, "Group", 12, 0, 0, 1>;
def IntrinsicBooleanEqual : ZKC_MathematicalIntrinsic<"bool.equal", MathBooleanEqual, "Boolean", 13, 0, 0, 1>;
def IntrinsicBooleanAnd : ZKC_MathematicalIntrinsic<"bool.and", MathBooleanAnd, "Boolean", 14>;
def IntrinsicBooleanOr : ZKC_MathematicalIntrinsic<"bool.or", MathBooleanOr, "Boolean", 15>;
def IntrinsicBooleanXor : ZKC_MathematicalIntrinsic<"bool.xor", MathBooleanXor, "Boolean", 16>;
def IntrinsicArrayFromElements : ZKC_MathematicalIntrinsic<"array.pack", MathArrayFromElements, "Field", 17, 1>;
def IntrinsicArrayAt : ZKC_MathematicalIntrinsic<"array.at", MathArrayAt, "Field", 18, 2>;
def IntrinsicPolynomialConstant : ZKC_MathematicalIntrinsic<"poly.constant", MathPolynomialConstant, "Field", 19, 1>;
def IntrinsicPolynomialFromCoefficients : ZKC_MathematicalIntrinsic<"poly.from_coefficients", MathPolynomialFromCoefficients, "Field", 20, 1>;
def IntrinsicPolynomialMLE : ZKC_MathematicalIntrinsic<"poly.mle", MathPolynomialMLE, "Field", 21, 1>;
def IntrinsicPolynomialAdd : ZKC_MathematicalIntrinsic<"poly.add", MathPolynomialAdd, "Field", 22, 1>;
def IntrinsicPolynomialMultiply : ZKC_MathematicalIntrinsic<"poly.multiply", MathPolynomialMultiply, "Field", 23, 1>;
def IntrinsicPolynomialFix : ZKC_MathematicalIntrinsic<"poly.fix", MathPolynomialFix, "Field", 24, 2>;
def IntrinsicPolynomialSum : ZKC_MathematicalIntrinsic<"poly.sum_suffix", MathPolynomialSum, "Field", 25, 2>;
def IntrinsicPolynomialEvaluate : ZKC_MathematicalIntrinsic<"poly.evaluate", MathPolynomialEvaluate, "Field", 26, 1>;
def IntrinsicPolynomialCoefficients : ZKC_MathematicalIntrinsic<"poly.coefficients", MathPolynomialCoefficients, "Field", 27, 1>;
def IntrinsicPolynomialEvaluateDomain : ZKC_MathematicalIntrinsic<"poly.evaluate_domain", MathPolynomialEvaluateDomain, "Field", 28, 0, 1>;
def IntrinsicPolynomialInterpolate : ZKC_MathematicalIntrinsic<"poly.interpolate", MathPolynomialInterpolate, "Field", 29, 0, 1>;
def IntrinsicPolynomialFixTable : ZKC_MathematicalIntrinsic<"poly.fix_table", MathPolynomialFixTable, "Field", 30, 2>;

// Append-only source catalogue meanings.
def MathVectorLength : ZKC_MathematicalIdentity<"VectorLength", 36>;
def MathIndexPowerOfTwo : ZKC_MathematicalIdentity<"IndexPowerOfTwo", 37>;
def IntrinsicVectorLength : ZKC_MathematicalIntrinsic<"vector.length", MathVectorLength, "Field", 31>;
def IntrinsicIndexPowerOfTwo : ZKC_MathematicalIntrinsic<"index.power_of_two", MathIndexPowerOfTwo, "Index", 32>;

#endif
