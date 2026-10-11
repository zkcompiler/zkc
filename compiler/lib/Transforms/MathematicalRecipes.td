include "zkc/Contracts/Installation.td"

include "lib/Transforms/RecipeSchema.td"

def FieldAddLanes : ZKC_LaneRecipe<OpFieldAdd, OpVectorAdd>;
def FieldSubtractLanes : ZKC_LaneRecipe<OpFieldSub, OpVectorSub>;
def FieldMultiplyLanes : ZKC_LaneRecipe<OpFieldMul, OpVectorMul> {
  let mixed = OpVectorScale;
}
def GroupAddLanes : ZKC_LaneRecipe<OpCurveAdd, OpCurveVectorAdd>;
def GroupScaleLanes : ZKC_LaneRecipe<OpCurveScale, OpCurveScaleEach, [1, 0]>;

def FieldSum : ZKC_ReductionRecipe<OpFieldAdd, OpVectorSum, "Direct", [0]>;
def FieldProduct : ZKC_ReductionRecipe<OpFieldMul, OpVectorProduct, "Direct", [0]>;
def FieldDot : ZKC_ReductionRecipe<OpFieldAdd, OpVectorDot, "Contraction"> {
  let term = OpFieldMul;
}
def GroupMultiscalar : ZKC_ReductionRecipe<OpCurveAdd, OpCurveMsm, "Contraction", [1, 0]> {
  let term = OpCurveScale;
}
// Matrix forms interpret operand zero as the semantic matrix role, and append
// the selected index after the two collection inputs.
def MatrixRowDot : ZKC_ReductionRecipe<OpFieldAdd, OpMatrixRowDot, "MatrixRow"> {
  let term = OpFieldMul;
}
def MatrixColumnDot : ZKC_ReductionRecipe<OpFieldAdd, OpMatrixColumnDot, "MatrixColumn"> {
  let term = OpFieldMul;
}
