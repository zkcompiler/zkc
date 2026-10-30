include "zkc/Contracts/Installation.td"

include "lib/Transforms/RecipeSchema.td"

def FieldAddLanes : ZKC_LaneRecipe<CatalogOperation_field_2eadd, CatalogOperation_vector_2eadd>;
def FieldSubtractLanes : ZKC_LaneRecipe<CatalogOperation_field_2esub, CatalogOperation_vector_2esub>;
def FieldMultiplyLanes : ZKC_LaneRecipe<CatalogOperation_field_2emul, CatalogOperation_vector_2emul> {
  let mixed = CatalogOperation_vector_2escale;
}
def GroupAddLanes : ZKC_LaneRecipe<CatalogOperation_curve_2eadd, CatalogOperation_curve_2evector_5fadd>;
def GroupScaleLanes : ZKC_LaneRecipe<CatalogOperation_curve_2escale, CatalogOperation_curve_2escale_5feach, [1, 0]>;

def FieldSum : ZKC_ReductionRecipe<CatalogOperation_field_2eadd, CatalogOperation_vector_2esum, "Direct", [0]>;
def FieldProduct : ZKC_ReductionRecipe<CatalogOperation_field_2emul, CatalogOperation_vector_2eproduct, "Direct", [0]>;
def FieldDot : ZKC_ReductionRecipe<CatalogOperation_field_2eadd, CatalogOperation_vector_2edot, "Contraction"> {
  let term = CatalogOperation_field_2emul;
}
def GroupMultiscalar : ZKC_ReductionRecipe<CatalogOperation_curve_2eadd, CatalogOperation_curve_2emsm, "Contraction", [1, 0]> {
  let term = CatalogOperation_curve_2escale;
}
// Matrix forms interpret operand zero as the semantic matrix role, and append
// the selected index after the two collection inputs.
def MatrixRowDot : ZKC_ReductionRecipe<CatalogOperation_field_2eadd, CatalogOperation_matrix_2erow_5fdot, "MatrixRow"> {
  let term = CatalogOperation_field_2emul;
}
def MatrixColumnDot : ZKC_ReductionRecipe<CatalogOperation_field_2eadd, CatalogOperation_matrix_2ecolumn_5fdot, "MatrixColumn"> {
  let term = CatalogOperation_field_2emul;
}

def MatrixBilinear : ZKC_MatrixContractionRecipe<CatalogOperation_field_2eadd, CatalogOperation_field_2emul,
    CatalogOperation_matrix_2ebilinear, "Bilinear", CatalogOperation_field_2eadd, [0, 1, 2], [], [0, 1]>;
def MatrixRows : ZKC_MatrixContractionRecipe<CatalogOperation_field_2eadd, CatalogOperation_field_2emul,
    CatalogOperation_matrix_2emul_5fvector, "Rows", CatalogOperation_vector_2eadd, [0, 1], [0], [1]>;
def MatrixColumns : ZKC_MatrixContractionRecipe<CatalogOperation_field_2eadd, CatalogOperation_field_2emul,
    CatalogOperation_matrix_2etranspose_5fmul_5fvector, "Columns", CatalogOperation_vector_2eadd, [0, 1], [1], [0]>;
