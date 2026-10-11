// Private, closed algorithm associations. Endpoint declarations retain their
// own scopes; staticArguments maps each target root to the source scope.
class ZKC_LaneRecipe<ZKC_Operation scalar, ZKC_Operation rows,
                     list<int> order = [0, 1]> {
  ZKC_Operation source = scalar;
  ZKC_Operation target = rows;
  list<int> operands = order;
  list<int> staticArguments = [0];
  ZKC_Operation mixed = ?;
  int scalarOperand = 1;
}
class ZKC_ReductionRecipe<ZKC_Operation combine, ZKC_Operation target,
                          string form, list<int> order = [0, 1]> {
  ZKC_Operation source = combine;
  ZKC_Operation endpoint = target;
  string kind = form;
  ZKC_Operation term = ?;
  list<int> operands = order;
  list<int> staticArguments = [0];
  // Domain arguments come from this operand in semantic source order. Group
  // actions use the group input even though MSM's native first input is scalar.
  int staticSourceOperand = 0;
}

// Closed matrix contraction algorithms. The form determines semantic input
// roles, free/reduced matrix axes and scalar versus lane-wise seed combining.
// The scalar declarations retain ownership of the underlying field laws.
class ZKC_MatrixContractionRecipe<ZKC_Operation combine, ZKC_Operation product,
    ZKC_Operation target, string form, ZKC_Operation seedCombine,
    list<int> order, list<int> free, list<int> reduced> {
  ZKC_Operation source = combine;
  ZKC_Operation term = product;
  ZKC_Operation endpoint = target;
  ZKC_Operation seedCombiner = seedCombine;
  string kind = form;
  list<int> operands = order;
  list<int> freeAxes = free;
  list<int> reducedAxes = reduced;
  list<int> staticArguments = [0];
}
