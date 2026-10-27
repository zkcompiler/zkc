#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>

using namespace llvm;
using namespace mlir;
using namespace zkc;

namespace {
unsigned checks = 0, failures = 0;
bool check(bool condition, const Twine &message) {
  ++checks;
  if (!condition) {
    ++failures;
    errs() << message << '\n';
  }
  return condition;
}

struct ExpectedMapping {
  StringLiteral contract;
  StringLiteral operation;
};

// Independent, literal expectations. Do not generate this oracle from ODS,
// boundOperationName, operationSupportsContract, or C++ operation classes.
// Contract spelling and IR mnemonic intentionally differ in several families.
constexpr ExpectedMapping expected[] = {
    {"quotient.prepare_matrix", "runtime.prepare_quotient_matrix"},
    {"quotient.matvec", "runtime.quotient_matvec"},
    {"quotient.add", "poly.exec.quotient_add"},
    {"quotient.subtract", "poly.exec.quotient_subtract"},
    {"quotient.multiply", "poly.exec.quotient_multiply"},
    {"quotient.norm_within", "poly.exec.quotient_norm_within"},
    {"quotient.project", "poly.exec.quotient_project"},
    {"quotient.ntt", "poly.exec.quotient_ntt"},
    {"quotient.intt", "poly.exec.quotient_intt"},
    {"quotient.pointwise", "poly.exec.quotient_pointwise"},
    {"transcript.observe", "crypto.exec.transcript_observe"},
    {"transcript.challenge", "crypto.exec.transcript_challenge"},
    {"transcript.index", "crypto.exec.transcript_index"},
    {"ring.point", "algebra.exec.ring_point"},
    {"ring.rows", "algebra.exec.ring_rows"},
    {"ring.coefficients", "algebra.exec.ring_coefficients"},
    {"ring.affine_sum", "algebra.exec.ring_affine_sum"},
    {"relation.table_rows", "relation.exec.table_rows"},
    {"relation.table_shape", "relation.exec.table_shape"},
    {"relation.table_input", "relation.exec.table_input"},
    {"relation.table_scope", "relation.exec.table_scope"},
    {"relation.table_point", "relation.exec.table_point"},
    {"relation.table_points", "relation.exec.table_points"},
    {"relation.table_widths", "relation.exec.table_widths"},
    {"relation.table_policy", "relation.exec.table_policy"},
    {"relation.table_interactions", "relation.exec.table_interactions"},
    {"relation.table_interaction", "relation.exec.table_interaction"},
    {"relation.table_record_points", "relation.exec.table_record_points"},
    {"transcript.native.indexed.challenge",
     "crypto.exec.indexed_transcript_challenge"},
    {"transcript.native.indexed.observe.data",
     "crypto.exec.indexed_transcript_observe_data"},
    {"transcript.native.indexed.index", "crypto.exec.indexed_transcript_index"},
    {"field_array.at", "algebra.exec.field_array_at"},
    {"field_array.get", "algebra.exec.field_array_get"},
    {"field_array.from_vector", "algebra.exec.field_array_from_vector"},
    {"fixed_vector.from_vector", "algebra.exec.fixed_vector_from_vector"},
    {"fixed_vector.to_vector", "algebra.exec.fixed_vector_to_vector"},
    {"fixed_vector.dot", "algebra.exec.fixed_vector_dot"},
    {"resource_unit.create", ""},
    {"resource_unit.pass", ""},
    {"resource_unit.consume", ""},
    {"external.monero.init", "crypto.exec.monero_init"},
    {"external.monero.hash", "crypto.exec.monero_hash"},
    {"external.monero.update", "crypto.exec.monero_update"},
    {"external.openvm.init", "crypto.exec.openvm_init"},
    {"external.openvm.observe", "crypto.exec.openvm_observe"},
    {"external.openvm.sample", "crypto.exec.openvm_sample"},
    {"external.openvm.sample_ext", "crypto.exec.openvm_sample_ext"},
    {"external.openvm.sample_bits", "crypto.exec.openvm_sample_bits"},
    {"external.openvm.check_witness", "crypto.exec.openvm_check_witness"},
    {"index.constant", "algebra.exec.index_constant"},
    {"index.add", "algebra.exec.index_add"},
    {"index.sub", "algebra.exec.index_sub"},
    {"index.mul", "algebra.exec.index_mul"},
    {"index.div", "algebra.exec.index_div"},
    {"index.mod", "algebra.exec.index_mod"},
    {"index.equal", "algebra.exec.index_equal"},
    {"index.less", "algebra.exec.index_less"},
    {"encoding.field_le", "crypto.exec.encoding_field_le"},
    {"encoding.field_from_le", "crypto.exec.encoding_field_from_le"},
    {"encoding.field_reduce_le", "crypto.exec.encoding_field_reduce_le"},
    {"encoding.fields_from_le", "crypto.exec.encoding_fields_from_le"},
    {"encoding.field_montgomery_le",
     "crypto.exec.encoding_field_montgomery_le"},
    {"encoding.field_from_montgomery_le",
     "crypto.exec.encoding_field_from_montgomery_le"},
    {"encoding.fields_montgomery_le",
     "crypto.exec.encoding_fields_montgomery_le"},
    {"encoding.fields_from_montgomery_le",
     "crypto.exec.encoding_fields_from_montgomery_le"},
    {"encoding.group_decode_cofactor",
     "crypto.exec.encoding_group_decode_cofactor"},
    {"encoding.cryptonote_map", "crypto.exec.encoding_cryptonote_map"},
    {"hash.keccak256", "crypto.exec.keccak256"},
    {"hash.sha256", "crypto.exec.sha256"},
    {"hash.poseidon2_16", "crypto.exec.poseidon2_16"},
    {"encoding.index_uleb128", "data.exec.encoding_index_uleb128"},
    {"encoding.fields_be", "crypto.exec.encoding_fields_be"},
    {"encoding.fields_from_be", "crypto.exec.encoding_fields_from_be"},
    {"encoding.fields_le", "crypto.exec.encoding_fields_le"},
    {"encoding.groups_compressed", "crypto.exec.encoding_groups_compressed"},
    {"encoding.field_be", "crypto.exec.encoding_field_be"},
    {"encoding.field_from_be", "crypto.exec.encoding_field_from_be"},
    {"encoding.field_reduce_be", "crypto.exec.encoding_field_reduce_be"},
    {"encoding.group_compressed", "crypto.exec.encoding_group_compressed"},
    {"encoding.group_from_compressed",
     "crypto.exec.encoding_group_from_compressed"},
    {"shake128.init", "crypto.exec.shake128_init"},
    {"shake128.absorb", "crypto.exec.shake128_absorb"},
    {"shake128.squeeze", "crypto.exec.shake128_squeeze"},
    {"bytes.repeat", "data.exec.bytes_repeat"},
    {"bytes.join", "data.exec.bytes_join"},
    {"bytes.empty", "data.exec.bytes_empty"},
    {"bytes.append", "data.exec.bytes_append"},
    {"bytes.concat", "data.exec.bytes_concat"},
    {"bytes.slice", "data.exec.bytes_slice"},
    {"bytes.at", "data.exec.bytes_at"},
    {"bytes.length", "data.exec.bytes_length"},
    {"bytes.equal", "data.exec.bytes_equal"},
    {"indices.empty", "algebra.exec.indices_empty"},
    {"indices.append", "algebra.exec.indices_append"},
    {"indices.at", "algebra.exec.indices_at"},
    {"indices.length", "algebra.exec.indices_length"},
    {"vector.get", "algebra.exec.vector_get"},
    {"vector.slice", "algebra.exec.vector_slice"},
    {"vector.transpose", "algebra.exec.vector_transpose"},
    {"vector.length", "algebra.exec.vector_length"},
    {"vector.rotate", "algebra.exec.vector_rotate"},
    {"vector.bit_reverse", "algebra.exec.vector_bit_reverse"},
    {"vector.bit_reverse_rows", "algebra.exec.vector_bit_reverse_rows"},
    {"vector.interleave", "algebra.exec.vector_interleave"},
    {"vector.prefix_product", "algebra.exec.vector_prefix_product"},
    {"vector.prefix_sum", "algebra.exec.vector_prefix_sum"},
    {"vector.inverse", "algebra.exec.vector_inverse"},
    {"vector.embed", "algebra.exec.vector_embed"},
    {"vector.fill", "algebra.exec.vector_fill"},
    {"vector.geometric", "algebra.exec.vector_geometric"},
    {"field.from_index", "algebra.exec.field_from_index"},
    {"poly.coefficient_count", "poly.exec.coefficient_count"},
    {"poly.coset_evaluate", "poly.exec.coset_evaluate"},
    {"poly.coset_evaluate_batch", "poly.exec.coset_evaluate_batch"},
    {"poly.coset_extend", "poly.exec.coset_extend"},
    {"poly.coset_evaluate_at", "poly.exec.coset_evaluate_at"},
    {"poly.coset_interpolate", "poly.exec.coset_interpolate"},
    {"poly.domain_point", "poly.exec.domain_point"},
    {"poly.domain_root", "poly.exec.domain_root"},
    {"poly.domain_points", "poly.exec.domain_points"},
    {"poly.even_odd_fold", "poly.exec.even_odd_fold"},
    {"poly.divide_opening", "poly.exec.divide_opening"},
    {"poly.opening_quotient", "poly.exec.opening_quotient"},
    {"poly.opening_quotient_sum", "poly.exec.opening_quotient_sum"},
    {"field.sub", "algebra.exec.field_subtract"},
    {"field.neg", "algebra.exec.field_negate"},
    {"field.inverse", "algebra.exec.field_inverse"},
    {"field.embed", "algebra.exec.field_embed"},
    {"matrix.mul_vector", "algebra.exec.matrix_mul_vector"},
    {"matrix.transpose_mul_vector", "algebra.exec.matrix_transpose_mul_vector"},
    {"matrix.bilinear", "algebra.exec.matrix_bilinear"},
    {"matrix.dimension", "algebra.exec.matrix_dimension"},
    {"matrix.get", "algebra.exec.matrix_get"},
    {"matrix.row_dot", "algebra.exec.matrix_row_dot"},
    {"matrix.column_dot", "algebra.exec.matrix_column_dot"},
    {"matrix.shape_check", "algebra.exec.matrix_shape_check"},
    {"matrix.identity_check", "algebra.exec.matrix_identity_check"},
    {"numerical.map", "algebra.exec.numerical_map"},
    {"numerical.sum", "algebra.exec.numerical_sum"},
    {"numerical.product", "algebra.exec.numerical_product"},
    {"vector.constant", "algebra.exec.vector_constant"},
    {"vector.scatter_sum", "algebra.exec.vector_scatter_sum"},
    {"vector.empty", "algebra.exec.vector_empty"},
    {"vector.append", "algebra.exec.vector_append"},
    {"vector.splat", "algebra.exec.vector_splat"},
    {"vector.powers", "algebra.exec.vector_powers"},
    {"vector.add", "algebra.exec.vector_add"},
    {"vector.sub", "algebra.exec.vector_sub"},
    {"vector.mul", "algebra.exec.vector_mul"},
    {"vector.dot", "algebra.exec.vector_dot"},
    {"vector.concat", "algebra.exec.vector_concat"},
    {"vector.kronecker", "algebra.exec.vector_kronecker"},
    {"vector.matvec", "algebra.exec.vector_matvec"},
    {"vector.scale", "algebra.exec.vector_scale"},
    {"vector.sum", "algebra.exec.vector_sum"},
    {"vector.product", "algebra.exec.vector_product"},
    {"vector.split", "algebra.exec.vector_split"},
    {"vector.at", "algebra.exec.vector_at"},
    {"vector.length_check", "algebra.exec.vector_length_check"},
    {"vector.gather", "algebra.exec.vector_gather"},
    {"vector.from_point", "poly.exec.point_to_vector"},
    {"vector.from_table", "poly.exec.table_to_vector"},
    {"vector.to_point", "poly.exec.point_from_vector"},
    {"vector.to_table", "poly.exec.table_from_vector"},
    {"poly.equality_weights", "poly.exec.equality_weights"},
    {"poly.from_coefficients", "poly.exec.from_coefficients"},
    {"poly.coefficients", "poly.exec.coefficients"},
    {"poly.degree_check", "poly.exec.degree_check"},
    {"poly.univariate_evaluate", "poly.exec.univariate_evaluate"},
    {"poly.univariate_boundary", "poly.exec.univariate_boundary"},
    {"random.vector", "crypto.exec.random_vector"},
    {"curve.neg", "algebra.exec.group_negate"},
    {"curve.nonidentity", "algebra.exec.group_nonidentity"},
    {"curve.msm", "algebra.exec.group_msm"},
    {"curve.scale_each", "algebra.exec.group_scale_each"},
    {"curve.vector_add", "algebra.exec.group_vector_add"},
    {"curve.vector_scale", "algebra.exec.group_vector_scale"},
    {"curve.split", "algebra.exec.group_split"},
    {"curve.concat", "algebra.exec.group_concat"},
    {"pairing.check", "algebra.exec.pairing_check"},
    {"pairing.apply", "algebra.exec.pairing"},
    {"vector.equal", "algebra.exec.vector_equal"},
    {"vector.find_last", "algebra.exec.vector_find_last"},
    {"field.constant", "algebra.exec.field_constant"},
    {"field.add", "algebra.exec.field_add"},
    {"field.mul", "algebra.exec.field_multiply"},
    {"field.equal", "algebra.exec.field_equal"},
    {"bool.and", "algebra.exec.bool_and"},
    {"bool.not", "algebra.exec.bool_not"},
    {"bool.or", "algebra.exec.bool_or"},
    {"control.require", ""},
    {"poly.product_sum", "poly.exec.product_sum"},
    {"poly.product_round", "poly.exec.product_round"},
    {"poly.boundary", "poly.exec.boundary"},
    {"poly.round_evaluate", "poly.exec.round_evaluate"},
    {"poly.table_arity", "poly.exec.table_arity"},
    {"poly.fold", "poly.exec.fold"},
    {"poly.evaluate", "poly.exec.mle_evaluate"},
    {"poly.empty_point", "poly.exec.empty_point"},
    {"poly.append_point", "poly.exec.append_point"},
    {"oracle.commit", "commitment.exec.vector_commit"},
    {"oracle.open", "commitment.exec.vector_open"},
    {"oracle.check", "commitment.exec.vector_check"},
    {"oracle.open_many", "commitment.exec.vector_open_many"},
    {"oracle.check_many", "commitment.exec.vector_check_many"},
    {"commitments.empty", "commitment.exec.commitments_empty"},
    {"sequence.empty", "data.exec.sequence_empty"},
    {"sequence.append", "data.exec.sequence_append"},
    {"sequence.length", "data.exec.sequence_length"},
    {"sequence.at", "data.exec.sequence_at"},
    {"commitments.append", "commitment.exec.commitments_append"},
    {"commitments.at", "commitment.exec.commitments_at"},
    {"commitments.length", "commitment.exec.commitments_length"},
    {"opening_states.empty", "commitment.exec.opening_states_empty"},
    {"opening_states.append", "commitment.exec.opening_states_append"},
    {"opening_states.at", "commitment.exec.opening_states_at"},
    {"opening_states.length", "commitment.exec.opening_states_length"},
    {"pcs.commit", "commitment.exec.polynomial_commit"},
    {"pcs.open", "commitment.exec.polynomial_open"},
    {"pcs.check", "commitment.exec.polynomial_check"},
    {"random.index", "crypto.exec.random_index"},
    {"random.draw", "crypto.exec.random_draw"},
    {"pcs.equal", "commitment.exec.polynomial_equal"},
    {"curve.generator", "algebra.exec.group_generator"},
    {"curve.identity", "algebra.exec.group_identity"},
    {"curve.add", "algebra.exec.group_add"},
    {"curve.scale", "algebra.exec.group_scale"},
    {"curve.equal", "algebra.exec.group_equal"},
    {"curve.empty", "algebra.exec.group_empty"},
    {"curve.append", "algebra.exec.group_append"},
    {"curve.at", "algebra.exec.group_at"},
    {"curve.get", "algebra.exec.group_get"},
    {"curve.length", "algebra.exec.group_length"},
    {"curve.commit", "crypto.exec.curve_commit"},
    {"curve.response", "crypto.exec.curve_response"},
};

void identities(MLIRContext &context) {
  llvm::StringSet<> installed, covered;
  for (const auto &kernel : protocol::operationShapes())
    check(installed.insert(kernel.key).second, "duplicate installed contract");
  for (const auto &row : expected) {
    check(covered.insert(row.contract).second, "duplicate expected contract");
    check(installed.contains(row.contract),
          "uninstalled oracle: " + row.contract);
    check(row.operation.empty() || context.isOperationRegistered(row.operation),
          "unregistered expected operation: " + row.operation);
    check(protocol::boundOperationName(row.contract) == row.operation,
          "wrong imported identity for " + row.contract + ": expected " +
              row.operation);
    // Check the complete cross product of exact contract mappings.
    // Neither expected side is computed with the production forward mapping.
    for (const auto &other : expected)
      check(
          protocol::operationSupportsContract(row.operation, other.contract) ==
              (!row.operation.empty() && row.operation == other.operation),
          "wrong operation-side association: " + row.operation + " / " +
              other.contract);
  }
  for (const auto &kernel : protocol::operationShapes())
    check(covered.contains(kernel.key),
          "missing independent oracle: " + kernel.key);

  for (StringRef unknown :
       {"", "invalid.contract", "algebra.exec.field_add", "Field.add",
        "field.add.extra", "transcript.native.indexed.observe.data.extra"}) {
    check(protocol::boundOperationName(unknown).empty(),
          "unknown contract mapped: " + unknown);
    for (const auto &row : expected)
      check(!protocol::operationSupportsContract(row.operation, unknown),
            "operation accepted unknown contract: " + unknown);
  }
  for (StringRef unknown :
       {"", "invalid.operation", "field.add", "algebra.exec.field_add.extra"})
    for (const auto &row : expected)
      check(!protocol::operationSupportsContract(unknown, row.contract),
            "unmapped operation accepted contract: " + unknown);
}

// Typed numerical adapters remain independently verified before scoped
// realization; these fixtures deliberately exercise their local invariants.
// A deliberately tiny independent interpreter for the two imported mnemonics.
// Small values do not wrap in koala-bear. This is a discriminating identity
// vector, not a production backend execution or a general field interpreter.
void arithmeticVector(func::FuncOp function, uint64_t x, uint64_t y,
                      uint64_t sum, uint64_t product) {
  llvm::DenseMap<Value, uint64_t> values;
  values[function.getArgument(0)] = x;
  values[function.getArgument(1)] = y;
  for (auto &op : function.getBody().front()) {
    if (auto ret = dyn_cast<func::ReturnOp>(op)) {
      if (!check(ret.getNumOperands() == 2, "arithmetic return arity"))
        return;
      auto left = values.find(ret.getOperand(0));
      auto right = values.find(ret.getOperand(1));
      if (!check(left != values.end() && right != values.end(),
                 "arithmetic return refers to unknown value"))
        return;
      check(left->second == sum && right->second == product,
            "imported add/mul behavior changed for (" + Twine(x) + ", " +
                Twine(y) + ")");
      return;
    }
    auto name = op.getName().getStringRef();
    if (!check((name == "algebra.exec.field_add" ||
                name == "algebra.exec.field_multiply") &&
                   op.getNumOperands() == 2 && op.getNumResults() == 1,
               "unexpected arithmetic operation: " + name))
      return;
    auto left = values.find(op.getOperand(0));
    auto right = values.find(op.getOperand(1));
    if (!check(left != values.end() && right != values.end(),
               "arithmetic operation refers to unknown value"))
      return;
    values[op.getResult(0)] = name == "algebra.exec.field_add"
                                  ? left->second + right->second
                                  : left->second * right->second;
  }
  check(false, "missing arithmetic return");
}

void importedArithmetic(MLIRContext &context) {
  auto imported = mlir::parseSourceString<ModuleOp>(R"(
!F = !algebra.field<"koala-bear">
module {
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["koala-bear"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["koala-bear"],implementation=""} : ()->()
 func.func @Arithmetic(%x:!F,%y:!F)->(!F,!F) {
   %sum = "algebra.exec.field_add"(%x,%y) {binding=@add,site="add_site",parameters=[]} : (!F,!F)->!F
   %product = "algebra.exec.field_multiply"(%x,%y) {binding=@mul,site="mul_site",parameters=[]} : (!F,!F)->!F
   func.return %sum,%product : !F,!F
 }
}

)",
                                                    &context);
  if (!check(bool(imported), "mathematical arithmetic fixture refused"))
    return;
  check(succeeded(verify(*imported)), "arithmetic fixture rejected");
  unsigned sites = 0, functions = 0;
  imported->walk([&](func::FuncOp function) {
    ++functions;
    arithmeticVector(function, 2, 3, 5, 6);
    arithmeticVector(function, 0, 7, 7, 0);
  });
  check(functions == 1, "expected one arithmetic function");
  imported->walk([&](Operation *op) {
    if (!op->hasAttr("binding"))
      return;
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!site)
      return;
    ++sites;
    bool isAdd = site.getValue() == "add_site";
    if (!check(isAdd || site.getValue() == "mul_site", "unexpected site"))
      return;
    check(
        op->getName().getStringRef() ==
            (isAdd ? "algebra.exec.field_add" : "algebra.exec.field_multiply"),
        "actual imported add/mul identity swapped: " + site.getValue());
    check(succeeded(protocol::verifyBoundOperation(op)),
          "valid binding refused before swap");
    auto original = op->getAttr("binding");
    op->setAttr("binding",
                FlatSymbolRefAttr::get(&context, isAdd ? "mul" : "add"));
    std::vector<diagnostics::RefusalInfo> refusals;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      llvm::append_range(refusals, diagnostics::refusals(diagnostic));
      return success();
    });
    check(failed(protocol::verifyBoundOperation(op)),
          "same-signature wrong binding passed adapter verifier");
    check(llvm::any_of(refusals,
                       [](const auto &info) {
                         return info.code == "binding-operation";
                       }),
          "wrong binding lost binding-operation identifier");
    refusals.clear();
    check(failed(op->getName().verifyInvariants(op)),
          "same-signature wrong binding passed registered op verifier");
    check(llvm::any_of(refusals,
                       [](const auto &info) {
                         return info.code == "binding-operation";
                       }),
          "registered verifier lost binding-operation identifier");
    op->setAttr("binding", original);
    check(succeeded(op->getName().verifyInvariants(op)),
          "restored binding failed registered verifier");
  });
  check(sites == 2, "arithmetic import lost or duplicated sites");
}
void importedProduct(MLIRContext &context) {
  auto imported = mlir::parseSourceString<ModuleOp>(R"(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module {
 "runtime.binding"() {sym_name="product",contract="vector.product",arguments=["koala-bear"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="other",contract="vector.product",arguments=["bn254.fr"],implementation=""} : ()->()
 func.func @Product(%xs:!V)->!F {
   %result = "algebra.exec.vector_product"(%xs) {binding=@product,site="product_site",parameters=[]} : (!V)->!F
   func.return %result : !F
 }
}

)",
                                                    &context);
  if (!check(bool(imported), "product fixture refused"))
    return;
  check(succeeded(verify(*imported)), "product fixture rejected");
  unsigned sites = 0;
  imported->walk([&](Operation *op) {
    if (op->getName().getStringRef() != "algebra.exec.vector_product")
      return;
    ++sites;
    std::vector<diagnostics::RefusalInfo> refusals;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      llvm::append_range(refusals, diagnostics::refusals(diagnostic));
      return success();
    });
    auto refuses = [&](StringRef code) {
      refusals.clear();
      check(failed(op->getName().verifyInvariants(op)),
            "product mutation admitted");
      check(llvm::any_of(refusals,
                         [&](const auto &info) { return info.code == code; }),
            "product mutation lost refusal identifier: " + code);
    };
    auto original = op->getAttr("binding");
    op->setAttr("binding", FlatSymbolRefAttr::get(&context, "sum"));
    refuses("binding-operation");
    op->setAttr("binding", FlatSymbolRefAttr::get(&context, "other"));
    refuses("binding-operation-signature");
    op->setAttr("binding", original);
    auto scalarType = op->getResult(0).getType();
    op->getResult(0).setType(op->getOperand(0).getType());
    refuses("binding-operation-signature");
    op->getResult(0).setType(scalarType);
    auto vectorType = op->getOperand(0).getType();
    op->getOperand(0).setType(scalarType);
    refuses("binding-operation-signature");
    op->getOperand(0).setType(vectorType);
    auto input = op->getOperand(0);
    op->setOperands(ValueRange{});
    refuses("binding-operation-signature");
    op->setOperands(ValueRange{input});
    check(succeeded(op->getName().verifyInvariants(op)),
          "restored product refused");
  });
  check(sites == 1, "product import lost or duplicated its occurrence");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  identities(context);
  importedArithmetic(context);
  importedProduct(context);
  outs() << checks << " mapping checks, " << failures << " failures\n";
  return failures ? 1 : 0;
}
