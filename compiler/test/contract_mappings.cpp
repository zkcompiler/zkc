#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Contracts/Kernels.h"
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
    {"transcript.native.indexed.challenge",
     "crypto.exec.indexed_transcript_challenge"},
    {"transcript.native.indexed.observe.data",
     "crypto.exec.indexed_transcript_observe_data"},
    {"field_array.at", "algebra.exec.field_array_at"},
    {"field_array.from_vector", "algebra.exec.field_array_from_vector"},
    {"fixed_vector.from_vector", "algebra.exec.fixed_vector_from_vector"},
    {"fixed_vector.to_vector", "algebra.exec.fixed_vector_to_vector"},
    {"fixed_vector.dot", "algebra.exec.fixed_vector_dot"},
    {"resource_unit.create", "local.exec.resource_unit_create"},
    {"resource_unit.pass", "local.exec.resource_unit_pass"},
    {"resource_unit.consume", "local.exec.resource_unit_consume"},
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
    {"indices.empty", "algebra.exec.indices_empty"},
    {"indices.append", "algebra.exec.indices_append"},
    {"indices.at", "algebra.exec.indices_at"},
    {"indices.length", "algebra.exec.indices_length"},
    {"vector.get", "algebra.exec.vector_get"},
    {"vector.slice", "algebra.exec.vector_slice"},
    {"vector.length", "algebra.exec.vector_length"},
    {"vector.rotate", "algebra.exec.vector_rotate"},
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
    {"poly.coset_interpolate", "poly.exec.coset_interpolate"},
    {"poly.domain_point", "poly.exec.domain_point"},
    {"poly.domain_root", "poly.exec.domain_root"},
    {"poly.domain_points", "poly.exec.domain_points"},
    {"poly.even_odd_fold", "poly.exec.even_odd_fold"},
    {"poly.divide_opening", "poly.exec.divide_opening"},
    {"poly.opening_quotient", "poly.exec.opening_quotient"},
    {"field.sub", "algebra.exec.field_subtract"},
    {"field.neg", "algebra.exec.field_negate"},
    {"field.inverse", "algebra.exec.field_inverse"},
    {"field.embed", "algebra.exec.field_embed"},
    {"matrix.mul_vector", "algebra.exec.matrix_mul_vector"},
    {"matrix.transpose_mul_vector", "algebra.exec.matrix_transpose_mul_vector"},
    {"matrix.bilinear", "algebra.exec.matrix_bilinear"},
    {"matrix.dimension", "algebra.exec.matrix_dimension"},
    {"matrix.shape_check", "algebra.exec.matrix_shape_check"},
    {"matrix.identity_check", "algebra.exec.matrix_identity_check"},
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
    {"field.constant", "algebra.exec.field_constant"},
    {"field.add", "algebra.exec.field_add"},
    {"field.mul", "algebra.exec.field_multiply"},
    {"field.equal", "algebra.exec.field_equal"},
    {"bool.and", "algebra.exec.bool_and"},
    {"bool.not", "algebra.exec.bool_not"},
    {"bool.or", "algebra.exec.bool_or"},
    {"control.require", "local.exec.require"},
    {"poly.product_sum", "poly.exec.product_sum"},
    {"poly.product_round", "poly.exec.product_round"},
    {"poly.boundary", "poly.exec.boundary"},
    {"poly.round_evaluate", "poly.exec.round_evaluate"},
    {"poly.table_arity", "poly.exec.table_arity"},
    {"poly.fold", "poly.exec.fold"},
    {"poly.evaluate", "poly.exec.mle_evaluate"},
    {"poly.empty_point", "poly.exec.empty_point"},
    {"poly.append_point", "poly.exec.append_point"},
    {"oracle.commit", "oracle.exec.commit"},
    {"oracle.open", "oracle.exec.open"},
    {"oracle.check", "oracle.exec.check"},
    {"commitments.empty", "oracle.exec.commitments_empty"},
    {"sequence.empty", "data.exec.sequence_empty"},
    {"sequence.append", "data.exec.sequence_append"},
    {"sequence.length", "data.exec.sequence_length"},
    {"sequence.at", "data.exec.sequence_at"},
    {"commitments.append", "oracle.exec.commitments_append"},
    {"commitments.at", "oracle.exec.commitments_at"},
    {"commitments.length", "oracle.exec.commitments_length"},
    {"opening_states.empty", "oracle.exec.opening_states_empty"},
    {"opening_states.append", "oracle.exec.opening_states_append"},
    {"opening_states.at", "oracle.exec.opening_states_at"},
    {"opening_states.length", "oracle.exec.opening_states_length"},
    {"pcs.commit", "pcs.exec.commit"},
    {"pcs.open", "pcs.exec.open"},
    {"pcs.check", "pcs.exec.check"},
    {"random.index", "crypto.exec.random_index"},
    {"random.draw", "crypto.exec.random_draw"},
    {"pcs.equal", "pcs.exec.equal"},
    {"curve.generator", "algebra.exec.group_generator"},
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
  for (const auto &kernel : protocol::kernels())
    check(installed.insert(kernel.key).second, "duplicate installed contract");
  for (const auto &row : expected) {
    check(covered.insert(row.contract).second, "duplicate expected contract");
    check(installed.contains(row.contract),
          "uninstalled oracle: " + row.contract);
    check(context.isOperationRegistered(row.operation),
          "unregistered expected operation: " + row.operation);
    check(protocol::boundOperationName(row.contract) == row.operation,
          "wrong imported identity for " + row.contract + ": expected " +
              row.operation);
    // Check the complete cross product of exact contract mappings.
    // Neither expected side is computed with the production forward mapping.
    for (const auto &other : expected)
      check(
          protocol::operationSupportsContract(row.operation, other.contract) ==
              (row.operation == other.operation),
          "wrong operation-side association: " + row.operation + " / " +
              other.contract);
  }
  for (const auto &kernel : protocol::kernels())
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

// A deliberately tiny independent interpreter for the two imported mnemonics.
// Small values do not wrap in koala-bear. This is a discriminating identity
// vector, not a production backend execution or a general field interpreter.
void arithmeticVector(zkc::local::FuncOp function, uint64_t x, uint64_t y,
                      uint64_t sum, uint64_t product) {
  llvm::DenseMap<Value, uint64_t> values;
  values[function.getArgument(0)] = x;
  values[function.getArgument(1)] = y;
  for (auto &op : function.getBody().front()) {
    if (auto ret = dyn_cast<zkc::local::ReturnOp>(op)) {
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
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["koala-bear"],implementation=""} : ()->()
 "local.binding"() {sym_name="mul",contract="field.mul",arguments=["koala-bear"],implementation=""} : ()->()
 local.func @Arithmetic(%x:!F,%y:!F)->(!F,!F) attributes {logical_origin=["Arithmetic",[]]} {
   %sum = "algebra.exec.field_add"(%x,%y) {binding=@add,site="add_site",parameters=[]} : (!F,!F)->!F
   %product = "algebra.exec.field_multiply"(%x,%y) {binding=@mul,site="mul_site",parameters=[]} : (!F,!F)->!F
   local.return %sum,%product : !F,!F
 }
 "protocol.func"() ({^entry(%x:!F,%y:!F):
   %out:2 = "protocol.local_call"(%x,%y) {callee=@Arithmetic,role="P",site="work"} : (!F,!F)->(!F,!F)
   "protocol.return"(%out#0,%out#1) : (!F,!F)->()
 }) {sym_name="main",function_type=(!F,!F)->(!F,!F),roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)",
                                                    &context);
  if (!check(bool(imported), "mathematical arithmetic fixture refused"))
    return;
  check(succeeded(verify(*imported)), "arithmetic fixture rejected");
  unsigned sites = 0, functions = 0;
  imported->walk([&](zkc::local::FuncOp function) {
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
    check(succeeded(protocol::verifyBoundOperation(op, false)),
          "valid binding refused before swap");
    auto original = op->getAttr("binding");
    op->setAttr("binding",
                FlatSymbolRefAttr::get(&context, isAdd ? "mul" : "add"));
    std::vector<diagnostics::RefusalInfo> refusals;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      llvm::append_range(refusals, diagnostics::refusals(diagnostic));
      return success();
    });
    check(failed(protocol::verifyBoundOperation(op, false)),
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
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  identities(context);
  importedArithmetic(context);
  outs() << checks << " mapping checks, " << failures << " failures\n";
  return failures ? 1 : 0;
}
