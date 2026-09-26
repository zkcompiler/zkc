#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Translation/Protocol.h"
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
    {"resource_unit.create", "pir.resource_unit_create"},
    {"resource_unit.pass", "pir.resource_unit_pass"},
    {"resource_unit.consume", "pir.resource_unit_consume"},
    {"external.monero.init", "algebra.external_monero_init"},
    {"external.monero.hash", "algebra.external_monero_hash"},
    {"external.monero.update", "algebra.external_monero_update"},
    {"external.openvm.init", "algebra.external_openvm_init"},
    {"external.openvm.observe", "algebra.external_openvm_observe"},
    {"external.openvm.sample", "algebra.external_openvm_sample"},
    {"external.openvm.sample_ext", "algebra.external_openvm_sample_ext"},
    {"external.openvm.sample_bits", "algebra.external_openvm_sample_bits"},
    {"external.openvm.check_witness", "algebra.external_openvm_check_witness"},
    {"index.constant", "algebra.index_constant"},
    {"index.add", "algebra.index_add"},
    {"index.sub", "algebra.index_sub"},
    {"index.mul", "algebra.index_mul"},
    {"index.div", "algebra.index_div"},
    {"index.mod", "algebra.index_mod"},
    {"index.equal", "algebra.index_equal"},
    {"index.less", "algebra.index_less"},
    {"indices.empty", "algebra.indices_empty"},
    {"indices.append", "algebra.indices_append"},
    {"indices.at", "algebra.indices_at"},
    {"indices.length", "algebra.indices_length"},
    {"vector.get", "algebra.vector_get"},
    {"vector.slice", "algebra.vector_slice"},
    {"vector.length", "algebra.vector_length"},
    {"vector.rotate", "algebra.vector_rotate"},
    {"vector.interleave", "algebra.vector_interleave"},
    {"vector.prefix_product", "algebra.vector_prefix_product"},
    {"vector.prefix_sum", "algebra.vector_prefix_sum"},
    {"vector.inverse", "algebra.vector_inverse"},
    {"vector.embed", "algebra.vector_embed"},
    {"vector.fill", "algebra.vector_fill"},
    {"vector.geometric", "algebra.vector_geometric"},
    {"field.from_index", "algebra.field_from_index"},
    {"poly.coefficient_count", "poly.coefficient_count"},
    {"poly.coset_evaluate", "poly.coset_evaluate"},
    {"poly.coset_interpolate", "poly.coset_interpolate"},
    {"poly.domain_point", "poly.domain_point"},
    {"poly.domain_root", "poly.domain_root"},
    {"poly.domain_points", "poly.domain_points"},
    {"poly.even_odd_fold", "poly.even_odd_fold"},
    {"poly.divide_opening", "poly.divide_opening"},
    {"poly.opening_quotient", "poly.opening_quotient"},
    {"field.sub", "algebra.subtract"},
    {"field.neg", "algebra.negate"},
    {"field.inverse", "algebra.inverse"},
    {"field.embed", "algebra.embed"},
    {"matrix.mul_vector", "algebra.matrix_mul_vector"},
    {"matrix.transpose_mul_vector", "algebra.matrix_transpose_mul_vector"},
    {"matrix.bilinear", "algebra.matrix_bilinear"},
    {"matrix.shape_check", "algebra.matrix_shape_check"},
    {"matrix.identity_check", "algebra.matrix_identity_check"},
    {"vector.constant", "algebra.vector_constant"},
    {"vector.scatter_sum", "algebra.vector_scatter_sum"},
    {"vector.empty", "algebra.vector_empty"},
    {"vector.append", "algebra.vector_append"},
    {"vector.splat", "algebra.vector_splat"},
    {"vector.powers", "algebra.vector_powers"},
    {"vector.add", "algebra.vector_add"},
    {"vector.sub", "algebra.vector_sub"},
    {"vector.mul", "algebra.vector_mul"},
    {"vector.dot", "algebra.vector_dot"},
    {"vector.concat", "algebra.vector_concat"},
    {"vector.kronecker", "algebra.vector_kronecker"},
    {"vector.matvec", "algebra.vector_matvec"},
    {"vector.scale", "algebra.vector_scale"},
    {"vector.sum", "algebra.vector_sum"},
    {"vector.split", "algebra.vector_split"},
    {"vector.at", "algebra.vector_at"},
    {"vector.length_check", "algebra.vector_length_check"},
    {"vector.gather", "algebra.vector_gather"},
    {"vector.from_point", "poly.point_to_vector"},
    {"vector.from_table", "poly.table_to_vector"},
    {"vector.to_point", "poly.point_from_vector"},
    {"vector.to_table", "poly.table_from_vector"},
    {"poly.equality_weights", "poly.equality_weights"},
    {"poly.from_coefficients", "poly.from_coefficients"},
    {"poly.coefficients", "poly.coefficients"},
    {"poly.degree_check", "poly.degree_check"},
    {"poly.univariate_evaluate", "poly.univariate_evaluate"},
    {"poly.univariate_boundary", "poly.univariate_boundary"},
    {"random.vector", "pir.random_vector"},
    {"curve.neg", "algebra.curve_negate"},
    {"curve.nonidentity", "algebra.curve_nonidentity"},
    {"curve.msm", "algebra.curve_msm"},
    {"curve.scale_each", "algebra.curve_scale_each"},
    {"curve.vector_add", "algebra.curve_vector_add"},
    {"curve.vector_scale", "algebra.curve_vector_scale"},
    {"curve.split", "algebra.curve_split"},
    {"curve.concat", "algebra.curve_concat"},
    {"pairing.check", "algebra.pairing_check"},
    {"field.constant", "algebra.constant"},
    {"field.add", "algebra.sum"},
    {"field.mul", "algebra.product"},
    {"field.equal", "algebra.compare"},
    {"bool.and", "pir.and"},
    {"bool.not", "pir.not"},
    {"bool.or", "pir.or"},
    {"control.require", "pir.require"},
    {"poly.product_sum", "poly.product_sum"},
    {"poly.product_round", "poly.product_round"},
    {"poly.boundary", "poly.boundary"},
    {"poly.round_evaluate", "poly.round_evaluate"},
    {"poly.fold", "poly.fold"},
    {"poly.evaluate", "poly.mle_evaluate"},
    {"poly.empty_point", "poly.empty_point"},
    {"poly.append_point", "poly.append_point"},
    {"oracle.commit", "oracle.commit"},
    {"oracle.open", "oracle.open"},
    {"oracle.check", "oracle.check"},
    {"commitments.empty", "oracle.commitments_empty"},
    {"commitments.append", "oracle.commitments_append"},
    {"commitments.at", "oracle.commitments_at"},
    {"commitments.length", "oracle.commitments_length"},
    {"opening_states.empty", "oracle.opening_states_empty"},
    {"opening_states.append", "oracle.opening_states_append"},
    {"opening_states.at", "oracle.opening_states_at"},
    {"opening_states.length", "oracle.opening_states_length"},
    {"pcs.commit", "pcs.commit"},
    {"pcs.open", "pcs.open"},
    {"pcs.check", "pcs.check"},
    {"random.index", "pir.random_index"},
    {"transcript.draw_index", "pir.transcript_draw_index"},
    {"random.draw", "pir.random_draw"},
    {"pcs.equal", "pcs.equal"},
    {"curve.generator", "algebra.curve_generator"},
    {"curve.add", "algebra.curve_add"},
    {"curve.scale", "algebra.curve_scale"},
    {"curve.equal", "algebra.curve_equal"},
    {"curve.empty", "algebra.curve_empty"},
    {"curve.append", "algebra.curve_append"},
    {"curve.at", "algebra.curve_at"},
    {"curve.get", "algebra.curve_get"},
    {"curve.length", "algebra.curve_length"},
    {"curve.commit", "algebra.curve_commit"},
    {"curve.response", "algebra.curve_response"},
    {"transcript.challenge", "pir.transcript_challenge"},
    {"transcript.observe.bool", "pir.transcript_observe"},
    {"transcript.observe.field", "pir.transcript_observe"},
    {"transcript.observe.table", "pir.transcript_observe"},
    {"transcript.observe.point", "pir.transcript_observe"},
    {"transcript.observe.round", "pir.transcript_observe"},
    {"transcript.observe.commitment", "pir.transcript_observe"},
    {"transcript.observe.proof", "pir.transcript_observe"},
    {"transcript.observe.group", "pir.transcript_observe"},
    {"transcript.observe.groups", "pir.transcript_observe"},
    {"transcript.observe.matrix", "pir.transcript_observe"},
    {"transcript.observe.vector", "pir.transcript_observe"},
    {"transcript.observe.polynomial", "pir.transcript_observe"},
    {"transcript.observe.index", "pir.transcript_observe"},
    {"transcript.observe.indices", "pir.transcript_observe"},
    {"transcript.observe.commitments", "pir.transcript_observe"},
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
    // Check the complete cross product, including all many-to-one observations.
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
       {"", "field.sum", "algebra.sum", "Field.add", "field.add.extra",
        "table.relayout", "transcript.observe", "transcript.observe.",
        "transcript.observe.uninstalled", "transcript.observe.field.extra",
        "transcript.observe_field"}) {
    check(protocol::boundOperationName(unknown).empty(),
          "unknown contract mapped: " + unknown);
    for (const auto &row : expected)
      check(!protocol::operationSupportsContract(row.operation, unknown),
            "operation accepted unknown contract: " + unknown);
  }
  for (StringRef unknown :
       {"", "algebra.add", "field.add", "pir.uninstalled",
        "plan.execute_kernel", "pir.transcript_observe.extra"})
    for (const auto &row : expected)
      check(!protocol::operationSupportsContract(unknown, row.contract),
            "unmapped operation accepted contract: " + unknown);
}

source::Module arithmetic() {
  source::Module module;
  module.bindings = {{{}, "add", {"field.add", {"koala-bear"}, ""}},
                     {{}, "mul", {"field.mul", {"koala-bear"}, ""}}};
  source::Function function;
  function.name = "Arithmetic";
  function.origin = source::LogicalOrigin{"Arithmetic", {}};
  function.arguments = {{"x", "field:koala-bear"}, {"y", "field:koala-bear"}};
  function.results = {"field:koala-bear", "field:koala-bear"};
  function.body = source::Body{
      {{}, "add_site", source::Operation{"add", {}, {}, {"x", "y"}, {"sum"}}},
      {{},
       "mul_site",
       source::Operation{"mul", {}, {}, {"x", "y"}, {"product"}}},
      {{}, "", source::Return{{"sum", "product"}}}};
  module.functions.push_back(std::move(function));
  return module;
}

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
    if (!check((name == "algebra.sum" || name == "algebra.product") &&
                   op.getNumOperands() == 2 && op.getNumResults() == 1,
               "unexpected arithmetic operation: " + name))
      return;
    auto left = values.find(op.getOperand(0));
    auto right = values.find(op.getOperand(1));
    if (!check(left != values.end() && right != values.end(),
               "arithmetic operation refers to unknown value"))
      return;
    values[op.getResult(0)] = name == "algebra.sum"
                                  ? left->second + right->second
                                  : left->second * right->second;
  }
  check(false, "missing arithmetic return");
}

void importedArithmetic(MLIRContext &context) {
  auto source = arithmetic();
  auto add = protocol::resolveBinding(source.bindings[0].application, false);
  auto mul = protocol::resolveBinding(source.bindings[1].application, false);
  if (!add || !mul) {
    if (!add)
      check(false, toString(add.takeError()));
    if (!mul)
      check(false, toString(mul.takeError()));
    return;
  }
  check(add->inputs == mul->inputs && add->outputs == mul->outputs,
        "swap control must have identical signatures");
  auto imported = protocol::importModule(source, context);
  if (!imported) {
    check(false, "arithmetic import failed: " + toString(imported.takeError()));
    return;
  }
  check(succeeded(verify(imported->get())), "imported arithmetic rejected");
  unsigned sites = 0, functions = 0;
  (*imported)->walk([&](func::FuncOp function) {
    ++functions;
    arithmeticVector(function, 2, 3, 5, 6);
    arithmeticVector(function, 0, 7, 7, 0);
  });
  check(functions == 1, "expected one arithmetic function");
  (*imported)->walk([&](Operation *op) {
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!site)
      return;
    ++sites;
    bool isAdd = site.getValue() == "add_site";
    if (!check(isAdd || site.getValue() == "mul_site", "unexpected site"))
      return;
    check(op->getName().getStringRef() ==
              (isAdd ? "algebra.sum" : "algebra.product"),
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
