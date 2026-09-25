#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Source/Relations.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace mlir;
using namespace zkc;

namespace {
void require(bool ok, const Twine &message) {
  if (!ok) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
void generatedView(source::Module source, MLIRContext &context) {
  if (auto e = relation::materializeViews(source)) {
    errs() << toString(std::move(e)) << '\n';
    std::exit(1);
  }
  auto module = take(protocol::importModule(source, context));
  auto exported = take(protocol::exportModule(module.get()));
  require(exported == source::encode(source),
          "relation view roundtrip changed");
  Operation *kernel = nullptr;
  module->walk([&](Operation *op) {
    if (!kernel && op->hasAttr("site") && op->getParentOfType<func::FuncOp>())
      kernel = op;
  });
  require(kernel, "generated relation must contain local computation");
  kernel->setAttr("site", StringAttr::get(&context, "tampered"));
  // Local IR is well-formed. Only the complete source reconstruction can
  // establish that the generated code corresponds to the retained relation.
  require(succeeded(kernel->getName().verifyInvariants(kernel)),
          "mutation must preserve local operation invariants");
  std::vector<diagnostics::RefusalInfo> codes;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    auto found = diagnostics::refusals(diagnostic);
    llvm::append_range(codes, found);
    return success();
  });
  require(failed(verify(module.get())),
          "whole-root verification lost correspondence");
  require(llvm::any_of(codes,
                       [](const auto &r) {
                         return r.code == "relation-generated-function";
                       }),
          "whole-root refusal lost its native identifier");
  auto rejected = protocol::exportSource(module.get());
  require(!rejected, "public export must check mutated roots");
  require(toString(rejected.takeError()) == "relation-generated-function",
          "changed refusal precedence");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  relation::Constraint row{{{{2, "1"}}, {{3, "1"}}, {{1, "1"}}}};
  auto r1cs = take(relation::R1CS::create("bls12-381.fr", 4, 1, 1, {row}));
  for (auto kind : {"multilinear", "rank_one"})
    for (auto staging : {"specialized", "public_matrices"}) {
      source::Module source;
      source.relations.push_back(
          {{}, "Circuit", std::make_shared<const relation::R1CS>(r1cs)});
      source.relationViews.push_back(
          {{}, "Rows", "Circuit", kind, staging, {}});
      generatedView(std::move(source), context);
    }
  using N = relation::AIRNode;
  auto air = take(relation::AIR::create(
      "bls12-381.fr", 1, 0,
      {{{relation::AIRScopeKind::Transition, 1},
        {N::read(1, 0), N::read(0, 0), N::mul(1, 1), N::neg(2), N::add(0, 3)},
        {},
        {}}}));
  source::Module source;
  source.relations.push_back(
      {{}, "Trace", std::make_shared<const relation::AIR>(air)});
  source.relationViews.push_back(
      {{}, "Steps", "Trace", "arithmetic", "specialized", 3});
  generatedView(std::move(source), context);
  outs() << "five generated relation views retain exact root/export "
            "correspondence\n";
}
