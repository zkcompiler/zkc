#include "zkc/Dialect/Bindings.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
namespace {
void require(bool condition, StringRef detail) {
  if (!condition) {
    errs() << detail << '\n';
    std::exit(1);
  }
}
template <typename T> T accept(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
template <typename T> void refuse(Expected<T> result, StringRef code) {
  require(!result, "expected refusal");
  require(toString(result.takeError()) == code, code);
}
} // namespace
int main() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  llvm::StringSet<> contracts;
  for (const auto &kernel : kernels()) {
    require(contracts.insert(kernel.key).second, "unique installed contract");
    auto operation = boundOperationName(kernel.key);
    require(!operation.empty(), kernel.key);
    require(context.isOperationRegistered(operation), operation);
  }
  require(boundOperationName("uninstalled.contract").empty(),
          "unknown contracts have no IR mapping");
  require(boundOperationName("transcript.observe.uninstalled").empty(),
          "unknown observation types have no IR mapping");
  require(boundOperationName("table.relayout").empty(),
          "physical adapters do not acquire logical operations");
  mlir::OperationState state(mlir::UnknownLoc::get(&context),
                             OperationBindingOp::getOperationName());
  auto *detached = mlir::Operation::create(state);
  refuse(readBinding(detached), "binding-declaration-context");
  detached->destroy();
  refuse(readBinding(nullptr), "binding-declaration-context");
  refuse(parseBoundType("bool@", false), "binding-representation");
  refuse(parseBoundType("field:bls12-381.fr@", false),
         "binding-representation");
  refuse(parseBoundType("bool@", true), "binding-representation");
  source::OperationBinding empty{
      {}, "empty", {"poly.empty_point", {"bls12-381.fr"}, ""}};
  auto signature = accept(resolveBinding(empty.application, false));
  require(signature.inputs.empty() &&
              signature.outputs[0].spelling() == "point:bls12-381.fr",
          "nullary operation has an explicit domain");
  empty.application.arguments.clear();
  refuse(resolveBinding(empty.application, false), "binding-static-arity");
  empty.application.arguments = {"bls12-381.g1"};
  refuse(resolveBinding(empty.application, false), "binding-static-identity");
  source::OperationBinding fold{
      {}, "fold", {"poly.fold", {"bls12-381.fr"}, "arkworks/poly.fold"}};
  auto lsb = accept(resolveBinding(fold.application, true));
  fold.application.implementation = "arkworks-msb/poly.fold";
  auto msb = accept(resolveBinding(fold.application, true));
  require(!(lsb.inputs[0] == msb.inputs[0]) && lsb.inputs[1] == msb.inputs[1],
          "layout is per physical type");
  require(accept(resolveBinding(fold.application, false))
              .inputs[0]
              .representation.empty(),
          "fixed implementation retains logical ports before planning");
  fold.application.implementation = "arkworks/poly.product_sum";
  refuse(resolveBinding(fold.application, true), "binding-implementation");
  fold.application.implementation.clear();
  refuse(resolveBinding(fold.application, true), "binding-stage");
  source::OperationBinding opening{
      {}, "open", {"pcs.open", {"multilinear.kzg.bls12-381/1"}, ""}};
  source::OperationBinding challenge{
      {}, "draw", {"transcript.challenge", {"merlin3.bls12-381.fr64be/1"}, ""}};
  require(accept(resolveBinding(challenge.application, false))
                  .outputs[0]
                  .identity == "bls12-381.fr",
          "installed Merlin challenge field");
  challenge.application.arguments = {"sha256.fiat-shamir.bls12-381/1"};
  refuse(resolveBinding(challenge.application, false),
         "binding-static-identity");
  source::OperationBinding observe{
      {},
      "observe",
      {"transcript.observe.table",
       {"merlin3.bls12-381.fr64be/1", "bls12-381.fr",
        "zkcv.table.bls12-381.fr/1"},
       ""}};
  require(
      accept(resolveBinding(observe.application, false)).inputs[1].identity ==
          "bls12-381.fr",
      "observation selects payload and codec explicitly");
  observe.application.arguments[2] = "zkcv.point.bls12-381.fr/1";
  refuse(resolveBinding(observe.application, false), "binding-requirement");
  for (const auto &op : boundOperationContracts())
    if (op.name == "transcript.observe.table") {
      require(op.signature.scope.terms.size() == 3 &&
                  !op.signature.scope.terms[1].parent &&
                  op.signature.inputs[1].arguments == std::vector<unsigned>{1},
              "payload field is independent of the transcript challenge field");
    }
  auto pcs = accept(resolveBinding(opening.application, false));
  require(pcs.outputs[0].identity == "bls12-381.fr" &&
              pcs.outputs[1].identity == opening.application.arguments[0],
          "associated field and construction identities stay distinct");
  for (const auto &type : {lsb.inputs[0], msb.inputs[0], pcs.outputs[1],
                           BoundType{"bool", "", ""}}) {
    bool physical = !type.representation.empty();
    auto parsed = accept(parseBoundType(type.spelling(), physical));
    require(accept(encodeBoundType(decodeBoundType(&context, parsed),
                                   physical)) == type,
            "full nominal/physical type round trip");
  }
  for (StringRef bad : {"field", "field:bls12-381.g1", "bool:bls12-381.fr",
                        "bool:", "table:uninstalled"}) {
    auto result = parseBoundType(bad, false);
    require(!result, "malformed or uninstalled type");
    consumeError(result.takeError());
  }

  // Every installed polymorphic operation signature is itself well formed and
  // sufficient for a body invoking exactly that operation.
  for (const auto &op : boundOperationContracts()) {
    generic::Function body;
    body.signature = op.signature;
    generic::Call call{"site", op.name, {}, {}};
    for (auto [i, term] : enumerate(op.signature.scope.terms))
      if (!term.parent)
        call.staticArguments.push_back(i);
    for (unsigned i = 0; i < op.signature.inputs.size(); ++i)
      call.inputs.push_back(i);
    for (unsigned i = 0; i < op.signature.outputs.size(); ++i)
      body.returns.push_back(op.signature.inputs.size() + i);
    body.body.push_back(std::move(call));
    accept(generic::check(body, boundTypeConstructors(),
                          boundOperationContracts(), boundCapabilityRules()));
  }
  source::Module module;
  module.bindings.push_back(
      {{},
       opening.name,
       {opening.application.contract, opening.application.arguments,
        opening.application.implementation}});
  auto encoded = source::encode(module);
  auto decoded = accept(source::decode(encoded));
  require(source::encode(decoded) == encoded,
          "binding source-codec round trip");
  require(!admit(decoded, false), "binding declaration admitted");
  module.bindings.push_back(module.bindings.front());
  auto duplicate = admit(module, false);
  require(bool(duplicate), "duplicate binding refused");
  require(toString(std::move(duplicate)) == "binding-name", "binding-name");
  module.bindings.pop_back();
  module.bindings.front().application.arguments.clear();
  auto malformed = admit(module, false);
  require(bool(malformed), "binding arity refused");
  require(toString(std::move(malformed)) == "binding-static-arity",
          "binding-static-arity");
  const std::string spongefish = "spongefish0.7.4.keccak.bls12-381.fr64be/1";
  require(associatedIdentity(spongefish, "ChallengeField") == "bls12-381.fr",
          "second-suite-associated-field");
  for (const auto &contract :
       {"transcript.challenge", "transcript.observe.field"}) {
    source::OperationBinding b{{}, "second", {contract, {spongefish}, ""}};
    if (StringRef(contract).ends_with("field")) {
      b.application.arguments.push_back("bls12-381.fr");
      b.application.arguments.push_back("zkcv.field.bls12-381.fr/1");
    }
    require(accept(defaultImplementation(b.application)) ==
                "spongefish/" + b.application.contract,
            "second-suite-independent-provider");
    b.application.implementation = "spongefish/" + b.application.contract;
    auto selected = accept(resolveBinding(b.application, true));
    require(selected.inputs.front().identity == spongefish,
            "second-suite-nominal-state");
    b.application.implementation = "arkworks/" + b.application.contract;
    refuse(resolveBinding(b.application, true), "binding-implementation");
    if (b.application.arguments.size() == 3) {
      b.application.implementation = "spongefish/" + b.application.contract;
      b.application.arguments[1] = "ristretto255.scalar";
      b.application.arguments[2] = "zkcv.field.ristretto255.scalar/1";
      refuse(resolveBinding(b.application, true), "binding-implementation");
    }
  }
}
