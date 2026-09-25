#include "zkc/Protocol/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
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
      {}, "empty", "poly.empty_point", {"bls12-381.fr"}, ""};
  auto signature = accept(resolveBinding(empty, false));
  require(signature.inputs.empty() &&
              signature.outputs[0].spelling() == "point:bls12-381.fr",
          "nullary operation has an explicit domain");
  empty.arguments.clear();
  refuse(resolveBinding(empty, false), "binding-static-arity");
  empty.arguments = {"bls12-381.g1"};
  refuse(resolveBinding(empty, false), "binding-static-identity");
  source::OperationBinding fold{
      {}, "fold", "poly.fold", {"bls12-381.fr"}, "arkworks/poly.fold"};
  auto lsb = accept(resolveBinding(fold, true));
  fold.implementation = "arkworks-msb/poly.fold";
  auto msb = accept(resolveBinding(fold, true));
  require(!(lsb.inputs[0] == msb.inputs[0]) && lsb.inputs[1] == msb.inputs[1],
          "layout is per physical type");
  require(accept(resolveBinding(fold, false)).inputs[0].representation.empty(),
          "fixed implementation retains logical ports before planning");
  fold.implementation = "arkworks/poly.product_sum";
  refuse(resolveBinding(fold, true), "binding-implementation");
  fold.implementation.clear();
  refuse(resolveBinding(fold, true), "binding-stage");
  source::OperationBinding opening{
      {}, "open", "pcs.open", {"multilinear.kzg.bls12-381/1"}, ""};
  source::OperationBinding challenge{
      {}, "draw", "transcript.challenge", {"merlin3.bls12-381.fr64be/1"}, ""};
  require(accept(resolveBinding(challenge, false)).outputs[0].identity ==
              "bls12-381.fr",
          "installed Merlin challenge field");
  challenge.arguments = {"sha256.fiat-shamir.bls12-381/1"};
  refuse(resolveBinding(challenge, false), "binding-static-identity");
  source::OperationBinding observe{{},
                                   "observe",
                                   "transcript.observe.table",
                                   {"merlin3.bls12-381.fr64be/1",
                                    "bls12-381.fr",
                                    "zkcv.table.bls12-381.fr/1"},
                                   ""};
  require(accept(resolveBinding(observe, false)).inputs[1].identity ==
              "bls12-381.fr",
          "observation selects payload and codec explicitly");
  observe.arguments[2] = "zkcv.point.bls12-381.fr/1";
  refuse(resolveBinding(observe, false), "binding-requirement");
  for (const auto &op : boundOperationContracts())
    if (op.name == "transcript.observe.table") {
      require(op.signature.scope.terms.size() == 3 &&
                  !op.signature.scope.terms[1].parent &&
                  op.signature.inputs[1].arguments == std::vector<unsigned>{1},
              "payload field is independent of the transcript challenge field");
    }
  auto pcs = accept(resolveBinding(opening, false));
  require(pcs.outputs[0].identity == "bls12-381.fr" &&
              pcs.outputs[1].identity == opening.arguments[0],
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
  module.bindings.push_back({{},
                             opening.name,
                             opening.contract,
                             opening.arguments,
                             opening.implementation});
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
  module.bindings.front().arguments.clear();
  auto malformed = admit(module, false);
  require(bool(malformed), "binding arity refused");
  require(toString(std::move(malformed)) == "binding-static-arity",
          "binding-static-arity");
  const std::string spongefish = "spongefish0.7.4.keccak.bls12-381.fr64be/1";
  require(associatedIdentity(spongefish, "ChallengeField") == "bls12-381.fr",
          "second-suite-associated-field");
  for (const auto &contract :
       {"transcript.challenge", "transcript.observe.field"}) {
    source::OperationBinding b{{}, "second", contract, {spongefish}, ""};
    if (StringRef(contract).ends_with("field")) {
      b.arguments.push_back("bls12-381.fr");
      b.arguments.push_back("zkcv.field.bls12-381.fr/1");
    }
    require(accept(defaultImplementation(b)) == "spongefish/" + b.contract,
            "second-suite-independent-provider");
    b.implementation = "spongefish/" + b.contract;
    auto selected = accept(resolveBinding(b, true));
    require(selected.inputs.front().identity == spongefish,
            "second-suite-nominal-state");
    b.implementation = "arkworks/" + b.contract;
    refuse(resolveBinding(b, true), "binding-implementation");
    if (b.arguments.size() == 3) {
      b.implementation = "spongefish/" + b.contract;
      b.arguments[1] = "ristretto255.scalar";
      b.arguments[2] = "zkcv.field.ristretto255.scalar/1";
      refuse(resolveBinding(b, true), "binding-implementation");
    }
  }
}
