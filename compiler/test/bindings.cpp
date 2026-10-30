#include "zkc/Dialect/Bindings.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "support/ContractWitnesses.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <utility>

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
  mlir::MLIRContext fresh;
  for (StringRef spelling : {"field:bls12-381.fr", "vector:bls12-381.fr",
                             "group:bls12-381.g1", "groups:bls12-381.g1"}) {
    auto bound = accept(parseBoundType(spelling, false));
    require(!decodeBoundType(&fresh, bound),
            "unloaded type decoding must fail without initializing dialects");
  }
  require(bool(decodeBoundType(&fresh, {"bool", "", ""})),
          "builtin Boolean decoding needs no zkc dialect");
  fresh.loadDialect<zkc::algebra::AlgebraDialect>();
  auto field = accept(parseBoundType("field:bls12-381.fr", false));
  require(bool(decodeBoundType(&fresh, field)), "loaded field type refused");
  auto physical = accept(defaultRepresentation(field));
  require(!decodeBoundType(&fresh, physical),
          "physical wrapper requires its own loaded dialect");

  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  require(context.isOperationRegistered("exec.apply"),
          "the installed contract invocation is registered");
  for (StringRef retired : {"algebra.exec.field_add", "poly.exec.fold",
                            "crypto.exec.random_draw", "data.exec.sequence_at"})
    require(!context.isOperationRegistered(retired),
            "retired execution wrapper is still registered");
  mlir::OperationState state(mlir::UnknownLoc::get(&context),
                             zkc::runtime::BindingOp::getOperationName());
  auto *detached = mlir::Operation::create(state);
  refuse(readBinding(detached), "binding-declaration-context");
  detached->destroy();
  refuse(readBinding(nullptr), "binding-declaration-context");
  {
    // A physical-only declaration is well formed in a stage-neutral module,
    // but does not become admissible in a logical Protocol profile.
    mlir::OwningOpRef<mlir::ModuleOp> module(
        mlir::ModuleOp::create(mlir::UnknownLoc::get(&context)));
    mlir::OpBuilder builder(module->getBody(), module->getBody()->end());
    auto binding = runtime::BindingOp::create(
        builder, module->getLoc(), "convert", "representation.convert",
        builder.getStrArrayAttr({"field:bls12-381.fr"}),
        "native/representation.convert",
        builder.getStrArrayAttr(
            {physical.spelling(), "field:bls12-381.fr@blst/fr"}));
    require(accept(readBinding(binding)).application.physicalArguments.size() ==
                    2 &&
                mlir::succeeded(mlir::verify(*module)),
            "builtin module refused a physical declaration");
    mlir::OperationState rootState(module->getLoc(), "protocol.module");
    rootState.addAttribute(
        "profile",
        protocol_ir::ProfileAttr::get(&context, protocol_ir::Profile::Exec));
    rootState.addRegion();
    auto *root = builder.create(rootState);
    auto *body = builder.createBlock(&root->getRegion(0));
    binding->moveBefore(body, body->end());
    refuse(readBinding(binding), "binding-conversion");
    root->setAttr("profile", protocol_ir::ProfileAttr::get(
                                 &context, protocol_ir::Profile::Physical));
    require(bool(readBinding(binding)),
            "physical Protocol profile refused a physical declaration");
    binding.setPhysicalArgumentsAttr(
        builder.getStrArrayAttr({physical.spelling(), physical.spelling()}));
    refuse(readBinding(binding), "binding-conversion");
    binding->moveBefore(module->getBody(), module->getBody()->begin());
    refuse(readBinding(binding), "binding-conversion");
  }
  {
    // A numerical schedule resolves only within its own lexical symbol table.
    // A surrounding declaration cannot silently authorize a missing binding.
    mlir::OwningOpRef<mlir::ModuleOp> outer(
        mlir::ModuleOp::create(mlir::UnknownLoc::get(&context)));
    mlir::OpBuilder builder(outer->getBody(), outer->getBody()->end());
    auto loc = outer->getLoc();
    auto declare = [&] {
      runtime::BindingOp::create(builder, loc, "combine", "bool.and",
                                 builder.getArrayAttr({}), "",
                                 mlir::ArrayAttr{});
    };
    declare();
    auto inner = mlir::ModuleOp::create(loc, "schedule");
    outer->getBody()->push_back(inner);
    builder.setInsertionPointToEnd(inner.getBody());
    auto type = builder.getI1Type();
    auto fn = mlir::func::FuncOp::create(
        builder, loc, "evaluate",
        builder.getFunctionType({runtime::ScopeType::get(&context), type, type},
                                {exec::OutcomeType::get(&context, {type})}));
    builder.setInsertionPointToEnd(fn.addEntryBlock());
    mlir::OperationState call(loc, exec::ApplyOp::getOperationName());
    call.addOperands(fn.getArguments());
    call.addTypes(exec::OutcomeType::get(&context, {type}));
    call.addAttribute("binding",
                      mlir::FlatSymbolRefAttr::get(&context, "combine"));
    call.addAttribute("parameters", builder.getArrayAttr({}));
    call.addAttribute("site", builder.getStringAttr("combine"));
    auto *use = builder.create(call);
    mlir::func::ReturnOp::create(builder, loc, use->getResults());
    refuse(operationBinding(use), "binding-declaration-context");
    builder.setInsertionPointToStart(inner.getBody());
    declare();
    require(accept(operationBinding(use)).application.contract == "bool.and" &&
                mlir::succeeded(mlir::verify(*outer)),
            "standard numerical module binding did not verify lexically");
  }
  refuse(parseBoundType("bool@", false), "binding-representation");
  refuse(parseBoundType("field:bls12-381.fr@", false),
         "binding-representation");
  refuse(parseBoundType("bool@", true), "binding-representation");
  for (StringRef spelling :
       {"table:koala-bear", "point:koala-bear",
        "table:koala-bear.ext8-binomial3", "table:bn254.fr", "nonce:bn254.fr",
        "rng:koala-bear"})
    refuse(parseBoundType(spelling, false), "binding-type-identity");
  protocol::OperationBinding empty{"empty",
                                   {"poly.empty_point", {"bls12-381.fr"}, ""}};
  auto signature = accept(resolveBinding(empty.application, false));
  require(signature.inputs.empty() &&
              signature.outputs[0].spelling() == "point:bls12-381.fr",
          "nullary operation has an explicit domain");
  empty.application.arguments.clear();
  refuse(resolveBinding(empty.application, false), "binding-static-arity");
  empty.application.arguments = {"bls12-381.g1"};
  refuse(resolveBinding(empty.application, false), "binding-static-identity");
  protocol::OperationBinding fold{
      "fold", {"poly.fold", {"bls12-381.fr"}, "arkworks/poly.fold"}};
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
  // Alternative providers retain exact physical ports, and never broaden their
  // mathematical domains or replace the installed default preference.
  for (StringRef contract :
       {"curve.scale", "curve.scale_each", "curve.vector_scale", "curve.msm",
        "pairing.check"}) {
    for (StringRef domain : {"bls12-381.g1", "bls12-381.g2", "bls12-381.fr"}) {
      BindingApplication alternative{
          contract.str(), {domain.str()}, ("blst/resident/" + contract).str()};
      bool eligible =
          (contract == "pairing.check") == (domain == "bls12-381.fr");
      auto signature = resolveBinding(alternative, true);
      if (!eligible) {
        refuse(std::move(signature), "binding-static-identity");
        continue;
      }
      auto original = alternative;
      original.implementation = ("arkworks/" + contract).str();
      auto expected = accept(resolveBinding(original, true));
      auto actual = accept(std::move(signature));
      for (auto *ports : {&actual.inputs, &actual.outputs})
        for (auto &port : *ports) {
          if (port.kind == "bool")
            continue;
          require(StringRef(port.representation).starts_with("blst/"),
                  "resident provider lost exact resident ports");
          port.representation = accept(defaultRepresentation(BoundType{
                                           port.kind, port.identity, ""}))
                                    .representation;
        }
      require(actual.inputs == expected.inputs &&
                  actual.outputs == expected.outputs,
              "resident provider changed logical ports");
    }
  }
  protocol::OperationBinding opening{
      "open", {"pcs.open", {"multilinear.kzg.bls12-381/0"}, ""}};
  protocol::OperationBinding challenge{"draw",
                                       {"transcript.native.indexed.challenge",
                                        {"merlin3.bls12-381.fr64be/0"},
                                        ""}};
  require(accept(resolveBinding(challenge.application, false))
                  .outputs[0]
                  .identity == "bls12-381.fr",
          "installed Merlin challenge field");
  challenge.application.arguments = {"sha256.fiat-shamir.bls12-381/0"};
  refuse(resolveBinding(challenge.application, false),
         "binding-static-identity");
  protocol::OperationBinding observe{
      "observe",
      {"transcript.native.indexed.observe.data",
       {"merlin3.bls12-381.fr64be/0", "vector:bls12-381.fr"},
       ""}};
  auto observed = accept(resolveBinding(observe.application, false));
  require(observed.inputs[1].identity == "bls12-381.fr" &&
              observed.inputs[2].kind == "indices",
          "typed payload and coordinates");
  observe.application.arguments[1] = "rng:bls12-381.fr";
  refuse(resolveBinding(observe.application, false), "native-proof-wire-type");
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
  for (const auto &op : zkc::test::genericWitnessOperations()) {
    generic::Function body;
    body.signature = op.signature;
    generic::Call call{"site", op.name, {}, {}};
    for (auto [i, term] : enumerate(op.signature.scope.terms))
      if (!term.parent && !term.arguments &&
          !op.signature.scope.constants.count(i))
        call.staticArguments.push_back(i);
    for (unsigned i = 0; i < op.signature.inputs.size(); ++i)
      call.inputs.push_back(i);
    for (unsigned i = 0; i < op.signature.outputs.size(); ++i)
      body.returns.push_back(op.signature.inputs.size() + i);
    body.body.push_back(std::move(call));
    accept(generic::check(body, boundTypeConstructors(),
                          zkc::test::genericWitnessOperations(),
                          boundCapabilityRules()));
  }
  program::LocalDefinitions module;
  module.bindings.push_back(
      {opening.name,
       {opening.application.contract, opening.application.arguments,
        opening.application.implementation}});
  module.bindings.push_back(module.bindings.front());
  auto duplicate = admitNativeLocalDefinitions(module);
  require(bool(duplicate), "duplicate binding refused");
  require(toString(std::move(duplicate)) == "binding-name", "binding-name");
  module.bindings.pop_back();
  module.bindings.front().application.arguments.clear();
  auto malformed = admitNativeLocalDefinitions(module);
  require(bool(malformed), "binding arity refused");
  require(toString(std::move(malformed)) == "binding-static-arity",
          "binding-static-arity");
  const std::string spongefish = "spongefish0.8.0.keccak.bls12-381.fr64be/0";
  // Explicit policy preserves the selected provider for all installed suites,
  // including suites whose physical state is named host.resource/1.
  for (const auto &[suite, provider] :
       {std::pair{"merlin3.bls12-381.fr64be/0", "arkworks"},
        std::pair{"merlin3.ristretto255.scalar64le/0", "dalek"},
        std::pair{"merlin3.koala-bear.ext8-binomial3.rejection31le/0",
                  "plonky3"},
        std::pair{"spongefish0.8.0.keccak.bls12-381.fr64be/0", "spongefish"}}) {
    BindingApplication application{
        "transcript.native.indexed.challenge", {suite}, ""};
    const std::string implementation =
        std::string(provider) + "/transcript.native.indexed.challenge";
    require(accept(defaultImplementation(application)) == implementation,
            "nominal transcript policy preserves the selected provider");
    application.implementation = implementation;
    accept(resolveBinding(application, true));
  }
  // Policy never installs an arbitrary operation on the selected provider.
  protocol::OperationBinding unsupported{
      "unsupported", {"field.add", {"bls12-381.fr"}, "spongefish/field.add"}};
  refuse(resolveBinding(unsupported.application, true),
         "binding-implementation");
  require(associatedIdentity(spongefish, "ChallengeField") == "bls12-381.fr",
          "second-suite-associated-field");
  for (const auto &contract : {"transcript.native.indexed.challenge",
                               "transcript.native.indexed.observe.data"}) {
    protocol::OperationBinding b{"second", {contract, {spongefish}, ""}};
    if (StringRef(contract).ends_with("data")) {
      b.application.arguments.push_back("field:bls12-381.fr");
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
    if (b.application.arguments.size() == 2) {
      b.application.implementation = "spongefish/" + b.application.contract;
      b.application.arguments[1] = "rng:bls12-381.fr";
      refuse(resolveBinding(b.application, true), "native-proof-wire-type");
    }
  }
}
