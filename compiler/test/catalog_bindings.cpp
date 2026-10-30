#include "support/NativeCases.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Interfaces/CatalogType.h"
#include <set>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Builder builder(&context);
  auto emit = [&] { return emitError(builder.getUnknownLoc()); };
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    for (const auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  auto field = algebra::FieldType::get(&context, "bls12-381.fr");
  auto vector = algebra::FieldVectorType::get(&context, "bls12-381.fr");
  auto natural = [&](uint64_t value) {
    return builder.getIntegerAttr(
        IntegerType::get(&context, 64, IntegerType::Unsigned), value);
  };
  auto domain = builder.getStringAttr("bls12-381.fr");
  auto resolve = [&](StringRef contract, ArrayRef<Attribute> arguments) {
    auto signature =
        resolveLogicalSignature(emit, &context, contract, arguments);
    require(bool(signature), "native signature refused: " + contract.str());
    return signature;
  };
  auto refuse = [&](StringRef contract, ArrayRef<Attribute> arguments) {
    codes.clear();
    require(!resolveLogicalSignature(emit, &context, contract, arguments),
            "malformed native binding accepted");
    require(llvm::is_contained(codes, "binding-signature"),
            "signature refusal lost its diagnostic identity");
  };
  Cases cases;
  cases.run("mathematical signature excludes execution bookkeeping", [&] {
    require(resolve("field.add", {domain}) ==
                builder.getFunctionType({field, field}, {field}),
            "scope or outcome leaked into mathematical ports");
  });
  cases.run("application terms construct complete nested ports", [&] {
    auto fixed = algebra::FixedVectorType::get(&context, field, 4);
    require(resolve("fixed_vector.dot", {domain, natural(4)}) ==
                builder.getFunctionType({fixed, fixed}, {field}),
            "nested Type application or Nat argument erased");
    auto array = algebra::FieldArrayType::get(&context, "bls12-381.fr", 4);
    require(resolve("field_array.from_vector", {domain, natural(4)}) ==
                builder.getFunctionType({vector}, {array}),
            "domain/Nat application changed");
  });
  cases.run("associated members determine actual challenge domain", [&] {
    const protocol::NominalDomain *selected = nullptr;
    for (const auto &candidate : protocol::installedDomains().allDomains())
      if (candidate.sort == "Transcript" &&
          protocol::associatedIdentity(candidate.identity, "ChallengeField") ==
              "bls12-381.fr") {
        selected = &candidate;
        break;
      }
    require(bool(selected), "missing transcript test installation");
    auto signature = resolve("transcript.native.indexed.challenge",
                             {builder.getStringAttr(selected->identity)});
    require(signature.getNumResults() == 2 && signature.getResult(0) == field &&
                signature.getInput(0) == signature.getResult(1),
            "associated field or affine successor changed");
  });
  cases.run("complete-Type ports retain native identity beyond byte limits",
            [&] {
              Type payload = field;
              for (unsigned i = 0; i < 12; ++i)
                payload = data::SequenceType::get(&context, payload);
              for (const auto &candidate :
                   protocol::installedDomains().allDomains()) {
                if (candidate.sort != "Transcript")
                  continue;
                auto signature = resolveLogicalSignature(
                    emit, &context, "transcript.native.indexed.observe.data",
                    {builder.getStringAttr(candidate.identity),
                     TypeAttr::get(payload)});
                if (!signature)
                  continue;
                require(signature.getInput(1) == payload,
                        "complete-Type payload was reconstructed or truncated");
                return;
              }
              require(false, "no native transcript signature formed");
            });
  cases.run("numerical families preserve mixed and empty masks", [&] {
    auto mask = builder.getDenseBoolArrayAttr({true, false, true});
    require(resolve("numerical.map", {domain, mask}) ==
                builder.getFunctionType(
                    {natural(0).getType(), vector, field, vector}, {vector}),
            "numerical mask lost its positional ABI");
    require(
        resolve("numerical.sum", {domain, builder.getDenseBoolArrayAttr({})}) ==
            builder.getFunctionType({natural(0).getType()}, {field}),
        "empty numerical mask acquired a hidden operand");
  });
  cases.run(
      "slot scope derives resource successor without domain installation", [&] {
        auto slot = builder.getStringAttr("ticket");
        auto type = runtime::CapabilityType::get(
            &context, zkc::runtime::CapabilityKind::ResourceUnit, "ticket");
        require(
            resolve("resource_unit.pass", {slot}) ==
                builder.getFunctionType({type}, {type}),
            "resource slot changed or required a field-domain registration");
        refuse("resource_unit.pass", {builder.getStringAttr("bad:slot")});
      });
  cases.run("static kinds and numerical masks refuse substitutions", [&] {
    refuse("missing", {});
    refuse("field.add", {});
    refuse("field.add", {domain, domain});
    refuse("field.add", {TypeAttr::get(field)});
    refuse("field.add", {builder.getStringAttr("bls12-381.g1")});
    refuse("field_array.get", {domain, builder.getStringAttr("4")});
    refuse("field_array.get", {domain, builder.getI64IntegerAttr(4)});
    refuse("field_array.get", {domain, natural(1048577)});
    refuse("numerical.map", {domain, builder.getStringAttr("101")});
    refuse("numerical.map", {domain, natural(5)});
    refuse("numerical.map", {domain});
    SmallVector<bool> excessive(1024, false);
    refuse("numerical.map", {domain, builder.getDenseBoolArrayAttr(excessive)});
    MLIRContext foreign;
    refuse("field.add", {StringAttr::get(&foreign, "bls12-381.fr")});
    refuse("numerical.map", {domain, DenseBoolArrayAttr::get(&foreign, {})});
  });
  cases.run("native and neutral signatures agree for installed instances", [&] {
    std::set<std::string> covered;
    unsigned checked = 0;
    // Sample every installed root identity independently. Neutral resolution is
    // an independent boundary oracle; unsupported codec profiles may refuse
    // there even when mathematical formation succeeds.
    for (const auto &operation : protocol::executableOperationContracts()) {
      std::vector<std::vector<std::string>> choices;
      for (auto [i, term] : llvm::enumerate(operation.signature.scope.terms)) {
        if (term.parent || term.arguments ||
            operation.signature.scope.constants.count(i))
          continue;
        auto sort = operation.signature.scope.sorts[i];
        if (sort == "Type")
          choices.push_back({"field:bls12-381.fr"});
        else if (sort == "Nat")
          choices.push_back({"4"});
        else if (sort == "Slot")
          choices.push_back({"ticket"});
        else {
          choices.emplace_back();
          for (const auto &candidate :
               protocol::installedDomains().allDomains())
            if (candidate.sort == sort)
              choices.back().push_back(candidate.identity);
        }
      }
      if (llvm::any_of(choices,
                       [](const auto &values) { return values.empty(); }))
        continue;
      size_t samples = 1;
      for (const auto &values : choices)
        samples = std::max(samples, values.size());
      for (size_t sample = 0; sample < samples; ++sample) {
        protocol::BindingApplication binding{operation.name, {}, ""};
        SmallVector<Attribute> actuals;
        unsigned root = 0;
        for (auto [i, term] :
             llvm::enumerate(operation.signature.scope.terms)) {
          if (term.parent || term.arguments ||
              operation.signature.scope.constants.count(i))
            continue;
          auto &values = choices[root++];
          auto value = values[sample % values.size()];
          binding.arguments.push_back(value);
          auto sort = operation.signature.scope.sorts[i];
          actuals.push_back(sort == "Type" ? Attribute(TypeAttr::get(field))
                            : sort == "Nat"
                                ? Attribute(natural(4))
                                : Attribute(builder.getStringAttr(value)));
        }
        if (operation.numerical) {
          binding.arguments.push_back("101");
          actuals.push_back(builder.getDenseBoolArrayAttr({true, false, true}));
        }
        auto neutral = protocol::resolveLogicalBinding(binding);
        if (!neutral) {
          llvm::consumeError(neutral.takeError());
          continue;
        }
        auto native = resolve(operation.name, actuals);
        auto compare = [&](ArrayRef<Type> types,
                           ArrayRef<protocol::BoundType> expected) {
          require(types.size() == expected.size(), "signature arity changed");
          for (auto [type, port] : llvm::zip(types, expected))
            require(type == protocol::decodeBoundType(&context, port),
                    "native and neutral port disagree: " + operation.name);
        };
        compare(native.getInputs(), neutral->inputs);
        compare(native.getResults(), neutral->outputs);
        ++checked;
        covered.insert(operation.name);
      }
    }
    require(covered.size() == protocol::executableOperationContracts().size() &&
                checked >= 1000,
            "installed signature coverage unexpectedly shrank");
    llvm::outs() << "native signatures: " << covered.size() << " contracts, "
                 << checked << " instances\n";
  });
  return cases.result();
}
