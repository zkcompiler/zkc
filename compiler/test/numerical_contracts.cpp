#include "support/NativeCases.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refuse(Error error, StringRef code) {
  require(bool(error), "expected refusal " + code);
  require(namesIdentifier(toString(std::move(error)), code),
          "wrong refusal identifier " + code);
}
std::string body(StringRef field, unsigned slots = 3) {
  std::vector<ring::Input> inputs(slots, {field.str()});
  return printJson(
      take(ring::Expression::create(std::move(inputs),
                                    {ring::Node::slot(0), ring::Node::slot(1),
                                     ring::Node::mul(0, 1), ring::Node::slot(2),
                                     ring::Node::add(2, 3)},
                                    {4}))
          .encode());
}
// A reachable negation chain with a final literal-size adjustment exercises
// the decoded body ceiling using canonical, well-typed expressions.
std::string boundary(size_t bytes) {
  std::vector<ring::Node> nodes{ring::Node::literal("bls12-381.fr", "0")};
  auto encode = [&] {
    return printJson(
        take(ring::Expression::create({}, nodes, {uint32_t(nodes.size() - 1)}))
            .encode());
  };
  std::string text = encode();
  for (;;) {
    nodes.push_back(ring::Node::neg(nodes.size() - 1));
    auto next = encode();
    if (next.size() > bytes) {
      nodes.pop_back();
      break;
    }
    text = std::move(next);
  }
  nodes[0].constant = std::string(bytes - text.size() + 1, '1');
  text = encode();
  require(text.size() == bytes, "body boundary construction failed");
  return text;
}
program::Participants makeProgram(StringRef contract, StringRef field,
                                  StringRef mask, StringRef expression) {
  BindingApplication binding{contract.str(), {field.str(), mask.str()}, ""};
  binding.implementation = take(defaultImplementation(binding));
  auto signature = take(resolveBinding(binding, true));
  program::Participants result;
  result.stage = program::Participants::Stage::Physical;
  result.bindings.push_back({"numerical", binding});
  program::Participant participant;
  participant.name = "P";
  participant.instance = "main";
  participant.role = "P";
  program::Names inputs;
  for (auto [i, type] : enumerate(signature.inputs)) {
    inputs.push_back("x" + std::to_string(i));
    participant.arguments.push_back({inputs.back(), type.spelling()});
  }
  program::Function function;
  function.name = "compute";
  function.origin = program::LogicalOrigin{"compute", {}};
  function.arguments = participant.arguments;
  function.results.push_back(signature.outputs.front().spelling());
  function.body.push_back(
      {"call",
       program::Operation{"numerical", {expression.str()}, inputs, {"r"}}});
  function.body.push_back({"", program::Return{{"r"}}});
  participant.results = function.results;
  participant.body.push_back(
      {"compute", program::LocalCall{"compute", inputs, {"r"}}});
  participant.body.push_back({"", program::Return{{"r"}}});
  result.functions.push_back(std::move(function));
  result.participants.push_back(std::move(participant));
  result.entries.push_back({"main", {{"P", "P"}}});
  return result;
}
} // namespace
int main() {
  Cases cases;
  for (StringRef field :
       {"bls12-381.fr", "bn254.fr", "ristretto255.scalar", "koala-bear",
        "koala-bear.ext4-binomial3", "koala-bear.ext8-binomial3",
        "gf2-64.pentanomial-4-3-1", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"})
    for (StringRef contract :
         {"numerical.map", "numerical.sum", "numerical.product"})
      cases.run(contract + " exact field " + field, [&] {
        require(
            authoringStage(contract) == AuthoringStage::CompilerGenerated &&
                none_of(boundOperationContracts(),
                        [&](const auto &op) { return op.name == contract; }),
            "consumer-owned signature leaked into the generic source API");
        BindingApplication binding{contract.str(), {field.str(), "001"}, ""};
        auto signature = take(resolveBinding(binding, false));
        require(signature.inputs.size() == 4 &&
                    signature.inputs[0].kind == "index" &&
                    signature.inputs[1].kind == "field" &&
                    signature.inputs[2].kind == "field" &&
                    signature.inputs[3].kind == "vector" &&
                    signature.outputs[0].kind ==
                        (contract == "numerical.map" ? "vector" : "field"),
                "leading zero mask changed its positional signature");
        accept(checkParameters(binding, {body(field)}));
        const auto implementation = take(defaultImplementation(binding));
        StringRef provider = field == "ristretto255.scalar" ? "dalek"
                             : field == "bn254.fr" || field == "bls12-381.fr"
                                 ? "arkworks"
                                 : "plonky3";
        require(implementation == (provider + "/" + contract).str(),
                "wrong installed provider");
        auto model = makeProgram(contract, field, "001", body(field));
        accept(protocol::admit(model));
        accept(program::checkStructure(model));
        auto decoded = take(program::parse(printJson(program::encode(model))));
        accept(protocol::admit(decoded));
        model.functions.front()
            .body.front()
            .get<program::Operation>()
            ->attributes = {body(field) + " "};
        refuse(protocol::admit(model), "numerical-body-canonical");
        binding.implementation =
            (provider == "arkworks" ? "dalek/" : "arkworks/") + contract.str();
        refuses(resolveBinding(binding, true), "binding-implementation");
      });
  for (StringRef mask : {"", "0", "00", "01", "10", "11"})
    cases.run("mask inventory " + mask, [&] {
      auto signature = take(resolveBinding(
          {"numerical.map", {"koala-bear", mask.str()}, ""}, false));
      require(signature.inputs.size() == mask.size() + 1,
              "mask was parsed as a number");
    });
  cases.run("mask maximum and invalid syntax", [&] {
    auto binding = BindingApplication{
        "numerical.map", {"koala-bear", std::string(1023, '0')}, ""};
    require(take(resolveBinding(binding, false)).inputs.size() == 1024,
            "maximum port inventory refused");
    for (const auto &mask :
         {std::string(1024, '1'), std::string("2"), std::string("01 "),
          std::string("\xc2\xb9"), std::string("0\0", 2)}) {
      binding.arguments[1] = mask;
      refuses(resolveBinding(binding, false), "numerical-mask");
    }
    for (const auto &args : std::vector<std::vector<std::string>>{
             {}, {"koala-bear"}, {"koala-bear", "", "0"}})
      refuses(resolveBinding({"numerical.map", args, ""}, false),
              "binding-static-arity");
    refuses(resolveBinding({"numerical.map", {"bn254.g1", "1"}, ""}, false),
            "binding-static-identity");
  });
  cases.run("canonical body byte boundary", [&] {
    take(readNumericalExpression(boundary(4096), "bls12-381.fr", 0));
    refuses(readNumericalExpression(boundary(4097), "bls12-381.fr", 0),
            "numerical-body-limit");
  });
  cases.run("closed body admission", [&] {
    BindingApplication binding{"numerical.map", {"koala-bear", "001"}, ""};
    auto original = body("koala-bear");
    refuse(checkParameters(binding, {}), "interactive-kernel-parameters");
    refuse(checkParameters(binding, {original, original}),
           "interactive-kernel-parameters");
    refuse(checkParameters(binding, {original + " "}),
           "numerical-body-canonical");
    refuse(checkParameters(binding, {body("bn254.fr")}),
           "numerical-body-field");
    binding.arguments[1] = "01";
    refuse(checkParameters(binding, {original}), "numerical-body-signature");
    auto two = take(ring::Expression::create({{"koala-bear"}},
                                             {ring::Node::slot(0)}, {0, 0}));
    refuses(readNumericalExpression(printJson(two.encode()), "koala-bear", 1),
            "numerical-body-signature");
    auto mixed = take(ring::Expression::create(
        {{"koala-bear"}},
        {ring::Node::slot(0),
         ring::Node::embed("koala-bear.ext4-binomial3", 0)},
        {1}));
    refuses(readNumericalExpression(printJson(mixed.encode()), "koala-bear", 1),
            "numerical-body-field");
    auto malformed = original;
    auto at = malformed.find("[\"input\",0]");
    require(at != std::string::npos, "missing body input");
    malformed.replace(at, 11, "[\"input\",9]");
    auto rejected = readNumericalExpression(malformed, "koala-bear", 3);
    require(!rejected, "out-of-range input admitted");
    consumeError(rejected.takeError());
  });
  cases.run("empty mask constant body and unused input field", [&] {
    auto constant = take(ring::Expression::create(
        {}, {ring::Node::literal("bn254.fr", "1")}, {0}));
    for (StringRef contract :
         {"numerical.map", "numerical.sum", "numerical.product"})
      accept(checkParameters({contract.str(), {"bn254.fr", ""}, ""},
                             {printJson(constant.encode())}));
    auto unused = take(ring::Expression::create({{"koala-bear"}, {"bn254.fr"}},
                                                {ring::Node::slot(0)}, {0}));
    refuses(
        readNumericalExpression(printJson(unused.encode()), "koala-bear", 2),
        "numerical-body-field");
  });
  return cases.result();
}
