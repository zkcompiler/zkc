#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <set>

using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
namespace {
unsigned failures = 0;
void check(bool condition, StringRef detail) {
  if (!condition) {
    errs() << detail << '\n';
    ++failures;
  }
}
void success(Error error, StringRef detail) {
  if (error) {
    errs() << detail << ": " << toString(std::move(error)) << '\n';
    ++failures;
  }
}
void refusal(Error error, StringRef expected) {
  if (!error) {
    check(false, "expected parameter refusal");
    return;
  }
  check(toString(std::move(error)) == expected, expected);
}
const generic::Signature &signature(StringRef key) {
  for (const auto &op : boundOperationContracts())
    if (op.name == key)
      return op.signature;
  errs() << "missing signature: " << key << '\n';
  std::exit(1);
}
bool type(const generic::Type &t, StringRef head,
          std::initializer_list<unsigned> args) {
  return t.constructor == head && t.arguments == std::vector<unsigned>(args);
}
void
  requires(StringRef op, StringRef capability)
{
  check(signature(op).requirements ==
            std::vector<requirements::Predicate>{
                requirements::Predicate::holds(capability.str(), {0})},
        op);
}
} // namespace
int main() {
  // Independent, hand-authored semantic witnesses. Do not replace these with
  // expectations emitted by the declaration generator.
  check(std::set<std::string>(domainSorts().begin(), domainSorts().end()) ==
            std::set<std::string>{"Field", "Group", "Commitment", "Transcript",
                                  "Codec"},
        "installed domain sorts");
  generic::Signature codecPromise;
  codecPromise.scope.sorts = {"Codec", "Field"};
  codecPromise.requirements = {
      requirements::Predicate::holds("Encodes.polynomial", {0, 1})};
  success(checkStaticVocabulary(codecPromise), "polynomial codec declaration");
  codecPromise.scope.sorts[1] = "Group";
  refusal(checkStaticVocabulary(codecPromise), "generic-predicate-sort");
  codecPromise.scope.sorts[1] = "Field";
  codecPromise.requirements[0].relation = "Encodes.rng";
  refusal(checkStaticVocabulary(codecPromise), "generic-declared-predicate");
  check(any_of(associatedMemberDeclarations(),
               [](const auto &member) {
                 return member.name == "Scalar" &&
                        member.owner ==
                            StaticParameter{StaticKind::Domain, "Group"} &&
                        member.result ==
                            StaticParameter{StaticKind::Domain, "Field"};
               }),
        "group scalar association has distinct owner and result sorts");
  requires("poly.univariate_evaluate", "CommRing");
  requires("poly.evaluate", "CommRing");
  requires("field.add", "Field");
  requires("poly.coset_evaluate", "TwoAdicField");
  requires("random.draw", "Field");
  requires("random.index", "IndexRandomness");
  check(parameterContract("field.constant")->fieldTerm == 0 &&
            parameterContract("vector.constant")->fieldTerm == 0 &&
            !parameterContract("field.add")->fieldTerm,
        "field literal domains are declaration-owned");
  success(
      checkParameters(BindingApplication{"field.constant", {"koala-bear"}, ""},
                      {"2130706432"}),
      "literal below KoalaBear modulus");
  refusal(
      checkParameters(BindingApplication{"field.constant", {"koala-bear"}, ""},
                      {"2130706433"}),
      "interactive-constant");
  success(checkParameters(
              BindingApplication{"field.constant", {"bls12-381.fr"}, ""},
              {"2130706433"}),
          "same literal has a different domain bound");
  refusal(checkParameters("field.constant", {"1"}), "interactive-constant");
  const auto &univariate = signature("poly.univariate_evaluate");
  const auto &multilinear = signature("poly.evaluate");
  check(type(univariate.inputs[0], "polynomial", {0}) &&
            type(univariate.inputs[1], "field", {0}) &&
            type(multilinear.inputs[0], "table", {0}) &&
            type(multilinear.inputs[1], "point", {0}),
        "univariate and multilinear evaluations conflated");
  check(signature("poly.even_odd_fold").requirements ==
            std::vector<requirements::Predicate>{
                requirements::Predicate::holds("TwoAdicField", {0}),
                requirements::Predicate::holds("CharacteristicNotTwo", {0})},
        "fold lost characteristic restriction");
  const auto &pcs = signature("pcs.check");
  check(pcs.scope.terms.size() == 4 && pcs.scope.terms[0].name == "C" &&
            pcs.scope.terms[1].name == "ValueField" &&
            pcs.scope.terms[2].name == "EvaluationField" &&
            pcs.scope.terms[3].name == "PointField" &&
            pcs.scope.terms[1].parent == 0 && pcs.scope.terms[2].parent == 0 &&
            pcs.scope.terms[3].parent == 0 &&
            type(pcs.inputs[2], "point", {3}) &&
            type(pcs.inputs[3], "field", {2}),
        "PCS associated fields lost their independent identities");
  check(type(signature("pcs.commit").inputs[1], "table", {1}),
        "PCS value field projection");
  const auto &embed = signature("field.embed");
  check(embed.scope.terms[0].name == "E" &&
            embed.scope.terms[1].name == "BaseField" &&
            embed.scope.terms[1].parent == 0 &&
            type(embed.inputs[0], "field", {1}) &&
            type(embed.outputs[0], "field", {0}),
        "extension embedding reversed base and extension");
  const auto &pairing = signature("pairing.check");
  check(pairing.scope.terms[1].name == "PairingG1" &&
            pairing.scope.terms[2].name == "PairingG2" &&
            type(pairing.inputs[0], "groups", {1}) &&
            type(pairing.inputs[1], "groups", {2}),
        "pairing groups collapsed");
  const auto &observe = signature("transcript.observe.field");
  check(observe.scope.terms[0].name == "T" &&
            observe.scope.terms[1].name == "F" &&
            !observe.scope.terms[1].parent &&
            observe.scope.terms[2].name == "E" &&
            observe.requirements ==
                std::vector<requirements::Predicate>{
                    requirements::Predicate::holds("Transcript", {0}),
                    requirements::Predicate::holds("Encodes.field", {2, 1})},
        "observation codec root or payload requirement lost");
  const auto &observeBool = signature("transcript.observe.bool");
  check(observeBool.requirements[1] ==
            requirements::Predicate::holds("Encodes.bool", {1}),
        "unparameterized observation codec lost");
  const auto &draw = signature("transcript.challenge");
  check(draw.scope.terms[1].name == "ChallengeField" &&
            draw.scope.terms[1].parent == 0 &&
            type(draw.outputs[0], "field", {1}),
        "transcript challenge projection lost");

  // Stage and export policy are separate from common carrier formation.
  check(authoringStage("poly.univariate_evaluate") == AuthoringStage::Source &&
            authoringStage("random.draw") == AuthoringStage::Source &&
            authoringStage("transcript.challenge") ==
                AuthoringStage::Construction &&
            authoringStage("unknown.call") != AuthoringStage::Source,
        "source authoring stage boundary");
  bool foundEvaluate = false, foundMultilinear = false;
  for (const auto &e : sourceOperationExports()) {
    check(authoringStage(e.contract) == AuthoringStage::Source &&
              !StringRef(e.contract).starts_with("transcript."),
          "construction operation leaked through export");
    if (e.module == "zkc::poly" && e.name == "evaluate")
      foundEvaluate =
          e.contract == "poly.univariate_evaluate" &&
          e.inputLabels == std::vector<std::string>{"polynomial", "point"};
    if (e.module == "zkc::poly" && e.name == "evaluate_multilinear")
      foundMultilinear = e.contract == "poly.evaluate";
  }
  check(foundEvaluate && foundMultilinear, "curated polynomial exports");
  check(sourceTypeFamilies().size() == 3 &&
            any_of(sourceTypeFamilies(),
                   [](const auto &f) {
                     return f.family == "vector-family" &&
                            f.elementConstructor == "group" &&
                            f.resultConstructor == "groups";
                   }) &&
            none_of(sourceTypeFamilies(),
                    [](const auto &f) {
                      return f.family == "matrix-family" &&
                             f.elementConstructor == "group";
                    }),
        "source families must preserve supported element cases");
  check(any_of(sourceAssociatedTypes(),
               [](const auto &t) {
                 return t.sort == "Field" && t.member == "Element" &&
                        t.constructor == "field";
               }) &&
            any_of(sourceAssociatedTypes(),
                   [](const auto &t) {
                     return t.sort == "Group" && t.member == "Element" &&
                            t.constructor == "group";
                   }),
        "associated source element types");
  check(any_of(sourceCapabilityExports(),
               [](const auto &c) {
                 return c.module == "zkc::algebra" && c.name == "Field" &&
                        c.predicate == "Field";
               }),
        "Field capability export");
  check(any_of(sourceTypeExports(),
               [](const auto &e) {
                 return e.module == "zkc::poly" && e.name == "Polynomial" &&
                        e.constructor == "polynomial";
               }),
        "polynomial constructor export");
  check(sourceOperatorBindings().size() == 15, "operator inventory changed");
  check(any_of(sourceOperatorBindings(),
               [](const auto &b) {
                 return b.symbol == "*" &&
                        b.operands ==
                            std::vector<std::string>{"field", "group"} &&
                        b.contract == "curve.scale" &&
                        b.order == std::vector<unsigned>{1, 0};
               }),
        "scalar/group permutation lost");
  check(none_of(sourceOperatorBindings(),
                [](const auto &b) {
                  return b.symbol == "*" &&
                         b.operands ==
                             std::vector<std::string>{"vector", "vector"};
                }),
        "ambiguous vector multiplication acquired sugar");
  for (auto key :
       {"external.monero.update", "external.openvm.observe",
        "external.openvm.sample", "external.openvm.sample_ext",
        "external.openvm.sample_bits", "external.openvm.check_witness"}) {
    auto *facets = operationContracts(key);
    check(facets && facets->history && facets->history->stateInput == 0 &&
              facets->history->stateOutput == 0 && !facets->sampling,
          "external snapshot history or sampling authority changed");
  }
  check(duplicable("indices") && discardable("indices"),
        "external snapshots stopped being copyable values");
  for (auto t : {"rng", "nonce", "transcript", "capability"})
    check(!duplicable(t) && !discardable(t) && custody(t) == Custody::Affine,
          "linear provider permissions changed");
  check(!duplicable("resource_unit") && discardable("resource_unit"),
        "resource unit drop permission lost");
  for (auto t :
       {"opening_state", "opening_states", "prover_key", "verifier_key"})
    check(duplicable(t) && discardable(t) &&
              custody(t) == Custody::PrivateImmutable,
          "private immutable custody changed");
  check(!typePermissions("fixture_array"),
        "Type/Nat fixture installed in production");
  check(operationEffect("unknown.call").empty(),
        "unknown operation acquired an effect envelope");
  check(!operationPurity("unknown.call"),
        "unknown operation acquired a purity contract");
  for (auto name : {"field.add", "field.mul", "curve.generator", "curve.add",
                    "curve.scale", "curve.equal"})
    check(operationPurity(name) == OperationPurity::Total, name);
  for (auto name : {"field.inverse", "curve.get", "control.require",
                    "curve.commit", "curve.response"})
    check(operationPurity(name) == OperationPurity::Ordered, name);
  for (const auto &kernel : kernels())
    check(operationEffect(kernel.key) == "local", kernel.key);
  auto unsupported = parseBoundType("fixture_array:anything", false);
  check(!unsupported, "generation-only constructor admitted");
  if (!unsupported)
    consumeError(unsupported.takeError());
  generic::Signature kinds;
  kinds.scope = {{{"T"}, {"N"}}, {"Type", "Nat"}};
  success(checkStaticVocabulary(kinds),
          "Type and Nat are installed static kinds");
  kinds.scope.sorts[0] = "UnknownKind";
  refusal(checkStaticVocabulary(kinds), "generic-declared-sort");

  success(checkParameters("field.constant", {"1"}, "bn254.fr"),
          "field literal");
  refusal(checkParameters("field.constant", {fieldModulus("bn254.fr").str()},
                          "bn254.fr"),
          "interactive-constant");
  refusal(checkParameters("field.constant", {"1"}, "unknown.field"),
          "interactive-constant");
  refusal(checkParameters("vector.constant", {"01"}), "noncanonical-natural");
  refusal(checkParameters("vector.constant", {"-1"}), "expected-natural");
  success(checkParameters("vector.constant", {}), "empty vector literal");
  refusal(checkParameters("vector.scatter_sum", {}),
          "interactive-kernel-parameters");
  success(checkParameters("vector.scatter_sum", {"1048577"}),
          "scatter keeps uint64 bound");
  refusal(checkParameters("vector.gather", {"1048577"}),
          "interactive-kernel-parameters");
  refusal(checkParameters("curve.at", {"1048577"}), "interactive-index");
  success(checkParameters("matrix.shape_check", {"65536", "65536"}),
          "matrix boundary");
  refusal(checkParameters("matrix.shape_check", {"65537", "1"}),
          "interactive-kernel-parameters");
  refusal(checkParameters("vector.matvec", {"1", "1", "2"}),
          "interactive-kernel-parameters");
  success(checkParameters("matrix.identity_check", {std::string(64, 'a')}),
          "matrix digest");
  refusal(checkParameters("matrix.identity_check", {std::string(64, 'A')}),
          "interactive-kernel-parameters");
  success(checkParameters("transcript.challenge", {"a", "b", "c", "d", "e"}),
          "transcript origin");
  refusal(checkParameters("transcript.challenge", {"a", "b", "c", "d", "!"}),
          "interactive-transcript-origin");

  // The generated structures must also satisfy the independent C++ checker.
  for (const auto &op : boundOperationContracts()) {
    success(checkStaticVocabulary(op.signature), op.name);
    check(operationEffect(op.name) == "local", "local envelope lost");
    generic::Function function;
    function.signature = op.signature;
    generic::Call call;
    call.site = "witness";
    call.operation = op.name;
    for (auto [i, term] : enumerate(op.signature.scope.terms))
      if (!term.parent && !term.arguments &&
          !op.signature.scope.constants.count(i))
        call.staticArguments.push_back(i);
    for (unsigned i = 0; i < op.signature.inputs.size(); ++i)
      call.inputs.push_back(i);
    function.body.push_back(std::move(call));
    for (unsigned i = 0; i < op.signature.outputs.size(); ++i)
      function.returns.push_back(op.signature.inputs.size() + i);
    auto checked =
        generic::check(function, boundTypeConstructors(),
                       boundOperationContracts(), boundCapabilityRules());
    if (!checked)
      success(checked.takeError(), op.name);
  }
  return failures ? 1 : 0;
}
