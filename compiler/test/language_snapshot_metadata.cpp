#include "../lib/Language/Semantics.h"
#include "../lib/Language/TypeInference.h"
#include "support/NativeCases.h"
#include <functional>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
using K = Type::Kind;
Type parameter(Permissions assumptions) {
  Type result(K::Parameter, "X");
  result.symbolic = true;
  result.assumptions = assumptions;
  return result;
}
Type record(Type argument) {
  Type result(K::Record, "R");
  result.arguments.push_back(std::move(argument));
  return result;
}
std::vector<Declaration> declarations() {
  Declaration result;
  result.id = {0};
  result.kind = Declaration::Kind::Record;
  result.name = result.qualifiedName = "R";
  Parameter formal;
  formal.name = "T";
  formal.atom = "R::T";
  formal.sort = Parameter::Sort::Type;
  result.parameters.push_back(formal);
  result.fields.push_back({"value", parameterType(formal), true, {}});
  return {std::move(result)};
}
bool snapshot(const Type &a, const Type &b) {
  TypeComparison comparison{b};
  take(typeComplexity(a, 128, 32, UINT64_MAX, nullptr, false, TypeWork::Copy,
                      &comparison));
  return comparison.equal;
}
} // namespace
int main() {
  Cases cases;
  for (bool reverse : {false, true})
    for (bool nested : {false, true})
      cases.run(
          "field results preserve permission metadata order=" + Twine(reverse) +
              " nested=" + Twine(nested),
          [&] {
            std::shared_ptr<const std::vector<TypeField>> first, second;
            Type firstInput, secondInput;
            {
              Limits limits;
              Work work{limits};
              auto source = declarations();
              Semantics types(source, {}, work);
              auto argument = parameter({!reverse, !reverse});
              if (nested) {
                Type tuple(K::Tuple);
                tuple.arguments = {argument, Type(K::Index)};
                argument = std::move(tuple);
              }
              firstInput = record(argument);
              secondInput = firstInput;
              auto &changed = nested ? secondInput.arguments[0].arguments[0]
                                     : secondInput.arguments[0];
              changed.assumptions = {reverse, reverse};
              require(firstInput == secondInput &&
                          typeIdentity(firstInput) == typeIdentity(secondInput),
                      "private memo changed nominal identity");
              first = types.fields(firstInput, {});
              second = types.fields(secondInput, {});
              require(first && second, "ordinary field query failed");
              require(
                  snapshot(first->front().type, firstInput.arguments[0]) &&
                      snapshot(second->front().type, secondInput.arguments[0]),
                  "field memo returned the other query's metadata");
              auto again = types.fields(firstInput, {});
              require(again == first,
                      "metadata collision discarded the first entry");
              auto observed =
                  types.permissions(nested ? second->front().type.arguments[0]
                                           : second->front().type,
                                    {});
              require(observed && *observed == changed.assumptions,
                      "copied metadata disagrees with permission observation");
              // Each hit keeps its current bounded preflight, even after
              // priming.
              limits.typeNodes = 1;
              require(!types.fields(firstInput, {}) && types.diagnostic &&
                          types.diagnostic->code == "source.limit",
                      "cached result bypassed current node bounds");
            }
            require(
                snapshot(first->front().type, firstInput.arguments[0]) &&
                    snapshot(second->front().type, secondInput.arguments[0]),
                "returned fields borrowed their memo or declaration owner");
          });
  cases.run(
      "snapshot equality observes every Type head and recursive child", [] {
        Type natural(K::Natural, "retained");
        natural.symbolic = true;
        natural.sort = "metadata";
        natural.dimension = take(Natural::atom("N"));
        natural.arguments = {parameter({true, false})};
        std::vector<std::function<void(Type &)>> mutations{
            [](Type &t) { t.kind = K::Parameter; },
            [](Type &t) { t.family = static_cast<DescriptorFamily>(1); },
            [](Type &t) { t.domain += "x"; },
            [](Type &t) { t.sort += "x"; },
            [](Type &t) { t.symbolic = false; },
            [](Type &t) { t.assumptions.copy = true; },
            [](Type &t) { t.assumptions.drop = true; },
            [](Type &t) { t.dimension = Natural::constant(3); },
            [](Type &t) { t.arguments.clear(); },
            [](Type &t) { t.arguments[0].assumptions.drop = true; }};
        for (const auto &mutate : mutations) {
          Type other = natural;
          mutate(other);
          require(!snapshot(natural, other) && !snapshot(other, natural),
                  "snapshot comparison erased retained metadata");
        }
        TypeComparison comparison{natural};
        const auto cost =
            take(typeComplexity(natural, 3, 2, UINT64_MAX, nullptr, false,
                                TypeWork::Copy, &comparison));
        require(comparison.equal && cost > 0,
                "equal snapshot comparison failed");
        comparison.equal = true;
        refuses(typeComplexity(natural, 3, 2, cost - 1, nullptr, false,
                               TypeWork::Copy, &comparison),
                "source.limit");
        comparison.equal = true;
        require(take(typeComplexity(natural, 3, 2, cost, nullptr, false,
                                    TypeWork::Copy, &comparison)) == cost &&
                    comparison.equal,
                "exact bounded snapshot retry changed work");
      });
  for (bool reverse : {false, true})
    cases.run(
        "Layout cache preserves owned metadata order=" + Twine(reverse), [&] {
          auto captured = take(capture({{"m", "module m;", "snapshot.zkc"}}));
          auto checked = take(analyze(captured).checkedProject());
          std::shared_ptr<const Layout> first, second;
          Type a(K::Tuple);
          a.arguments = {Type(K::Index)};
          a.arguments[0].assumptions = {!reverse, reverse};
          auto b = a;
          b.arguments[0].assumptions = {reverse, !reverse};
          {
            Layouts layouts(checked);
            first = take(layouts.get(a));
            second = take(layouts.get(b));
            require(first->identity.key == second->identity.key &&
                        snapshot(first->type, a) && snapshot(second->type, b),
                    "Layout cache substituted another candidate's metadata");
            require(take(layouts.get(a)) == first,
                    "Layout metadata collision lost its original result");
          }
          require(snapshot(first->type, a) && snapshot(second->type, b),
                  "Layout result lifetime depended on its observer");
        });
  cases.run("inference memo retains separate equation metadata and rollback",
            [] {
              Limits limits;
              Work work{limits};
              std::vector<Declaration> source;
              Semantics types(source, {}, work);
              TypeInference inference(types);
              auto a = parameter({true, false}), b = parameter({false, true});
              auto x = inference.known(a, {}), y = inference.known(b, {});
              auto checkpoint = inference.checkpoint({});
              require(bool(checkpoint), "checkpoint refused");
              require(snapshot(*inference.get(x, {}), a) &&
                          snapshot(*inference.get(y, {}), b),
                      "separate equations shared nominal metadata");
              require(inference.equal(x, y, {}),
                      "nominal equations stopped unifying");
              require(inference.restore(*checkpoint, {}), "restore refused");
              require(snapshot(*inference.get(x, {}), a) &&
                          snapshot(*inference.get(y, {}), b),
                      "rollback exposed a stale reconstructed result");
            });
  cases.run("helper preflight refuses with current phase without a debit", [] {
    Limits limits;
    limits.work = 64;
    uint64_t allowance = 32;
    Work work{limits};
    work.allowance = &allowance;
    std::vector<Declaration> source;
    Semantics types(source, {}, work);
    require(!work.charge(3), "prefix failed");
    Work::Scope phase(work, SourceWorkPhase::Specialization);
    Type large(K::Parameter, std::string(64, 'x'));
    require(!types.chargeIdentity(large, {}) && types.diagnostic &&
                types.diagnostic->code == "source.limit" &&
                StringRef(types.diagnostic->message)
                    .contains("in specialization") &&
                work.used == 3 && allowance == 29 &&
                work.ledger.used(SourceWorkPhase::Specialization) == 0,
            "helper preflight changed phase, refusal debit or allowance");
    types.diagnostic.reset();
    zkc::source::Cancellation cancellation;
    work.cancellation = cancellation;
    cancellation.cancel();
    require(!types.chargeIdentity(large, {}) && types.diagnostic &&
                types.diagnostic->code == "source.cancelled" && work.used == 3,
            "preflight refusal overrode cancellation or charged failed work");
  });
  return cases.result();
}
