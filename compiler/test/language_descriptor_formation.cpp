#include "../lib/Language/Checker.h"
#include "../lib/Language/DescriptorClosure.h"
#include "../lib/Language/DescriptorFrames.h"
#include "../lib/Language/DescriptorPatterns.h"
#include "../lib/Language/DescriptorSequence.h"
#include "../lib/Language/DescriptorWitness.h"
#include "../lib/Language/FormationCursor.h"
#include "../lib/Language/ScopedWitness.h"
#include "../lib/Language/State.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/CommonControl.h"
#include "zkc/Language/Project.h"
#include <algorithm>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
const Limits defaultLimits;
const std::string prelude = R"(module m
use zkc::descriptor as ds
type Finite<I: Type + Copy + Drop> = builtin("finite", I)
view def range(lo: index, hi: index) -> Finite<index> = domain("range")
)";
Expected<CheckedProject> check(StringRef source) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured =
      capture({{"m", prelude + source.str(), "formation.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
void accepted(StringRef source) {
  auto project = take(check(source));
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing source declaration");
}
const std::string guardSource = R"(
view def zip<A: Type + Copy + Drop, B: Type + Copy + Drop>(a: Finite<A>, b: Finite<B>) -> Finite<(A, B)> = domain("zip")
view def guarded(a: index, b: index, c: index, d: index) -> ds::Product<Finite<index>, ds::Sequence<Finite<index>>>:
    checked = zip(range(a, b), range(c, d))
    empty: ds::Sequence<Finite<index>> = ds::concat([], [])
    return (range(a, b), empty)
def example(a: index, b: index, c: index, d: index) -> index:
    unrelated = range(d, c)
    selected = guarded(d=d, b=b, a=a, c=c)
    result = selected.0
    return a
)";

} // namespace
int main() {
  Cases cases;
  cases.run("empty product source expectation", [] {
    accepted("view def unit() -> ds::Product<>:\n    return ()\n");
  });
  for (unsigned arity : {1u, 2u, 3u, 5u})
    cases.run("ordered heterogeneous product " + Twine(arity), [&] {
      std::string contract, tuple;
      for (unsigned i = 0; i < arity; ++i) {
        if (i) {
          contract += ", ";
          tuple += ", ";
        }
        contract += i % 2 ? "Finite<bool>" : "Finite<index>";
        tuple += i % 2 ? "b" : "a";
      }
      if (arity == 1)
        tuple += ",";
      accepted(
          "view def pack(a: Finite<index>, b: Finite<bool>) -> ds::Product<" +
          contract + ">:\n    return (" + tuple + ")\n");
    });
  for (StringRef literal : {"[(), u]", "[u, ()]"})
    cases.run("rigid unit sibling " + literal, [&] {
      accepted("view def pairs(u: ds::Product<>) -> "
               "ds::Sequence<ds::Product<>, 2>:\n    values = " +
               literal.str() + "\n    return values\n");
    });
  for (StringRef literal : {"[[], xs]", "[xs, []]"})
    cases.run("rigid nested empty sibling " + literal, [&] {
      accepted("view def lists(xs: ds::Sequence<Finite<index>>) -> "
               "ds::Sequence<ds::Sequence<Finite<index>>, 2>:\n    values = " +
               literal.str() + "\n    return values\n");
    });
  for (StringRef literal : {"[[()], [u]]", "[[u], [()]]"})
    cases.run("nested fresh aggregates collect sibling evidence " + literal,
              [&] {
                accepted("view def nested(u: ds::Product<>) -> "
                         "ds::Sequence<ds::Sequence<ds::Product<>, 1>, 2>:\n   "
                         " values = " +
                         literal.str() + "\n    return values\n");
              });
  for (StringRef literal : {"[(), relay(d)]", "[relay(d), ()]"})
    cases.run("inferred call result is rigid sibling evidence " + literal, [&] {
      accepted("view def relay<T: Type + Copy + Drop>(d: Finite<T>) -> "
               "ds::Product<>:\n    return ()\n"
               "view def nested(d: Finite<index>) -> "
               "ds::Sequence<ds::Product<>, 2>:\n    values = " +
               literal.str() + "\n    return values\n");
    });
  for (bool zipped : {false, true})
    cases.run(
        zipped ? "unresolved Zip cardinality stays unknown until closure"
               : "unresolved Product cardinality stays unknown until closure",
        [&] {
          auto count = zipped ? "2" : "4";
          const auto program = std::string(R"(
domain F = field("koala-bear")
type Array<E: Field, N: nat> = builtin("field_array", E, N)
view def array<T: Type + Copy + Drop, N: nat>(xs: [T; N]) -> Finite<T> = domain("source_array")
view def combined<A: Type + Copy + Drop, B: Type + Copy + Drop>(a: Finite<A>, b: Finite<B>) -> Finite<(A, B)> = domain(")") +
                               (zipped ? "zip" : "product") + R"(")
def collect<I: Type + Copy + Drop, N: nat>(rows: Finite<I>, body: fn(item: I) -> F where item_from(item, rows)) -> Array<F, N> = finite("math.collect.field_array")
def work(a: Finite<F>, b: Finite<F>) -> Array<F, )" +
                               count + R"(>:
    return collect(combined(a, b), fn((x, y)) => x)
def assembled(a: F) -> Array<F, )" +
                               count +
                               R"(>:
    return work(array([a, a]), array([a, a]))
pub protocol Demo roles(P)(a: F @P) -> Array<F, )" +
                               count + R"(> @P:
    return assembled(a)
)";
          auto project = take(check(program));
          auto closed = take(closeNativeRun(project, "m::Demo"));
          if (auto error = checkScopedSpecialization(closed))
            throw std::runtime_error(toString(std::move(error)));
          auto invalid = program;
          const std::string extent = std::string("Array<F, ") + count + ">";
          for (size_t pos = 0;
               (pos = invalid.find(extent, pos)) != std::string::npos;)
            invalid.replace(pos, extent.size(), "Array<F, 3>");
          auto wrongExtent = check(invalid);
          if (wrongExtent) {
            auto result = closeNativeRun(*wrongExtent, "m::Demo");
            require(!result,
                    "closed product/zip accepted a false collect extent");
            consumeError(result.takeError());
          } else
            consumeError(wrongExtent.takeError());
          if (zipped) {
            invalid = program;
            auto pos = invalid.find("array([a, a]), array([a, a])");
            require(pos != std::string::npos, "Zip control source missing");
            invalid.replace(pos,
                            std::string("array([a, a]), array([a, a])").size(),
                            "array([a, a]), array([a])");
            auto unequal = take(check(invalid));
            auto result = closeNativeRun(unequal, "m::Demo");
            require(!result,
                    "closed Zip accepted unequal actual child extents");
            consumeError(result.takeError());
          }
        });
  cases.run("all installed sequence schemes", [] {
    accepted(R"(
view def schemes(d: Finite<index>) -> Finite<index>:
    a: ds::Sequence<Finite<index>> = ds::append([], d)
    b = ds::concat(a, [])
    c = ds::replace<Index=0>(b, d)
    fixed = ds::sized<Length=1>(c)
    unsized = ds::unsized(fixed)
    return unsized[0]
)");
  });
  for (unsigned width : {1u, 64u})
    for (bool sequence : {false, true})
      cases.run(
          (sequence ? "abstract sequence route retains input dependencies "
                    : "abstract product route retains input dependencies ") +
              Twine(width),
          [&] {
            std::string item = width == 1 ? "index" : "(";
            if (width != 1) {
              for (unsigned i = 0; i < width; ++i)
                item += i ? ", index" : "index";
              item += ")";
            }
            auto container = sequence ? "ds::Sequence<Finite<" + item + ">, 1>"
                                      : "ds::Product<Finite<" + item + ">>";
            auto project = take(check(
                "def fold<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: "
                "Finite<I>, initial: S, step: fn(S, item: I) -> S where "
                "item_from(item, rows)) -> S = finite(\"math.fold\")\n"
                "interface Factory:\n    view def make(n: index) -> " +
                std::string(container) +
                "\n    view def inspect(d: " + container +
                ") -> Finite<index>\ndef selected<C: Factory>(n: index) -> "
                "index:\n"
                "    values = C::make(n)\n    child = values" +
                (sequence ? "[0]" : ".0") +
                "\n    combined = C::inspect(values)\n    return n\n"
                "def dependent<C: Factory>(n: index) -> bool:\n"
                "    return fold(C::inspect(C::make(n)), true, fn(s, item) => "
                "s)\n"
                "pub protocol Generic<C: Factory> roles(P, V)(n: index @(P, "
                "V)) "
                "-> bool @(P, V):\n"
                "    condition = dependent<C>(n)\n"
                "    return if condition:\n        true\n    else:\n        "
                "false\n"));
            auto requirements = take(deriveCommonControlRequirements(
                project, named(project, "m::Generic").id));
            require(requirements.size() == 1 &&
                        requirements.front().components.size() == 2 &&
                        llvm::all_of(requirements.front().components,
                                     [](const auto &component) {
                                       return component.input == 0;
                                     }),
                    "abstract structural source lost its common-input premise");
            Limits bounded;
            bounded.work = 512;
            refuses(deriveCommonControlRequirements(
                        project, named(project, "m::Generic").id, bounded),
                    "source.limit");
            const auto &decl = named(project, "m::selected");
            std::vector<Declaration> declarations(
                project.declarations().begin(), project.declarations().end());
            Work work{defaultLimits};
            Semantics types(declarations, project.assets(), work);
            for (unsigned root : {1u, 2u}) {
              auto formation =
                  formDescriptor(types, declarations, *decl.body, root);
              require(formation.has_value(),
                      types.diagnostic ? types.diagnostic->message
                                       : "abstract formation missing");
              unsigned applications = 0;
              auto leaf =
                  [&](const DescriptorBinding &node, ArrayRef<ValueId> data,
                      ArrayRef<unsigned> children) -> std::optional<unsigned> {
                unsigned dependencies = 0;
                for (auto value : data)
                  dependencies |= 1u << value.index;
                for (auto child : children)
                  dependencies |= child;
                if (node.kind == DescriptorBinding::Kind::Application) {
                  require(node.factory && node.factory->module,
                          "abstract route lost its callable/module identity");
                  ++applications;
                }
                return dependencies;
              };
              auto compose =
                  [](DescriptorBinding::Kind, const DescriptorContract &,
                     ArrayRef<Type>,
                     ArrayRef<unsigned> children) -> std::optional<unsigned> {
                unsigned dependencies = 0;
                for (auto child : children)
                  dependencies |= child;
                return dependencies;
              };
              auto read = readFormation<unsigned>(
                  types, *formation,
                  [](std::optional<unsigned>, const DescriptorContract &) {
                    return 0u;
                  },
                  leaf, compose);
              require(read && read->selected == 1 && applications >= 1,
                      types.diagnostic
                          ? types.diagnostic->message
                          : "abstract structural route lost actual n");
            }
          });
  cases.run(
      "source analysis preserves shared sequence history without flattening",
      [] {
        std::string source =
            "view def shared(d: Finite<index>) -> "
            "ds::Sequence<Finite<index>>:\n    s0: ds::Sequence<Finite<index>> "
            "= ds::append([], d)\n";
        for (unsigned i = 1; i <= 40; ++i)
          source += "    s" + std::to_string(i) + " = ds::concat(s" +
                    std::to_string(i - 1) + ", s" + std::to_string(i - 1) +
                    ")\n";
        source += "    return s40\ndef example(a: index, b: index) -> index:\n "
                  "   values = shared(range(a, b))\n    selected = values[0]\n "
                  "   return a\n";
        auto project = take(check(source));
        const auto &body = *named(project, "m::example").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        Work work{defaultLimits};
        Semantics types(declarations, project.assets(), work);
        unsigned root = body.descriptorBindings.size() - 1;
        auto formation = formDescriptor(types, declarations, body, root);
        require(formation.has_value(), types.diagnostic
                                           ? types.diagnostic->message
                                           : "shared source formation missing");
        auto read = readFormation<unsigned>(
            types, *formation,
            [](std::optional<unsigned>, const DescriptorContract &) {
              return 1u;
            },
            [](const DescriptorBinding &, ArrayRef<ValueId>,
               ArrayRef<unsigned>) -> std::optional<unsigned> { return 1u; },
            [](DescriptorBinding::Kind, const DescriptorContract &,
               ArrayRef<Type>,
               ArrayRef<unsigned>) -> std::optional<unsigned> { return 1u; });
        require(read && read->selected == 1,
                types.diagnostic
                    ? types.diagnostic->message
                    : "shared analysis flattened sequence histories");
        auto closed = closeDescriptor(types, declarations, body, root, {}, {});
        require(closed && closed->shape->nodes.size() == 1 &&
                    checkDescriptorClosure(types, declarations, body, root, {},
                                           {}, *closed),
                types.diagnostic
                    ? types.diagnostic->message
                    : "generic length became a native assertion cap");
        require(work.used < defaultLimits.work / 2,
                "shared sequence history lost bounded headroom");
      });
  cases.run("static selectors use the existing Natural arithmetic", [] {
    accepted(R"(
view def select<N: nat>(xs: ds::Sequence<Finite<index>, 4>) -> Finite<index>:
    return xs[pow2(0) + 0 * N]
)");
  });
  for (StringRef source :
       {"view def recursive(d: Finite<index>) -> Finite<index>:\n    return "
        "recursive(d)\n",
        "module Cycle:\n    pub view def step<I: nat>(context: ds::Product<>, "
        "state: ds::Product<>) -> ds::Product<>:\n        return "
        "ds::fold<Count=0>(member=Cycle::step, context=context, seed=state)\n"})
    cases.run("source admission refuses a cycle before caching " + source, [&] {
      auto project = check(source);
      require(!project, "recursive source admission escaped a result cache");
      consumeError(project.takeError());
    });
  for (unsigned count : {0u, 1u, 3u})
    cases.run("source selected Fold " + Twine(count), [&] {
      accepted(R"(
module Build:
    pub view def step<I: nat>(context: ds::Product<Finite<index>>, state: ds::Sequence<Finite<index>>) -> ds::Sequence<Finite<index>>:
        return ds::append(state, context.0)
view def generated(d: Finite<index>) -> ds::Sequence<Finite<index>>:
    return ds::fold<Count=)" +
               std::to_string(count) +
               R"(>(seed=[], member=Build::step, context=(d,))
)");
    });
  for (bool nested : {false, true})
    for (unsigned mutation = 0; mutation < (nested ? 9u : 8u); ++mutation)
      cases.run(
          (nested ? "nested zero Fold source route mutation "
                  : "zero Fold source route mutation ") +
              Twine(mutation),
          [&] {
            std::string source = R"(
module Build:
    pub view def step<I: nat>(context: ds::Product<Finite<index>>, state: ds::Sequence<Finite<index>>) -> ds::Sequence<Finite<index>>:
        return ds::append(state, context.0)
)";
            source += nested ? R"(
local def example(flag: bool, a: index, b: index) -> index:
    descriptor = range(a, b)
    other = range(b, a)
    return if flag:
        sequence = ds::fold<Count=0>(member=Build::step, context=(descriptor,), seed=[])
        a
    else:
        b
)"
                             : R"(
def example(a: index, b: index) -> index:
    sequence = ds::fold<Count=0>(member=Build::step, context=(range(a, b),), seed=[])
    return a
)";
            auto project = take(check(source));
            if (auto error = checkScopedElaboration(project))
              throw std::runtime_error(toString(std::move(error)));
            auto *selected = named(project, "m::example").body.get();
            const Control *selectedControl = nullptr;
            if (nested)
              for (const auto &op : selected->operations)
                if (const auto *control = std::get_if<Control>(&op.action)) {
                  selectedControl = control;
                  selected = control->regions.front().get();
                  break;
                }
            auto &body = const_cast<Body &>(*selected);
            auto &binding = body.descriptorBindings.back();
            require(binding.kind == DescriptorBinding::Kind::Fold &&
                        binding.selectedView.has_value(),
                    "zero Fold fixture lost its selected member");
            if (mutation == 0)
              binding.selectedView.reset();
            if (mutation == 1)
              ++binding.selectedView->iteration;
            if (mutation == 2)
              binding.selectedView->target.declaration =
                  named(project, "m::range").id;
            if (mutation == 3)
              std::swap(binding.selectedView->context,
                        binding.selectedView->state);
            if (mutation == 4)
              binding.selectedView->arguments.front().dimension =
                  Natural::constant(0);
            if (mutation == 5)
              binding.arguments.front().dimension = Natural::constant(1);
            if (mutation == 6)
              std::reverse(binding.argumentOrder.begin(),
                           binding.argumentOrder.end());
            if (mutation == 7)
              ++*binding.expression;
            if (mutation == 8) {
              require(selectedControl &&
                          selectedControl->descriptorArguments.size() == 1,
                      "nested source lost its descriptor transfer");
              const_cast<Control *>(selectedControl)->descriptorArguments[0] =
                  1;
            }
            auto error = checkScopedElaboration(project);
            require(bool(error),
                    "zero Fold trusted candidate selection metadata");
            consumeError(std::move(error));
          });
  for (unsigned mutation = 0; mutation < 5; ++mutation)
    cases.run(
        "protocol repeat copied descriptor relation " + Twine(mutation), [&] {
          auto project = take(check(R"(
pub protocol Example roles(P)(a: index @P, b: index @P) -> index @P:
    descriptor = range(a, b)
    for iteration in 0..2:
        sequence = ds::append([], descriptor)
    return a
)"));
          if (auto error = checkScopedElaboration(project))
            throw std::runtime_error(toString(std::move(error)));
          auto &body = const_cast<Body &>(*named(project, "m::Example").body);
          ProtocolRepeat *repeat = nullptr;
          for (auto &op : body.operations)
            if (auto *found = std::get_if<ProtocolRepeat>(&op.action))
              repeat = found;
          require(repeat && repeat->region &&
                      !repeat->region->descriptorBindings.empty(),
                  "protocol repeat lost its copied recipe");
          auto &nested = const_cast<Body &>(*repeat->region);
          auto &copy = nested.descriptorBindings.front();
          if (mutation == 0)
            std::swap(copy.operands[0], copy.operands[1]);
          if (mutation == 1)
            ++*copy.expression;
          if (mutation == 2)
            copy.contract =
                DescriptorContract(Type(Type::Kind::DescriptorProduct));
          if (mutation == 3)
            std::reverse(repeat->captures.begin(), repeat->captures.end());
          if (mutation == 4)
            nested.descriptorBindings.push_back(copy);
          auto error = checkScopedElaboration(project);
          require(bool(error),
                  "copied descriptor trusted candidate origins or coverage");
          consumeError(std::move(error));
        });
  cases.run("implicit selected Math body owns descriptor formations", [] {
    accepted(R"(
def fold<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: fn(S, item: I) -> S where item_from(item, rows)) -> S = finite("math.fold")
view def packed(d: Finite<index>) -> ds::Sequence<Finite<index>>:
    return ds::append([], d)
pub protocol Example roles(P)(flag: bool @P, a: index @P, b: index @P) -> bool @P:
    return flag and fold(packed(range(a, b))[0], true, fn(state, item) => state)
)");
  });
  // Observed integration gap: InstalledViewScheme is not yet recognized by
  // the coordinator-owned Boolean mathematical-expression classifier. This
  // receipt preserves the original failing positive, not a language ban.
  cases.run("known integration gap: direct scheme in protocol Boolean Math",
            [] {
              refuses(check(R"(
def fold<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: fn(S, item: I) -> S where item_from(item, rows)) -> S = finite("math.fold")
pub protocol Example roles(P)(flag: bool @P, a: index @P, b: index @P) -> bool @P:
    return flag and fold(ds::append([], range(a, b))[0], true, fn(state, item) => state)
)"),
                      "source.mode");
            });
  for (StringRef expression : {"(d, ())", "(d, true)", "[d, ()]"})
    cases.run("mixed source category " + expression, [&] {
      auto result =
          check("view def bad(d: Finite<index>) -> Finite<index>:\n    bad = " +
                expression.str() + "\n    return d\n");
      require(!result, "mixed aggregate accepted");
      consumeError(result.takeError());
    });
  cases.run("ordinary Body consumes selected structural result", [] {
    accepted(R"(
def fold<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: fn(S, item: I) -> S where item_from(item, rows)) -> S = finite("math.fold")
view def pack(d: Finite<index>) -> ds::Product<Finite<index>, ds::Sequence<Finite<index>>>:
    return (d, ds::append([], d))
def count(lo: index, hi: index) -> index:
    selected = pack(range(lo, hi))
    return fold(selected.1[0], lo, fn(state, item) => state)
)");
  });
  cases.run("closure retains entered sibling guards and repeated calls", [] {
    auto project = take(check(guardSource));
    const auto &body = *named(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    Work work{defaultLimits};
    Semantics types(declarations, project.assets(), work);
    auto closed = closeDescriptor(types, declarations, body,
                                  body.descriptorBindings.size() - 1, {}, {});
    require(closed.has_value(),
            types.diagnostic ? types.diagnostic->message : "closure failed");
    require(closed->shape->nodes.size() == 4 && closed->shape->result == 0 &&
                closed->shape->nodes[2].kind == DescriptorBinding::Kind::Zip,
            "guard-only sibling, repeated assertion, or selected origin "
            "disappeared");
    require(checkDescriptorClosure(types, declarations, body,
                                   body.descriptorBindings.size() - 1, {}, {},
                                   *closed),
            types.diagnostic ? types.diagnostic->message
                             : "closure witness failed");
  });
  for (unsigned mutation = 0; mutation < 16; ++mutation)
    cases.run(
        "independent formation candidate mutation " + Twine(mutation), [&] {
          auto project = take(check(guardSource));
          const auto &body = *named(project, "m::example").body;
          std::vector<Declaration> declarations(project.declarations().begin(),
                                                project.declarations().end());
          Work work{defaultLimits};
          Semantics types(declarations, project.assets(), work);
          unsigned root = body.descriptorBindings.size() - 1;
          auto original =
              closeDescriptor(types, declarations, body, root, {}, {});
          require(original.has_value(), types.diagnostic
                                            ? types.diagnostic->message
                                            : "closure failed");
          auto candidate = *original;
          auto shape = std::make_shared<DescriptorShape>(*candidate.shape);
          auto arena = std::make_shared<DescriptorArena>(*shape->arena);
          candidate.shape = shape;
          shape->arena = arena;
          shape->identity = "candidate key is not authority";
          if (mutation == 1)
            shape->nodes.pop_back();
          if (mutation == 2)
            shape->result = 1;
          if (mutation == 3)
            shape->payload = (shape->payload + 1) % arena->payloads.size();
          if (mutation == 4)
            shape->formation = arena->blocks.size();
          if (mutation == 5)
            arena->leaves.front().axis = 1;
          if (mutation == 6)
            arena->leaves.front().parameter = 0;
          if (mutation == 7)
            arena->leaves.front().contract.type.arguments.clear();
          if (mutation == 8)
            arena->blocks.front().clear();
          if (mutation == 9)
            arena->blocks.front().front().authority += "changed route";
          if (mutation == 10)
            arena->blocks.front().front().invocation = 0;
          if (mutation == 11)
            arena->payloads.pop_back();
          if (mutation == 12)
            std::swap(candidate.operands[0], candidate.operands[2]);
          if (mutation == 13)
            shape->nodes[2].children.front().node = 2;
          if (mutation == 14)
            arena->blocks.push_back({});
          if (mutation == 15)
            arena->payloads.front().arguments.push_back(
                Type(Type::Kind::Boolean));
          Work witnessWork{defaultLimits};
          Semantics witness(declarations, project.assets(), witnessWork);
          bool valid = checkDescriptorClosure(witness, declarations, body, root,
                                              {}, {}, candidate);
          require(mutation == 0 ? valid : !valid,
                  mutation == 0 && witness.diagnostic
                      ? witness.diagnostic->message
                      : "candidate coverage mutation escaped");
        });
  for (unsigned count : {0u, 1u, 3u})
    cases.run("actual selected Fold closure " + Twine(count), [&] {
      auto project =
          take(check(R"(
module Build:
    pub view def step<I: nat>(context: ds::Product<Finite<index>>, state: ds::Sequence<Finite<index>>) -> ds::Sequence<Finite<index>>:
        return ds::append(state, context.0)
def example(a: index, b: index) -> index:
    sequence = ds::fold<Count=)" +
                     std::to_string(count) +
                     R"(>(member=Build::step, context=(range(a, b),), seed=[])
    return a
)"));
      const auto &body = *named(project, "m::example").body;
      std::vector<Declaration> declarations(project.declarations().begin(),
                                            project.declarations().end());
      Work work{defaultLimits};
      Semantics types(declarations, project.assets(), work);
      unsigned root = body.descriptorBindings.size() - 1;
      auto closed = closeDescriptor(types, declarations, body, root, {}, {});
      require(closed.has_value(), types.diagnostic ? types.diagnostic->message
                                                   : "Fold closure failed");
      const auto &shape = *closed->shape;
      const auto &payload = shape.arena->payloads[shape.payload];
      const auto *sequence = std::get_if<uint64_t>(&payload.value);
      require(sequence &&
                  (*sequence == UINT32_MAX
                       ? 0
                       : shape.arena->sequences[*sequence].length) == count,
              "Fold did not produce exactly the source Count frames");
      require(checkDescriptorClosure(types, declarations, body, root, {}, {},
                                     *closed),
              types.diagnostic ? types.diagnostic->message
                               : "Fold witness failed");
      for (unsigned mutation = 0; mutation < 6; ++mutation) {
        auto candidate = *closed;
        auto shape = std::make_shared<DescriptorShape>(*candidate.shape);
        auto arena = std::make_shared<DescriptorArena>(*shape->arena);
        candidate.shape = shape;
        shape->arena = arena;
        auto &driver =
            *std::find_if(arena->blocks.front().begin(),
                          arena->blocks.front().end(), [](const auto &event) {
                            return event.kind == DescriptorBinding::Kind::Fold;
                          });
        if (mutation == 0) {
          auto &frames = arena->blocks[*driver.invocation];
          if (frames.empty())
            frames.push_back(driver);
          else
            frames.pop_back();
        }
        if (mutation == 1)
          std::swap(driver.children[0], driver.children[1]);
        if (mutation == 2)
          driver.invocation = shape->formation;
        if (mutation == 3)
          arena->payloads[driver.children[1]].contract.type.arguments.clear();
        if (mutation == 4)
          shape->payload = driver.children[0];
        if (mutation == 5) {
          auto &frames = arena->blocks[*driver.invocation];
          if (count > 1)
            frames[1].children[1] = frames[0].children[1];
          else
            driver.authority += "changed zero/one source selection";
        }
        Work witnessWork{defaultLimits};
        Semantics witness(declarations, project.assets(), witnessWork);
        require(!checkDescriptorClosure(witness, declarations, body, root, {},
                                        {}, candidate),
                "Fold frame/context/seed/prior-state mutation escaped");
      }
    });
  for (unsigned outer : {0u, 3u})
    cases.run("nested selected Fold actual old state " + Twine(outer), [&] {
      auto project =
          take(check(R"(
module Inner:
    pub view def step<I: nat>(context: ds::Product<Finite<index>>, state: ds::Sequence<Finite<index>>) -> ds::Sequence<Finite<index>>:
        return ds::append(state, context.0)
module Outer:
    pub view def step<J: nat>(context: ds::Product<Finite<index>>, state: ds::Sequence<Finite<index>>) -> ds::Sequence<Finite<index>>:
        return ds::fold<Count=2>(member=Inner::step, context=context, seed=state)
def example(a: index, b: index) -> index:
    sequence = ds::fold<Count=)" +
                     std::to_string(outer) +
                     R"(>(member=Outer::step, context=(range(a, b),), seed=[])
    return a
)"));
      const auto &body = *named(project, "m::example").body;
      std::vector<Declaration> declarations(project.declarations().begin(),
                                            project.declarations().end());
      Work work{defaultLimits};
      Semantics types(declarations, project.assets(), work);
      unsigned root = body.descriptorBindings.size() - 1;
      auto closed = closeDescriptor(types, declarations, body, root, {}, {});
      require(closed.has_value(), types.diagnostic ? types.diagnostic->message
                                                   : "nested closure failed");
      auto sequence = std::get<uint64_t>(
          closed->shape->arena->payloads[closed->shape->payload].value);
      require((sequence == UINT32_MAX
                   ? 0
                   : closed->shape->arena->sequences[sequence].length) ==
                  outer * 2,
              "nested Fold used stale or sequentially overwritten state");
      require(checkDescriptorClosure(types, declarations, body, root, {}, {},
                                     *closed),
              types.diagnostic ? types.diagnostic->message
                               : "nested witness failed");
    });
  cases.run("selected abstract interface route closes at zero", [] {
    auto project = take(check(R"(
interface Step:
    view def step<I: nat>(context: ds::Product<>, state: ds::Product<>) -> ds::Product<>
module Provider: Step:
    view def step<J: nat>(context: ds::Product<>, state: ds::Product<>) -> ds::Product<>:
        return state
view def selected<M: Step>() -> ds::Product<>:
    return ds::fold<Count=0>(member=M::step, context=(), seed=())
def example(a: index) -> index:
    result = selected<Provider>()
    return a
)"));
    if (auto error = checkScopedElaboration(project))
      throw std::runtime_error(toString(std::move(error)));
    const auto &body = *named(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    Work work{defaultLimits};
    Semantics types(declarations, project.assets(), work);
    auto closed = closeDescriptor(types, declarations, body,
                                  body.descriptorBindings.size() - 1, {}, {});
    require(closed.has_value(), types.diagnostic
                                    ? types.diagnostic->message
                                    : "abstract zero closure failed");
    require(checkDescriptorClosure(types, declarations, body,
                                   body.descriptorBindings.size() - 1, {}, {},
                                   *closed),
            types.diagnostic ? types.diagnostic->message
                             : "abstract zero witness failed");
  });
  cases.run("conformance cannot invent an iteration premise", [] {
    auto project = check(R"(
interface Step<N: nat>:
    view def step<I: nat>(context: ds::Product<>, state: ds::Product<>) -> ds::Product<>
module Invalid<N: nat>: Step<N>:
    view def step<I: nat>(context: ds::Product<>, state: ds::Product<>) -> ds::Product<> where I + 1 <= N:
        return state
)");
    require(!project,
            "implementation invented a Fold premise at interface conformance");
    consumeError(project.takeError());
  });
  cases.run("zero selection rejects independent closed extent failure", [] {
    auto project = check(R"(
module Bad:
    pub view def step<I: nat>(context: ds::Product<>, state: ds::Sequence<ds::Product<>>) -> ds::Sequence<ds::Product<>>:
        invalid: ds::Sequence<ds::Product<>, 1> = ds::sized<Length=1>([])
        return state
def example(a: index) -> index:
    sequence = ds::fold<Count=0>(member=Bad::step, context=(), seed=[])
    return a
)");
    require(!project, "zero Fold hid an independent invalid selection");
    consumeError(project.takeError());
  });
  cases.run(
      "thousands of entries use source work rather than expression depth", [] {
        std::string entries;
        for (unsigned i = 0; i < 2048; ++i) {
          if (i)
            entries += ",";
          entries += "d";
        }
        auto project = take(
            check("view def long_list(d: Finite<index>) -> "
                  "ds::Sequence<Finite<index>, 2048>:\n    return [" +
                  entries +
                  "]\ndef example(a: index, b: index) -> index:\n    values = "
                  "long_list(range(a, b))\n    return a\n"));
        auto error = checkScopedElaboration(project);
        if (error)
          throw std::runtime_error(toString(std::move(error)));
        const auto &body = *named(project, "m::example").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        Work work{defaultLimits};
        Semantics types(declarations, project.assets(), work);
        unsigned root = body.descriptorBindings.size() - 1;
        auto closed = closeDescriptor(types, declarations, body, root, {}, {});
        require(closed.has_value(), types.diagnostic ? types.diagnostic->message
                                                     : "long closure failed");
        const auto &shape = *closed->shape;
        auto sequence =
            std::get<uint64_t>(shape.arena->payloads[shape.payload].value);
        require(shape.arena->sequences[sequence].length == 2048 &&
                    shape.nodes.empty(),
                "generic sequence inherited the native Finite cap");
        require(checkDescriptorClosure(types, declarations, body, root, {}, {},
                                       *closed),
                types.diagnostic ? types.diagnostic->message
                                 : "long closure witness failed");
      });
  for (unsigned mutation = 0; mutation < 9; ++mutation)
    cases.run("immutable source coverage mutation " + Twine(mutation), [&] {
      auto project = take(check(guardSource));
      auto &definition = const_cast<DescriptorDefinition &>(
          *named(project, "m::guarded").descriptorDefinition);
      if (mutation == 0)
        definition.statements.pop_back();
      if (mutation == 1)
        std::reverse(definition.statements.begin(),
                     definition.statements.end());
      if (mutation == 2)
        definition.result = 0;
      if (mutation == 3)
        definition.bindings.back().parameter = 0;
      if (mutation == 4)
        definition.bindings.back().contract.type.arguments.clear();
      if (mutation == 5)
        definition.bindings.front().operands.front() = ValueId{3};
      if (mutation == 6)
        definition.bindings.back().expression =
            definition.bindings.front().expression;
      if (mutation == 7)
        definition.bindings.back().children.front().node = definition.result;
      if (mutation == 8)
        ++definition.bindings.back().span.begin;
      auto error = checkScopedElaboration(project);
      require(bool(error), "candidate recipe defined its own source universe");
      consumeError(std::move(error));
    });
  for (StringRef expression : {"[(d, ()), p]", "[p, (d, ())]"})
    cases.run("nested rigid aggregate evidence " + expression, [&] {
      accepted(
          "view def nested(d: Finite<index>, p: ds::Product<Finite<index>, "
          "ds::Product<>>) -> ds::Sequence<ds::Product<Finite<index>, "
          "ds::Product<>>, 2>:\n    values = " +
          expression.str() + "\n    return values\n");
    });
  for (StringRef source :
       {"def example(a: index) -> index:\n    u = ()\n    d: ds::Product<> = "
        "u\n    return a\n",
        "view def data_unit() -> ():\n    return ()\nview def invalid() -> "
        "ds::Product<>:\n    return data_unit()\n",
        "view def invalid(xs: ds::Sequence<Finite<index>, 2>) -> "
        "ds::Sequence<Finite<index>>:\n    return xs\n",
        "view def invalid(d: Finite<index>) -> Finite<index>:\n    xs = [[], "
        "[d]]\n    return d\n",
        "view def invalid(d: Finite<index>) -> Finite<index>:\n    xs = [d]\n  "
        "  return xs.0\n",
        "view def invalid(d: Finite<index>) -> Finite<index>:\n    p = (d,)\n  "
        "  return p[0]\n"})
    cases.run("strict source category and extent refusal " + source, [&] {
      auto project = check(source);
      require(!project, "fixed source category or extent was weakened");
      consumeError(project.takeError());
    });
  for (StringRef bound : {"I <= N", "I + K + 1 <= N + K", "I <= I + K"})
    cases.run("selected normalized one premise implication " + bound, [&] {
      accepted(
          "module Build<N: nat, K: nat>:\n    pub view def step<I: "
          "nat>(context: ds::Product<>, state: ds::Product<>) -> ds::Product<> "
          "where " +
          bound.str() +
          ":\n        return state\nview def generated() -> ds::Product<>:\n   "
          " return ds::fold<Count=0>(member=Build::step<N=0, K=5>, context=(), "
          "seed=())\n");
    });
  for (StringRef bound : {"1 <= N", "I + 1 <= I + N", "0 * I + 1 <= N"})
    cases.run("independent positivity refuses zero " + bound, [&] {
      auto project = check(
          "module Build<N: nat>:\n    pub view def step<I: nat>(context: "
          "ds::Product<>, state: ds::Product<>) -> ds::Product<> where " +
          bound.str() +
          ":\n        return state\nview def generated() -> ds::Product<>:\n   "
          " return ds::fold<Count=0>(member=Build::step<N=0>, context=(), "
          "seed=())\n");
      require(!project, "public independent positivity escaped at zero");
      consumeError(project.takeError());
    });
  cases.run(
      "ordinary source static observation borrows contracts and isolates "
      "writes",
      [] {
        std::string tuple;
        for (unsigned i = 0; i < 256; ++i)
          tuple += i ? ", bool" : "bool";
        auto project = take(
            check("type Packet = (" + tuple +
                  ")\ndef ordinary(x: Packet) -> bool:\n    return true\n"));
        const auto &storage = DeclarationAccess::storage(project);
        const auto &owner = named(project, "m::ordinary");
        CheckedStorage scratch(storage.capture, "");
        Work work{defaultLimits};
        auto reader = take(
            Checker::observe(scratch, storage, work, SourceAccess{owner.id}));
        require(&reader->declarations == &storage.declarations &&
                    scratch.declarations.empty() && scratch.assets.empty() &&
                    !reader->types.inferCapability &&
                    !reader->types.inferNatural &&
                    !reader->types.recordAdmission &&
                    !reader->types.completeDispatchBody,
                "observation copied metadata or installed mutation hooks");
        auto selected = reader->callable(owner, "ordinary", owner.span, false);
        require(selected && selected->declaration.index == owner.id.index,
                "ordinary static route observation failed");
        const auto *children = owner.inputs.front().type.arguments.data();
        SyntaxType term;
        term.name = "bool";
        term.span = owner.span;
        auto result = reader->type(owner, term);
        term.name = "Packet";
        auto placed = reader->placedType(owner, term);
        require(result && result->kind == Type::Kind::Boolean && placed &&
                    placed->type.arguments.size() == 256 &&
                    owner.inputs.front().type.arguments.data() == children &&
                    owner.inputs.front().type.arguments.size() == 256 &&
                    scratch.declarations.empty() &&
                    scratch.api.references.empty(),
                "static query mutated the candidate or retained a signature "
                "snapshot");
        // Queried values own their result, while the synchronous reader borrows
        // candidate metadata only for this scope.
        reader.reset();
        require(result->kind == Type::Kind::Boolean &&
                    placed->type.arguments.size() == 256 &&
                    llvm::all_of(placed->type.arguments,
                                 [](const Type &type) {
                                   return type.kind == Type::Kind::Boolean;
                                 }),
                "owned recursive query result depended on reader lifetime");
        for (bool cancel : {false, true}) {
          CheckedStorage refusedScratch(storage.capture, "");
          Work bounded{defaultLimits};
          uint64_t allowance = 1;
          bounded.allowance = &allowance;
          if (cancel) {
            bounded.cancellation.emplace();
            bounded.cancellation->cancel();
          }
          auto refused = Checker::observe(refusedScratch, storage, bounded,
                                          SourceAccess{owner.id});
          require(!refused, "bounded observation published a reader");
          auto diagnostic = diagnose(refused.takeError());
          require(
              diagnostic &&
                  diagnostic->code ==
                      (cancel ? "source.cancelled" : "source.limit") &&
                  refusedScratch.declarations.empty() &&
                  !refusedScratch.declarationIndex,
              "observation did work before its allowance/cancellation check");
        }
      });
  cases.run(
      "inherited structural storage is admitted and independently witnessed",
      [] {
        auto project = take(check(R"(
view def generated(a: index, b: index) -> ds::Sequence<Finite<index>, 1>:
    return [range(a, b)]
def seed(a: index, b: index) -> index:
    values = generated(a, b)
    return a
def forward(a: index, b: index, flag: bool, values: ds::Sequence<Finite<index>, 1>) -> index:
    selected = values[0]
    return a
)"));
        const auto &seedBody = *named(project, "m::seed").body;
        const auto &body = *named(project, "m::forward").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        Work seedWork{defaultLimits};
        Semantics seedTypes(declarations, project.assets(), seedWork);
        auto seed =
            closeDescriptor(seedTypes, declarations, seedBody,
                            seedBody.descriptorBindings.size() - 1, {}, {});
        require(seed.has_value(), seedTypes.diagnostic
                                      ? seedTypes.diagnostic->message
                                      : "seed missing");
        DescriptorEnvironment original{seed->shape, {{0}, {1}}};
        Work referenceWork{defaultLimits};
        Semantics referenceTypes(declarations, project.assets(), referenceWork);
        auto reference = closeDescriptor(referenceTypes, declarations, body, 0,
                                         {}, {original});
        require(reference.has_value(), referenceTypes.diagnostic
                                           ? referenceTypes.diagnostic->message
                                           : "inherited reference missing");
        for (unsigned mutation = 0; mutation < 10; ++mutation) {
          auto mutate = [&](DescriptorShape &shape, DescriptorArena &arena) {
            auto &selected = arena.payloads[shape.payload];
            if (mutation == 1)
              selected.value = uint64_t(UINT32_MAX);
            if (mutation == 2) {
              auto root = std::get<uint64_t>(selected.value);
              arena.sequences[root].elements[0] = shape.payload;
            }
            if (mutation == 3) {
              auto root = std::get<uint64_t>(selected.value);
              auto child = arena.sequences[root].elements[0];
              auto leaf = std::get<unsigned>(arena.payloads[child].value);
              arena.payloads[child].contract.type.arguments[0] =
                  Type(Type::Kind::Boolean);
              arena.leaves[leaf].contract = arena.payloads[child].contract;
            }
            if (mutation == 4) {
              Type product(Type::Kind::DescriptorProduct);
              product.arguments.push_back(Type(Type::Kind::DescriptorProduct));
              arena.payloads.push_back(
                  {DescriptorContract(std::move(product)),
                   std::vector<unsigned>{unsigned(arena.payloads.size())},
                   {}});
            }
            if (mutation == 5)
              selected.arguments.emplace_back(Type::Kind::Boolean);
            if (mutation >= 6) {
              auto root = std::get<uint64_t>(selected.value);
              auto child = arena.sequences[root].elements[0];
              auto &leaf =
                  arena.leaves[std::get<unsigned>(arena.payloads[child].value)];
              if (mutation == 6)
                leaf.operands.clear();
              if (mutation == 7)
                leaf.kind = DescriptorBinding::Kind::Parameter;
              if (mutation == 8) {
                shape.inputs.emplace_back(Type::Kind::Boolean);
                leaf.operands[0] = {unsigned(shape.inputs.size() - 1)};
              }
              if (mutation == 9)
                leaf.axis = 1;
            }
          };
          auto environment = original;
          auto sourceShape =
              std::make_shared<DescriptorShape>(*environment.shape);
          auto sourceArena =
              std::make_shared<DescriptorArena>(*sourceShape->arena);
          sourceShape->arena = sourceArena;
          mutate(*sourceShape, *sourceArena);
          environment.shape = sourceShape;
          if (mutation == 8)
            environment.operands.push_back({2});
          Work work{defaultLimits};
          Semantics types(declarations, project.assets(), work);
          auto result =
              closeDescriptor(types, declarations, body, 0, {}, {environment});
          require(mutation == 0 ? result.has_value() : !result,
                  "inherited storage mutation escaped admission");
          auto candidate = *reference;
          auto shape = std::make_shared<DescriptorShape>(*candidate.shape);
          auto arena = std::make_shared<DescriptorArena>(*shape->arena);
          shape->arena = arena;
          mutate(*shape, *arena);
          candidate.shape = shape;
          Work witnessWork{defaultLimits};
          Semantics witness(declarations, project.assets(), witnessWork);
          bool valid = checkDescriptorClosure(witness, declarations, body, 0,
                                              {}, {environment}, candidate);
          require(
              mutation == 0 ? valid : !valid,
              "self-consistent invalid inherited storage escaped witnessing");
        }
        for (bool cancelled : {false, true}) {
          Work work{defaultLimits};
          uint64_t allowance = 1;
          work.allowance = &allowance;
          if (cancelled) {
            work.cancellation.emplace();
            work.cancellation->cancel();
          }
          Semantics types(declarations, project.assets(), work);
          require(
              !checkClosedDescriptorStorage(types, *seed->shape, {},
                                            "source.domain-witness") &&
                  types.diagnostic &&
                  types.diagnostic->code ==
                      (cancelled ? "source.cancelled" : "source.limit"),
              "closed storage scratch preceded its budget/cancellation check");
        }
      });
  cases.run("inherited sequence keeps valid historical sharing", [] {
    auto project = take(check(R"(
view def product<A: Type + Copy + Drop, B: Type + Copy + Drop>(a: Finite<A>, b: Finite<B>) -> Finite<(A, B)> = domain("product")
view def generated(a: index, b: index) -> ds::Sequence<Finite<index>, 2>:
    one = [range(a, b)]
    twice = ds::concat(ds::unsized(one), ds::unsized(one))
    discarded = ds::replace<Index=1>(twice, range(b, a))
    paired = product(range(a, b), range(b, a))
    return ds::sized<Length=2>(twice)
def seed(a: index, b: index) -> index:
    values = generated(a, b)
    return a
def forward(a: index, b: index, values: ds::Sequence<Finite<index>, 2>) -> index:
    selected = values[0]
    return a
)"));
    const auto &seedBody = *named(project, "m::seed").body;
    const auto &body = *named(project, "m::forward").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    Work work{defaultLimits};
    Semantics types(declarations, project.assets(), work);
    auto seed = closeDescriptor(types, declarations, seedBody,
                                seedBody.descriptorBindings.size() - 1, {}, {});
    require(seed && seed->shape->arena->sequences.size() > 1 &&
                seed->shape->arena->leaves.size() >= 3,
            types.diagnostic ? types.diagnostic->message
                             : "historical storage missing");
    DescriptorEnvironment environment{seed->shape, {{0}, {1}}};
    auto closed =
        closeDescriptor(types, declarations, body, 0, {}, {environment});
    require(closed && checkDescriptorClosure(types, declarations, body, 0, {},
                                             {environment}, *closed),
            types.diagnostic ? types.diagnostic->message
                             : "valid historical sharing was refused");
    for (unsigned metadata = 0; metadata < 4; ++metadata) {
      auto mutate = [metadata](DescriptorArena &arena) {
        auto pair = llvm::find_if(arena.leaves, [](const auto &leaf) {
          return leaf.kind == DescriptorBinding::Kind::Product;
        });
        require(pair != arena.leaves.end(), "historical Product missing");
        unsigned index = pair - arena.leaves.begin();
        auto &head = pair->contract.type.arguments.front();
        switch (metadata) {
        case 0:
          head.domain = "foreign-tuple";
          break;
        case 1:
          head.sort = "foreign-sort";
          break;
        case 2:
          head.dimension = Natural(1);
          break;
        case 3:
          head.symbolic = true;
          break;
        }
        for (auto &payload : arena.payloads)
          if (auto *leaf = std::get_if<unsigned>(&payload.value);
              leaf && *leaf == index)
            payload.contract = pair->contract;
      };
      auto sourceShape = std::make_shared<DescriptorShape>(*seed->shape);
      auto sourceArena = std::make_shared<DescriptorArena>(*sourceShape->arena);
      sourceShape->arena = sourceArena;
      mutate(*sourceArena);
      environment.shape = sourceShape;
      Work invalidWork{defaultLimits};
      Semantics invalid(declarations, project.assets(), invalidWork);
      require(
          !closeDescriptor(invalid, declarations, body, 0, {}, {environment}),
          "historical Product accepted foreign Tuple root metadata");
      auto candidate = *closed;
      auto shape = std::make_shared<DescriptorShape>(*candidate.shape);
      auto arena = std::make_shared<DescriptorArena>(*shape->arena);
      shape->arena = arena;
      mutate(*arena);
      candidate.shape = shape;
      Work replayWork{defaultLimits};
      Semantics replay(declarations, project.assets(), replayWork);
      require(!checkDescriptorClosure(replay, declarations, body, 0, {},
                                      {environment}, candidate),
              "matching historical Tuple metadata forgery passed witness");
    }
  });
  for (unsigned count : {0u, 1u})
    cases.run("wide ordinary-source Fold closure " + Twine(count), [&] {
      std::string tuple, value;
      for (unsigned i = 0; i < 64; ++i) {
        tuple += i ? ", index" : "index";
        value += i ? ", a" : "a";
      }
      auto project = take(check(
          "view def array<T: Type + Copy + Drop, N: nat>(xs: [T; N]) -> "
          "Finite<T> = domain(\"source_array\")\n"
          "module Wide:\n    pub view def step<I: nat>(context: "
          "ds::Product<Finite<(" +
          tuple +
          ")>>, state: ds::Product<>) -> ds::Product<>:\n        return state\n"
          "def example(a: index) -> index:\n    input = array([(" +
          value + ")])\n    folded = ds::fold<Count=" + std::to_string(count) +
          ">(member=Wide::step, context=(input,), seed=())\n    return a\n"));
      const auto &body = *named(project, "m::example").body;
      std::vector<Declaration> declarations(project.declarations().begin(),
                                            project.declarations().end());
      Work work{defaultLimits};
      Semantics types(declarations, project.assets(), work);
      auto root = body.descriptorBindings.size() - 1;
      auto closed = closeDescriptor(types, declarations, body, root, {}, {});
      require(closed.has_value(), types.diagnostic
                                      ? types.diagnostic->message
                                      : "wide Fold closure failed");
      auto closureCost = work.used;
      Work witnessWork{defaultLimits};
      Semantics witness(declarations, project.assets(), witnessWork);
      require(checkDescriptorClosure(witness, declarations, body, root, {}, {},
                                     *closed),
              witness.diagnostic ? witness.diagnostic->message
                                 : "wide Fold witness failed");
      auto witnessCost = witnessWork.used;
      errs() << "ordinary Fold Count=" << count
             << " closure work=" << closureCost
             << " witness work=" << witnessCost << '\n';
      for (bool replay : {false, true}) {
        const auto cost = replay ? witnessCost : closureCost;
        require(cost > 1, "ordinary Fold work receipt missing");
        for (unsigned control = 0; control < 3; ++control) {
          Work bounded{defaultLimits};
          uint64_t remaining = cost - (control == 0);
          bounded.allowance = &remaining;
          if (control == 2) {
            bounded.cancellation.emplace();
            bounded.cancellation->cancel();
          }
          Semantics observed(declarations, project.assets(), bounded);
          bool valid =
              replay
                  ? checkDescriptorClosure(observed, declarations, body, root,
                                           {}, {}, *closed)
                  : closeDescriptor(observed, declarations, body, root, {}, {})
                        .has_value();
          require(valid == (control == 1),
                  "ordinary Fold budget/cancellation boundary changed");
          if (!valid)
            require(
                observed.diagnostic &&
                    observed.diagnostic->code ==
                        (control == 2 ? "source.cancelled" : "source.limit"),
                "ordinary Fold refusal lost its owning diagnostic");
        }
      }
    });
  cases.run("wide Fold frame scratch is charged before ownership", [] {
    Type item(Type::Kind::Tuple);
    for (unsigned i = 0; i < 128; ++i)
      item.arguments.emplace_back(Type::Kind::Boolean);
    Type finite(Type::Kind::Descriptor);
    finite.arguments.push_back(std::move(item));
    Type context(Type::Kind::DescriptorProduct);
    context.arguments.push_back(std::move(finite));
    DescriptorContract k(std::move(context));
    DescriptorContract a{Type(Type::Kind::DescriptorProduct)};
    std::vector<Declaration> declarations;
    for (bool cancelled : {false, true}) {
      Work work{defaultLimits};
      uint64_t allowance = sizeof(std::vector<DescriptorBinding>) +
                           2 * sizeof(DescriptorBinding) + 2 * sizeof(void *);
      work.allowance = &allowance;
      if (cancelled) {
        work.cancellation.emplace();
        work.cancellation->cancel();
      }
      Semantics types(declarations, {}, work);
      require(!descriptorFrameParameters(types, k, a, {}) && types.diagnostic &&
                  types.diagnostic->code ==
                      (cancelled ? "source.cancelled" : "source.limit"),
              "wide frame contract copy escaped precharge");
    }
    Work work{defaultLimits};
    Semantics types(declarations, {}, work);
    auto frame = descriptorFrameParameters(types, k, a, {});
    require(frame && frame->size() == 2 && frame->front().contract == k &&
                frame->back().contract == a,
            "precharged Fold frame changed its contracts");
  });
  cases.run("retained pattern results precharge recursive copies", [] {
    Limits limits;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    DescriptorPatterns patterns(types, {}, 1, {});
    Type value(Type::Kind::DescriptorProduct);
    for (unsigned i = 0; i < 64; ++i)
      value.arguments.emplace_back(Type::Kind::DescriptorProduct);
    auto variable = std::make_shared<const zkc::protocol::ContractPattern>(
        zkc::protocol::ContractPattern{zkc::protocol::ContractVariable{0}});
    require(patterns.match(variable, value), "pattern setup failed");
    work.used = limits.work - 1;
    require(!patterns.instantiate(variable) && types.diagnostic &&
                types.diagnostic->code == "source.limit",
            "retained recursive pattern result escaped its copy allowance");
  });
  cases.run("long Natural identities pay before domination comparison", [] {
    Limits limits;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    auto atom = take(Natural::atom(std::string(4096, 'n')));
    work.used = limits.work - 64;
    auto result = types.naturals.dominatedBy(atom, atom);
    require(!result, "factor identity comparison escaped work allowance");
    consumeError(result.takeError());
  });
  cases.run("cancelled closure does not publish a partial arena", [] {
    auto project = take(check(guardSource));
    const auto &body = *named(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    Work work{defaultLimits};
    Semantics types(declarations, project.assets(), work);
    work.cancellation.emplace();
    work.cancellation->cancel();
    auto closed = closeDescriptor(types, declarations, body,
                                  body.descriptorBindings.size() - 1, {}, {});
    require(!closed && types.diagnostic,
            "cancelled closure published a result");
  });
  cases.run("closed arena outlives its source and checker", [] {
    std::shared_ptr<const DescriptorShape> retained;
    {
      auto project = take(check(guardSource));
      const auto &body = *named(project, "m::example").body;
      std::vector<Declaration> declarations(project.declarations().begin(),
                                            project.declarations().end());
      Work work{defaultLimits};
      Semantics types(declarations, project.assets(), work);
      auto closed = closeDescriptor(types, declarations, body,
                                    body.descriptorBindings.size() - 1, {}, {});
      require(closed.has_value(), "closure setup failed");
      retained = closed->shape;
    }
    require(retained->arena && retained->nodes.size() == 4 &&
                retained->arena->leaves.size() == 3 &&
                !retained->identity.empty(),
            "immutable arena retained source or checker lifetime dependencies");
  });
  cases.run("persistent sequence retained roots and lifetime", [] {
    Limits limits;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    std::deque<DescriptorSequenceNode> storage;
    DescriptorSequence sequences(types, storage);
    auto root = DescriptorSequence::empty;
    std::vector<DescriptorSequence::Root> history;
    for (unsigned i = 0; i < 4096; ++i) {
      auto leaf = sequences.singleton(i, {});
      auto next = leaf ? sequences.concat(root, *leaf, {}) : std::nullopt;
      require(next.has_value(), types.diagnostic ? types.diagnostic->message
                                                 : "sequence append failed");
      root = *next;
      if (!(i % 257))
        history.push_back(root);
    }
    auto original = root;
    for (unsigned i = 0; i < 4096; i += 127) {
      auto next = sequences.replace(root, i, 8192 + i, {});
      require(next.has_value(), "sequence replacement failed");
      root = *next;
      require(sequences.at(original, i, {}) == i,
              "retained sequence root changed");
      require(sequences.at(root, i, {}) == 8192 + i,
              "replacement lost its position");
    }
    for (unsigned i = 0; i < history.size(); ++i)
      require(sequences.size(history[i]) == 1 + i * 257 &&
                  sequences.at(history[i], i * 257, {}) == i * 257,
              "historical root lost its arena-owned payload");
    require(storage.size() < 4096 * 16,
            "persistent storage growth is not bounded");
  });
  return cases.result();
}
