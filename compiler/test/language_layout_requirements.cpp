#include "../lib/Language/FiniteContracts.h"
#include "../lib/Language/LayoutReader.h"
#include "../lib/Language/Semantics.h"
#include "../lib/Language/SignatureWitness.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(domain F = field("bls12-381.fr")
type Vector = builtin("vector", F)
type Matrix = builtin("matrix", F)
type Array<N: nat> = builtin("field_array", F, N)
struct Row:
    pub values: Vector
)";
const StringLiteral projectedHeader =
    R"(def read(pair: (Row, index), ys: Vector) -> bool where (in_bounds(pair.1, pair.0.values), equal_extent(pair.0.values, ys)):
    return true
)";
Expected<CheckedProject> check(const Twine &source, Limits limits = {}) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured =
      capture({{"m", prelude + source.str(), "requirements.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == ("m::" + name).str())
      return const_cast<Declaration &>(decl);
  throw std::runtime_error("missing declaration " + name.str());
}
void valid(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refusesWitness(const CheckedProject &project) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "candidate data header was accepted");
  const auto message = toString(std::move(error));
  require(namesIdentifier(message, "source.scoped-witness"),
          "unexpected data header refusal: " + message);
}
} // namespace
int main() {
  Cases cases;
  for (StringRef clause :
       {"()", "equal_extent(xs, ys)", "(equal_extent(xs, ys))",
        "(equal_extent(xs, ys),)", "(equal_extent(xs, ys), in_bounds(i, xs))"})
    cases.run("accepted where expression: " + clause, [&] {
      take(check("def same(xs: Vector, ys: Vector, i: index) -> bool where " +
                 clause + ":\n    return true\n"));
    });
  cases.run("mixed requirements retain their distinct owners", [] {
    auto project = take(check(R"(use zkc::transport::{NativeMessage}
def mixed<T: Type, E: Field, N: nat, M: nat>(xs: Vector, ys: Vector) -> bool where (Copy(T), Drop(T), N <= M, NativeMessage(T), zkc::algebra::TwoAdicField(E), equal_extent(xs, ys)):
    return true
)"));
    const auto &decl = named(project, "mixed");
    require(decl.dataPreconditions.size() == 1 &&
                decl.consumerRequirements.size() == 1 &&
                decl.capabilityBounds.size() == 1 && !decl.bounds.empty() &&
                decl.parameters.front().permissions.copy,
            "mixed requirement categories were conflated");
    valid(checkScopedElaboration(project));
  });
  cases.run(
      "tuple and record selector spans and paths survive written export", [] {
        auto project = take(check(
            R"(def read(pair: (Row, index), ys: Vector) -> bool where (in_bounds(pair.1, pair.0.values), equal_extent(pair.0.values, ys)):
    return true
)"));
        const auto &conditions = named(project, "read").dataPreconditions;
        require(conditions.size() == 2 && conditions[0].left.port == 0 &&
                    conditions[0].left.path == std::vector<unsigned>{1} &&
                    conditions[0].right.path == std::vector<unsigned>({0, 0}),
                "logical selectors were not resolved by input position");
        auto written = take(json::parse(take(inspectWrittenSource(project))));
        unsigned selectors = 0, requirements = 0;
        for (const auto &owner :
             *written.getAsObject()->getArray("declarations"))
          if (owner.getAsObject()->getString("owner") == "m::read")
            for (const auto &node : *owner.getAsObject()->getArray("nodes")) {
              const auto &record = *node.getAsObject();
              if (record.getString("kind") == "input_selector") {
                ++selectors;
                require(record.getString("port").has_value(),
                        "missing selector port");
                auto location = record.getObject("span");
                require(location && record.getArray("path") &&
                            record.getArray("fields"),
                        "selector lost its source identity or fields");
                const auto begin = *location->getInteger("begin");
                const auto end = *location->getInteger("end");
                auto bytes =
                    StringRef(project.sources().front().text).slice(begin, end);
                require(bytes == "pair.1" || bytes == "pair.0.values" ||
                            bytes == "ys",
                        "selector span does not cover its written path");
                if (bytes == "pair.0.values") {
                  const auto &fields = *record.getArray("fields");
                  require(fields.size() == 2 &&
                              fields[0].getAsString() == "0" &&
                              fields[1].getAsString() == "values",
                          "tuple/record path spelling changed during export");
                }
              }
              if (record.getString("kind") == "requirement") {
                ++requirements;
                require(record.getString("capability") == "" &&
                            record.getString("data").has_value(),
                        "data requirement exported as a capability");
              }
            }
        require(selectors == 4 && requirements == 2,
                "written requirement nodes lost");
        require(take(inspectWrittenSource(project)) ==
                    take(inspectWrittenSource(project)),
                "written node identities changed on repeated inspection");
        valid(checkScopedElaboration(project));
        const auto authenticated = named(project, "read").dataPreconditions;
        const auto originalWritten = take(inspectWrittenSource(project));
        named(project, "read").dataPreconditions[0].right.path = {};
        require(take(inspectWrittenSource(project)) == originalWritten,
                "candidate header changed the immutable written requirements");
        namespace detail = zkc::language::detail;
        Limits limits;
        detail::Work work{limits};
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        detail::Semantics semantics(declarations, {}, work);
        const auto &helper = named(project, "read");
        auto replayed =
            detail::deriveDataPreconditions(semantics, declarations, helper,
                                            *helper.body, authenticated, false);
        require(replayed && *replayed == authenticated,
                "candidate annotations replaced authenticated replay seeds");
      });
  cases.run("matrix axes use existing semantic validation", [] {
    auto project = take(check(
        R"(def axes(xs: Matrix, ys: Matrix, i: index) -> bool where (in_bounds(i, xs, 1), equal_extent(xs, ys, 1, 0)):
    return true
)"));
    const auto &conditions = named(project, "axes").dataPreconditions;
    require(conditions[0].rightAxis == 1 && conditions[1].leftAxis == 1 &&
                conditions[1].rightAxis == 0,
            "axes were not retained");
  });
  for (StringRef mutation :
       {"erase all",      "erase first",   "inject",       "duplicate",
        "order",          "kind",          "left input",   "right input",
        "left path",      "right path",    "left axis",    "right axis",
        "premise source", "premise begin", "premise end",  "left source",
        "left begin",     "left end",      "right source", "right begin",
        "right end"})
    cases.run("unused projected header rejects " + mutation, [&] {
      auto project = take(check(projectedHeader));
      valid(checkScopedElaboration(project));
      const auto written = take(inspectWrittenSource(project));
      auto &conditions = named(project, "read").dataPreconditions;
      auto &first = conditions.front();
      if (mutation == "erase all")
        conditions.clear();
      else if (mutation == "erase first")
        conditions.erase(conditions.begin());
      else if (mutation == "inject") {
        auto extra = conditions.back();
        std::swap(extra.left, extra.right);
        conditions.push_back(std::move(extra));
      } else if (mutation == "duplicate")
        conditions.push_back(first);
      else if (mutation == "order")
        std::swap(conditions[0], conditions[1]);
      else if (mutation == "kind")
        first.kind = DataPrecondition::Kind::EqualExtent;
      else if (mutation == "left input")
        first.left.port = 1;
      else if (mutation == "right input")
        conditions.back().right.port = 0;
      else if (mutation == "left path")
        first.left.path.clear();
      else if (mutation == "right path")
        first.right.path.clear();
      else if (mutation == "left axis")
        first.leftAxis = 1;
      else if (mutation == "right axis")
        first.rightAxis = 1;
      else {
        Span &span = mutation.starts_with("left")    ? first.left.span
                     : mutation.starts_with("right") ? first.right.span
                                                     : first.span;
        if (mutation.ends_with("source"))
          ++span.source.index;
        else if (mutation.ends_with("begin"))
          ++span.begin;
        else
          --span.end;
      }
      require(take(inspectWrittenSource(project)) == written,
              "candidate mutation changed immutable authored syntax");
      refusesWitness(project);
    });
  cases.run("header with no authored clauses rejects premise injection", [] {
    auto project = take(check(R"(def unused(xs: Vector, ys: Vector) -> bool:
    return true
)"));
    valid(checkScopedElaboration(project));
    auto &decl = named(project, "unused");
    require(decl.dataPreconditions.empty(), "original has a data premise");
    decl.dataPreconditions.push_back({DataPrecondition::Kind::EqualExtent,
                                      {0, {}, decl.inputs[0].span},
                                      {1, {}, decl.inputs[1].span},
                                      0,
                                      0,
                                      decl.span});
    refusesWitness(project);
  });
  cases.run("generated owner cannot acquire an authored data premise", [] {
    auto project = take(check(R"(pub protocol Run roles(P)() -> bool @P:
    return true
)"));
    valid(checkScopedElaboration(project));
    bool injected = false;
    for (const auto &decl : project.declarations()) {
      if (!decl.generated)
        continue;
      const_cast<Declaration &>(decl).dataPreconditions.push_back(
          {DataPrecondition::Kind::EqualExtent,
           {0, {}, decl.span},
           {0, {}, decl.span},
           0,
           0,
           decl.span});
      injected = true;
      break;
    }
    require(injected, "missing generated owner control");
    refusesWitness(project);
  });
  cases.run("unused generic helper authenticates data beside mixed clauses",
            [] {
              auto project = take(check(R"(use zkc::transport::{NativeMessage}
def mixed<T: Type, E: Field, N: nat, M: nat>(pair: (Row, index), ys: Vector) -> bool where (Copy(T), Drop(T), N <= M, NativeMessage(T), zkc::algebra::TwoAdicField(E), in_bounds(pair.1, pair.0.values), equal_extent(pair.0.values, ys)):
    return true
)"));
              valid(checkScopedElaboration(project));
              auto &decl = named(project, "mixed");
              require(decl.parameters.size() == 4 && !decl.bounds.empty() &&
                          decl.parameters[0].permissions.copy &&
                          decl.capabilityBounds.size() == 1 &&
                          decl.consumerRequirements.size() == 1 &&
                          decl.dataPreconditions.size() == 2,
                      "missing independent mixed contract controls");
              decl.dataPreconditions.clear();
              refusesWitness(project);
            });
  cases.run(
      "unused abstract generic helper authenticates projected premises", [] {
        auto project = take(check(R"(interface Reader<N: nat>:
    def read(pair: (Row, index), ys: Array<N>) -> bool where (in_bounds(pair.1, pair.0.values), equal_extent(pair.0.values, ys))
)"));
        auto &decl = named(project, "Reader::read");
        require(decl.abstract && !decl.body && decl.parameters.size() == 1 &&
                    decl.dataPreconditions.size() == 2,
                "abstract helper was not retained");
        valid(checkScopedElaboration(project));
        decl.dataPreconditions[0].right.path.clear();
        refusesWitness(project);
      });
  cases.run("valid matrix axes cannot replace authored axes", [] {
    auto project = take(check(
        R"(def axes(xs: Matrix, ys: Matrix) -> bool where equal_extent(xs, ys, 1, 0):
    return true
)"));
    valid(checkScopedElaboration(project));
    named(project, "axes").dataPreconditions[0].leftAxis = 0;
    refusesWitness(project);
  });
  cases.run("same typed projection cannot replace an authored selector", [] {
    auto project = take(check(
        R"(def read(pair: (Row, Row), ys: Vector) -> bool where equal_extent(pair.0.values, ys):
    return true
)"));
    valid(checkScopedElaboration(project));
    named(project, "read").dataPreconditions[0].left.path[0] = 1;
    refusesWitness(project);
  });
  cases.run("selected statics retain inherited contracts and data headers", [] {
    auto project = take(check(R"(module Helpers<N: nat>:
    pub def same(xs: Array<N>, ys: Array<N>) -> bool where equal_extent(xs, ys):
        return true
pub protocol Run roles(P)(xs: Array<2> @P) -> bool @P:
    return Helpers<2>::same(xs, xs)
)"));
    valid(checkScopedElaboration(project));
    auto closed = take(closeNativeRun(project, "m::Run"));
    valid(checkScopedSpecialization(closed));
    take(prepareOriginal(closed));
    named(project, "Helpers::same").dataPreconditions.clear();
    refusesWitness(project);
  });
  cases.run("inherited mixed clauses stay separate from member data premises",
            [] {
              auto project = take(check(R"(use zkc::transport::{NativeMessage}
module Helpers<T: Type, E: Field, N: nat, M: nat> where (Copy(T), N <= M, NativeMessage(T), zkc::algebra::TwoAdicField(E)):
    def read(xs: Vector, ys: Vector) -> bool where equal_extent(xs, ys):
        return true
)"));
              const auto &owner = named(project, "Helpers");
              auto &member = named(project, "Helpers::read");
              require(owner.dataPreconditions.empty() &&
                          member.dataPreconditions.size() == 1 &&
                          member.parameters.size() == 4 &&
                          member.parameters[0].permissions.copy &&
                          !member.bounds.empty() &&
                          member.consumerRequirements.size() == 1 &&
                          member.capabilityBounds.size() == 1,
                      "member lost its inherited contract context");
              valid(checkScopedElaboration(project));
              member.dataPreconditions.clear();
              refusesWitness(project);
            });
  cases.run("header replay charges paths at exact and one-short budgets", [] {
    namespace detail = zkc::language::detail;
    auto project = take(check(projectedHeader));
    const auto &storage = detail::DeclarationAccess::storage(project);
    auto replay = [&](uint64_t allowance) {
      Limits limits;
      limits.work = allowance;
      detail::Work work{limits};
      auto result = detail::replayHeaderContracts(storage, work);
      const bool accepted = bool(result);
      if (!result)
        require(namesIdentifier(toString(result.takeError()), "source.limit"),
                "bounded header replay did not stop at work limit");
      require(work.used <= allowance, "header replay overspent its budget");
      return std::make_pair(work.used, accepted);
    };
    const auto baseline = replay(Limits{}.work);
    const auto cost = baseline.first;
    require(baseline.second && cost > 0, "original header did not replay");
    require(replay(cost) == baseline, "exact header replay budget changed");
    require(!replay(cost - 1).second, "one-short header replay succeeded");
    require(replay(cost) == baseline, "failed replay changed retry work");
    auto &path = named(project, "read").dataPreconditions[0].right.path;
    const auto original = path;
    // A changed path must exhaust this budget before it can be copied or
    // compared. An early semantic mismatch is not the work-limit control.
    path.resize(cost + 1, 0);
    require(!replay(cost).second, "candidate path escaped snapshot charging");
    path = original;
    require(replay(cost) == baseline, "restored path changed replay work");
    auto &conditions = named(project, "read").dataPreconditions;
    const auto authored = conditions;
    conditions.resize(cost + 1, conditions.front());
    require(!replay(cost).second,
            "candidate premises escaped snapshot charging");
    conditions = authored;
    require(replay(cost) == baseline, "restored premises changed replay work");
    outs() << "header replay exact_work=" << cost
           << " oversized_path=" << cost + 1 << '\n';
  });
  for (StringRef clause :
       {"in_bounds(i)",
        "in_bounds(i, xs, 0, 1)",
        "equal_extent(xs, ys, 0)",
        "equal_extent(xs, ys, 0, 1, 0)",
        "in_bounds(i, xs, 2)",
        "in_bounds(i, xs, -1)",
        "in_bounds(i, xs, true)",
        "in_bounds(i, xs, 0 + 0)",
        "in_bounds(i, xs, i)",
        "in_bounds(i, xs, 9999999999999999999999999999999999999999)",
        "in_bounds(i, xs, axis=0)",
        "equal_extent(left=xs, ys)",
        "equal_extent(xs: Vector, ys)",
        "equal_extent(xs=true, ys)",
        "in_bounds(i, xs, 1)",
        "equal_extent(xs, ys, 0, 1)",
        "in_bounds(xs, ys)",
        "equal_extent(i, xs)",
        "equal_extent(missing, ys)",
        "equal_extent(m::xs, ys)",
        "equal_extent(xs(), ys)",
        "equal_extent((xs), ys)",
        "equal_extent(xs[0], ys)",
        "equal_extent(xs + ys, ys)",
        "(equal_extent(xs, ys), equal_extent(xs, ys))"})
    cases.run("invalid data requirement: " + clause, [&] {
      refuses(check("def bad(xs: Vector, ys: Vector, i: index) -> bool where " +
                    clause + ":\n    return true\n"),
              "source.data-bound");
    });
  for (const auto &test :
       {std::pair<StringRef, StringRef>{"pair.2", "source.field"},
        {"pair.0.missing", "source.field"},
        {"pair::values", "source.data-bound"},
        {"pair.0.0x0", "syntax.expected"}})
    cases.run("invalid selector: " + test.first, [&] {
      refuses(check("def bad(pair: (Row, index), ys: Vector) -> bool "
                    "where equal_extent(" +
                    test.first + ", ys):\n    return true\n"),
              test.second);
    });
  cases.run("declaration item_from stays distinct from callback conditions",
            [] {
              refuses(check("def bad(xs: Vector, i: index) -> bool where "
                            "item_from(i, xs):\n    return true\n"),
                      "source.finite-domain");
            });
  cases.run("callback conditions cannot assume declaration data premises", [] {
    refuses(check("def bad(f: fn(xs: Vector, ys: Vector) -> bool where "
                  "equal_extent(xs, ys)) -> bool:\n    return true\n"),
            "source.finite-domain");
  });
  for (const auto &test : {std::pair<StringRef, StringRef>{
                               "ghost", "source.assurance-unavailable"},
                           {"statement", "syntax.expected"},
                           {"witness", "syntax.expected"},
                           {"parameter", "syntax.expected"}})
    cases.run("data selector cannot erase a foreign binding: " + test.first,
              [&] {
                refuses(check("def bad(xs: Vector, ys: Vector) -> bool where "
                              "equal_extent(" +
                              test.first + " xs, ys):\n    return true\n"),
                        test.second);
              });
  cases.run("unknown predicates do not become assumed data facts", [] {
    refuses(check("def bad(xs: Vector) -> bool where arbitrary(xs):\n    "
                  "return true\n"),
            "source.capability");
  });
  cases.run("hexadecimal axis remains a syntax refusal", [] {
    refuses(check("def bad(xs: Vector, i: index) -> bool where in_bounds(i, "
                  "xs, 0x0):\n    return true\n"),
            "syntax.expected");
  });
  cases.run("bare comma list remains outside the layout grammar", [] {
    refuses(check("def bad(xs: Vector, ys: Vector, i: index) -> bool where "
                  "equal_extent(xs, ys), in_bounds(i, xs):\n    return true\n"),
            "syntax.line");
  });
  cases.run("only mathematical declarations can assume data conditions", [] {
    refuses(check("local def bad(xs: Vector, i: index) -> bool where "
                  "in_bounds(i, xs):\n    return true\n"),
            "source.data-bound");
  });
  cases.run("fixed extent contradiction is checked before body", [] {
    refuses(check("def bad(xs: Array<2>, ys: Array<3>) -> bool where "
                  "equal_extent(xs, ys):\n    return true\n"),
            "source.data-bound");
  });
  cases.run(
      "member inclusion maps names by position and permits fewer premises", [] {
        take(check(R"(interface Reader:
    def read(xs: Vector, i: index) -> bool where in_bounds(i, xs)
module Exact: Reader:
    def read(values: Vector, position: index) -> bool where in_bounds(position, values):
        return true
module Weaker: Reader:
    def read(values: Vector, position: index) -> bool:
        return true
)"));
      });
  cases.run("member implementation cannot strengthen a data contract", [] {
    refuses(check(R"(interface Reader:
    def read(xs: Vector, i: index) -> bool
module Stronger: Reader:
    def read(xs: Vector, i: index) -> bool where in_bounds(i, xs):
        return true
)"),
            "source.conformance");
  });
  cases.run(
      "selector depth is charged and bounded during header projection", [] {
        Limits limits;
        limits.typeDepth = 1;
        refuses(check("def bad(pair: (Row, index), ys: Vector) -> bool where "
                      "equal_extent(pair.0.values, ys):\n    return true\n",
                      limits),
                "source.limit");
        namespace detail = zkc::language::detail;
        detail::Work work{limits};
        SourceBuffer source{"m",
                            "def f(xs: T) -> bool where equal_extent(xs, "
                            "xs):\n    return true\n",
                            "header.zkc"};
        auto tree =
            zkc::syntax::parseHeaders(zkc::source::Revision(source), {0});
        auto syntax = take(detail::LayoutReader(tree, {}, work).headers());
        require(work.used > 0 && syntax.members.size() == 1,
                "projection did not consume work");
        const auto required = work.used;
        Limits limited;
        limited.work = required - 1;
        detail::Work exhausted{limited};
        refuses(detail::LayoutReader(tree, {}, exhausted).headers(),
                "source.limit");
      });
  for (StringRef predicate :
       {"same(xs, ys)", "apply(xs, ys, fn(left, right) => same(left, right))",
        "apply(xs, ys, same_fixed)", "apply(xs, ys, same<2, 2>)"})
    cases.run("layout concrete callback preparation: " + predicate, [&] {
      auto fixture = MemoryBuffer::getFile(ZKC_LAYOUT_REQUIREMENTS_FIXTURE);
      require(bool(fixture), "missing data requirements fixture");
      CaptureOptions options;
      options.format = "zkc-layout";
      auto captured = take(capture({{"m",
                                     ((*fixture)->getBuffer() + R"(
pub protocol Run roles(P)(xs: Array<2> @P, ys: Array<2> @P) -> (bool, F) @P:
    return ()" + predicate + R"(, total(xs, ys))
)")
                                         .str(),
                                     "callbacks.zkc"}},
                                   options));
      auto project = take(analyze(captured).checkedProject());
      valid(checkScopedElaboration(project));
      auto closed = take(closeNativeRun(project, "m::Run"));
      valid(checkScopedSpecialization(closed));
      take(prepareOriginal(closed));
    });
  return cases.result();
}
