#include "../lib/Frontend/Instantiation/Work.h"
#include "../lib/Frontend/Library/LinkInternal.h"
#include "../lib/Frontend/Model/Access.h"
#include "../lib/Frontend/Model/Libraries.h"
#include "../lib/Frontend/Static/Naturals.h"
#include "support/NativeCases.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Source/Codec.h"
#include <limits>

using namespace llvm;
using namespace zkc;
using namespace zkc::frontend;
using namespace zkc::test;

namespace {
constexpr WorkAccount accounts[] = {
    WorkAccount::AuthoredStatic, WorkAccount::LibraryFormation,
    WorkAccount::GeneratedSource, WorkAccount::Output};
constexpr const char *names[] = {"authored-static", "library-formation",
                                 "generated-source", "output"};
uint64_t &limit(WorkLimits &limits, WorkAccount account) {
  switch (account) {
  case WorkAccount::AuthoredStatic:
    return limits.authoredStatic;
  case WorkAccount::LibraryFormation:
    return limits.libraryFormation;
  case WorkAccount::GeneratedSource:
    return limits.generatedSource;
  case WorkAccount::Output:
    return limits.output;
  }
  llvm_unreachable("unknown account");
}
WorkLimits exact(const WorkUsage &usage) {
  return {usage[0], usage[1], usage[2], usage[3]};
}
std::string librarySource(unsigned aliases,
                          StringRef type = "(Array<bool, 0>, bool)") {
  std::string text =
      "module { library(namespace=\"test\", name=\"budget\", version=\"1\", "
      "resolution=\"fixed\"); fn Echo(x: " +
      type.str() + ") -> " + type.str() + " { return x; } ";
  for (unsigned i = 0; i < aliases; ++i)
    text += "link Alias" + std::to_string(i) + " = Echo<>; ";
  return text + "}";
}
Analysis analyze(StringRef text, WorkLimits limits = {}) {
  return analyzeProtocol(text, "budget.pir", limits);
}
void complete(const Analysis &analysis) {
  if (!analysis.complete()) {
    std::string details;
    for (const auto &d : analysis.diagnostics())
      details += d.code + ": " + d.message + "\n";
    require(false, details);
  }
}
void stopped(const Analysis &analysis, WorkAccount account) {
  require(!analysis.complete(), "budget stop cannot complete");
  require(analysis.state() == AnalysisState::ResourceLimit, "resource state");
  StringRef code =
      account == WorkAccount::AuthoredStatic || account == WorkAccount::Output
          ? "source-staging-limit"
          : "library-source-limit";
  bool found = false;
  for (const auto &d : analysis.diagnostics())
    found |= d.code == code &&
             StringRef(d.message).contains(names[static_cast<size_t>(account)]);
  require(found, "stable resource code and exhausted account");
  refuses(analysis.lower(), code);
  refuses(analysis.checkedModule(), code);
}
library::CheckedBody directBody(unsigned emptyFields) {
  namespace lib = library;
  lib::Environment environment;
  lib::LibraryId owner{"tests", "budgets", "1", "fixed"};
  lib::QualifiedDecl id{owner, {}, "Echo"};
  environment.libraries.push_back({owner, {id}});
  auto empty = lib::Type::product({});
  std::vector<lib::Type> fields(
      emptyFields, lib::Type::array(empty, lib::StaticTerm::natural(0)));
  auto type = lib::Type::product(std::move(fields));
  lib::Body body;
  body.id = id;
  body.signature.inputs = {{type, ""}};
  body.signature.outputs = {{type, ""}};
  body.inputs = {{{0}, {type, ""}}};
  body.returns = {{{0}, {}}};
  return take(lib::checkBody(std::move(body), std::move(environment)));
}
} // namespace

int main() {
  Cases cases;
  cases.run("overflow-safe atomic counters", [&] {
    const auto max = std::numeric_limits<uint64_t>::max();
    WorkBudget budget({max, max, max, max});
    for (auto account : accounts) {
      require(budget.charge(account, max - 1), "large debit");
      require(!budget.charge(account, 2), "sum overflow refused");
      require(budget.used(account) == max - 1, "failed debit is atomic");
      require(!budget.chargeProduct(account, max, max),
              "product overflow refused");
      require(budget.chargeProduct(account, max, 0), "zero product safe");
      require(budget.charge(account), "last unit accepted");
      require(!budget.charge(account), "full counter refuses");
    }
  });
  cases.run("copied call vectors consume the authored account", [&] {
    syntax::Call call;
    call.staticTerms.resize(2);
    call.staticTerms.front().members.resize(3);
    call.attributeAtoms.resize(4);
    call.inputAtoms.resize(5);
    call.staticArguments = source::Names(6);
    call.attributes.resize(7);
    call.inputs.resize(8);
    call.outputs.resize(9);
    call.argumentNames.resize(10);
    syntax::Instruction instruction;
    instruction.value = std::move(call);
    // One instruction and 54 copied vector slots, including lexical metadata.
    WorkLimits limits;
    limits.authoredStatic = 55;
    WorkBudget sufficient(limits);
    require(instantiation::chargeBodyCopy(sufficient, {instruction}),
            "exact call copy allowance");
    require(sufficient.used(WorkAccount::AuthoredStatic) == 55,
            "all call vectors counted");
    --limits.authoredStatic;
    WorkBudget shortBudget(limits);
    require(!instantiation::chargeBodyCopy(shortBudget, {instruction}),
            "call copy refused before allocation");
  });
  cases.run("copied invocation vectors consume the authored account", [&] {
    syntax::Invocation call;
    call.inputs.resize(2);
    call.outputs.resize(3);
    call.resultNames.resize(4);
    syntax::Instruction instruction;
    instruction.value = std::move(call);
    WorkLimits limits;
    limits.authoredStatic = 10;
    WorkBudget sufficient(limits);
    require(instantiation::chargeBodyCopy(sufficient, {instruction}),
            "exact invocation copy allowance");
    require(sufficient.used(WorkAccount::AuthoredStatic) == 10,
            "instruction plus all invocation vector slots");
    --limits.authoredStatic;
    WorkBudget shortBudget(limits);
    require(!instantiation::chargeBodyCopy(shortBudget, {instruction}),
            "invocation copy refused before allocation");
  });
  cases.run("default policy accepts 1024 modest protocol specializations", [&] {
    // Fixed input size protects useful default acceptance independently of
    // measured/injected ceilings. This is not the old worst-case envelope.
    std::string text = "module { protocol Family<F: Field> { roles(A); inputs(";
    for (unsigned i = 0; i < 8; ++i)
      text += (i ? ", " : "") + std::string("A x") + std::to_string(i) +
              ": F::Element";
    text += "); outputs(";
    for (unsigned i = 0; i < 8; ++i)
      text += (i ? ", " : "") + std::string("A F::Element");
    text += "); return (";
    for (unsigned i = 0; i < 8; ++i)
      text += (i ? ", " : "") + std::string("x") + std::to_string(i);
    text += "); } ";
    for (unsigned i = 0; i < 1024; ++i)
      text += "configure Instance" + std::to_string(i) +
              " = Family(F = koala-bear); ";
    text += "}";
    auto analysis = analyze(text);
    complete(analysis);
    require(analysis.instantiations().size() == 1024,
            "all requested specializations retained");
    auto content = take(analysis.lower());
    require(std::get<source::Module>(content).protocols.size() == 1024,
            "all requested specializations emitted");
  });
  for (size_t i = 0; i < 4; ++i) {
    cases.run(Twine(names[i]) + " exhaustion", [&, i] {
      auto text = librarySource(2);
      auto baseline = analyze(text);
      complete(baseline);
      auto limits = exact(baseline.workUsage());
      require(limit(limits, accounts[i]) > 0, "fixture exercises account");
      --limit(limits, accounts[i]);
      stopped(analyze(text, limits), accounts[i]);
      limit(limits, accounts[i]) = 0;
      stopped(analyze(text, limits), accounts[i]);
    });
    cases.run(Twine(names[i]) + " monotonic artifact", [&, i] {
      auto text = librarySource(2);
      auto baseline = analyze(text);
      complete(baseline);
      auto limits = exact(baseline.workUsage());
      auto atLimit = analyze(text, limits);
      complete(atLimit);
      auto expected = source::encode(take(atLimit.lower()));
      limit(limits, accounts[i]) += 37;
      auto larger = analyze(text, limits);
      complete(larger);
      require(source::encode(take(larger.lower())) == expected,
              "same encoded artifact");
      require(larger.workUsage() == baseline.workUsage(),
              "same logical operations");
    });
  }
  cases.run("aliases accumulate across link requests", [&] {
    auto one = analyze(librarySource(1));
    auto two = analyze(librarySource(2));
    complete(one);
    complete(two);
    require(one.workUsage()[0] == two.workUsage()[0],
            "generated aliases do not consume authored static evaluation");
    for (auto account : {WorkAccount::LibraryFormation,
                         WorkAccount::GeneratedSource, WorkAccount::Output}) {
      auto i = static_cast<size_t>(account);
      require(two.workUsage()[i] > one.workUsage()[i],
              "second alias consumes account");
      WorkLimits limits;
      limit(limits, account) = one.workUsage()[i];
      stopped(analyze(librarySource(2), limits), account);
    }
  });
  cases.run("layout refuses repeated empty payload before expansion", [&] {
    WorkLimits limits;
    limits.libraryFormation = 8;
    WorkBudget budget(limits);
    library::detail::World world(budget);
    world.environment.expansionLimit = 1000000;
    auto huge = library::Type::array(library::Type::product({}),
                                     library::StaticTerm::natural(1000000));
    refuses(world.layout(huge, {}), "library-source-limit");
    require(budget.used(WorkAccount::LibraryFormation) <= 8,
            "bulk charge refuses before allocating one million children");
    require(world.environment.expansionLimit == 1000000,
            "compiler account does not rewrite environment admission");
  });
  cases.run("zero-length nested types have costs", [&] {
    auto small = directBody(1), wide = directBody(12);
    WorkBudget first, second;
    auto linked = take(library::link({small, {}, {}}, first));
    auto wider = take(library::link({wide, {}, {}}, second));
    require(linked.functions().back().results.front().leaves.empty(),
            "zero leaves");
    require(wider.functions().back().results.front().leaves.empty(),
            "wide zero leaves");
    require(second.used(WorkAccount::LibraryFormation) >
                first.used(WorkAccount::LibraryFormation),
            "empty fields still cost type visits");
    WorkLimits limits;
    limits.libraryFormation = first.used(WorkAccount::LibraryFormation);
    WorkBudget tight(limits);
    refuses(library::link({wide, {}, {}}, tight), "library-source-limit");
  });
  cases.run("direct link shares budget without a project", [&] {
    auto body = directBody(3);
    WorkBudget measured;
    auto first = take(library::link({body, {}, {}}, measured));
    auto cost = measured.used(WorkAccount::LibraryFormation);
    auto second = take(library::link({body, {}, {}}, measured));
    require(first.identity() == second.identity(),
            "budget absent from identity");
    require(measured.used(WorkAccount::LibraryFormation) == 2 * cost,
            "no reset between aliases");
    WorkLimits limits;
    limits.libraryFormation = 2 * cost - 1;
    WorkBudget tight(limits);
    take(library::link({body, {}, {}}, tight));
    refuses(library::link({body, {}, {}}, tight), "library-source-limit");
  });
  cases.run("output stop retains semantic and library judgments", [&] {
    WorkLimits limits;
    limits.output = 0;
    auto partial = analyze(librarySource(2), limits);
    stopped(partial, WorkAccount::Output);
    require(!partial.types().empty() && !partial.declarations().empty(),
            "retained source judgments");
    auto report = model::AnalysisAccess::libraries(partial);
    require(report && !report->clients.empty() && report->links.size() == 3,
            "checked clients and all completed links survive");
    auto project = ProjectInput::single(Input::withoutFile(librarySource(1)));
    refuses(compileProject(project, limits), "source-staging-limit");
  });
  cases.run("library stop retains the completed judgment prefix", [&] {
    auto text = librarySource(2);
    auto baseline = analyze(text);
    complete(baseline);
    WorkLimits limits;
    limits.libraryFormation = baseline.workUsage()[1] - 1;
    auto partial = analyze(text, limits);
    stopped(partial, WorkAccount::LibraryFormation);
    auto report = model::AnalysisAccess::libraries(partial);
    require(report && !report->clients.empty() && !report->links.empty(),
            "library budget failure preserves preceding checked judgments");
  });
  cases.run("captured modules share the authored account", [&] {
    auto project = [](bool second) {
      ProjectLibrary owner;
      owner.sources.push_back(
          {{},
           Input(second ? "module { mod a; mod b; }" : "module { mod a; }",
                 "root.pir")});
      owner.sources.push_back(
          {{"a"},
           Input("module { pub fn Echo(x: bool) -> bool { return x; } }",
                 "a.pir")});
      if (second)
        owner.sources.push_back(
            {{"b"},
             Input("module { pub fn Echo(x: bool) -> bool { return x; } }",
                   "b.pir")});
      return take(ProjectInput::capture({std::move(owner)}));
    };
    auto first = analyzeProject(project(false));
    auto second = analyzeProject(project(true));
    complete(first);
    complete(second);
    require(second.workUsage()[0] > first.workUsage()[0],
            "imported declarations add logical work");
    WorkLimits limits;
    limits.authoredStatic = first.workUsage()[0];
    stopped(analyzeProject(project(true), limits), WorkAccount::AuthoredStatic);
  });
  cases.run("natural accounting independent of dependency cache order", [&] {
    auto constant = [](std::string name, syntax::Expression expression) {
      syntax::Constant result;
      result.name = std::move(name);
      result.expression = std::move(expression);
      return result;
    };
    syntax::Expression literal, reference;
    literal.kind = syntax::Expression::Kind::Index;
    literal.name = "7";
    reference.name = "A";
    auto a = constant("A", literal), b = constant("B", reference);
    WorkBudget forward, reverse;
    auto x = take(
        static_eval::evaluateNaturals({a, b}, "", "test", nullptr, forward));
    auto y = take(
        static_eval::evaluateNaturals({b, a}, "", "test", nullptr, reverse));
    require(x == y && x.at("B") == 7, "independent expected natural");
    require(forward.used(WorkAccount::AuthoredStatic) == 4 &&
                forward.usage() == reverse.usage(),
            "two declarations plus two written expressions");
    WorkLimits limits;
    limits.authoredStatic = 3;
    WorkBudget tight(limits);
    refuses(static_eval::evaluateNaturals({a, b}, "", "test", nullptr, tight),
            "source-staging-limit");
  });
  return cases.result();
}
