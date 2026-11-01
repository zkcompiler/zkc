#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "support/SourceProject.h"
#include "zkc/Analysis/CommonControl.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/BindingTypes.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/CommonControl.h"
#include "zkc/Language/Names.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/STLExtras.h"
#include <map>
#include <set>
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source, bool legacy = false,
                               const Limits &limits = {}) {
  CaptureOptions options;
  options.format = legacy ? "zkc" : "zkc-layout";
  auto captured = capture({{"m", source.str(), "recurrence.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  auto found = llvm::find_if(project.declarations(), [&](const auto &decl) {
    return decl.name == name;
  });
  require(found != project.declarations().end(),
          "missing declaration: " + name);
  return *found;
}
std::string replaceText(std::string source, StringRef from, StringRef to) {
  auto at = source.find(from.str());
  require(at != std::string::npos, "missing fixture fragment: " + from);
  source.replace(at, from.size(), to.str());
  return source;
}
std::string header(StringRef subject, unsigned indent = 8) {
  std::string pad(indent, ' ');
  return pad + "if " + subject.str() + ":\n" + pad + "    ()\n" + pad +
         "else:\n" + pad + "    ()\n";
}
std::string loop(StringRef transition, unsigned count = 2,
                 bool exitControl = false) {
  return (Twine("pub protocol Run roles(P,V)() -> () @(P,V):\n") +
          "    mut state = true\n    for i in 0..index<" + Twine(count) +
          ">() roles(P,V) max 4:\n" + header("state") + transition +
          (exitControl ? header("state", 4) : "") + "    return ()\n")
      .str();
}
std::string divergent(unsigned count = 2, bool exitControl = false) {
  return loop("        state := @(P = true, V = false)\n", count, exitControl);
}
std::string booleanHelper() {
  return "def xor(left: bool, right: bool) -> bool:\n"
         "    return if left:\n        if right:\n            false\n"
         "        else:\n            true\n    else:\n        right\n";
}
std::string pure(bool exitControl = true) {
  return booleanHelper() +
         std::string(
             "pub protocol Run roles(P,V)(count: index @(P,V), base: bool "
             "@(P,V), step: bool @(P,V)) -> () @(P,V):\n"
             "    mut state = base\n"
             "    for i in 0..count roles(P,V) max 4:\n") +
         header("state") + "        state := xor(state, step)\n" +
         (exitControl ? header("state", 4) : "") + "    return ()\n";
}
// Canonical connected equality classes, separately for exact physical type and
// observation. Direction, spanning edges and emission order carry no meaning.
using Inventory = std::map<std::string, std::set<std::set<std::string>>>;
Inventory canonical(
    const std::vector<std::pair<std::string, std::set<std::string>>> &rows) {
  Inventory result;
  for (const auto &row : rows) {
    auto observation = row.first;
    auto components = row.second;
    auto &classes = result[observation];
    bool merged;
    do {
      merged = false;
      for (auto it = classes.begin(); it != classes.end(); ++it)
        if (llvm::any_of(*it, [&](const auto &item) {
              return components.count(item);
            })) {
          components.insert(it->begin(), it->end());
          classes.erase(it);
          merged = true;
          break;
        }
    } while (merged);
    if (components.size() > 1)
      classes.insert(std::move(components));
  }
  return result;
}
std::string facetKey(mlir::Type type, bool tag,
                     std::optional<unsigned> extent) {
  std::string key;
  raw_string_ostream stream(key);
  type.print(stream);
  stream << (extent ? ":extent:" + std::to_string(*extent)
             : tag  ? ":tag"
                    : ":value");
  return key;
}
std::string componentKey(unsigned input, StringRef role,
                         ArrayRef<unsigned> path) {
  std::string key = std::to_string(input) + ":" + role.str();
  for (unsigned step : path)
    key += ":" + std::to_string(step);
  return key;
}
protocol_ir::MathematicalOp nativeProtocol(mlir::ModuleOp module,
                                           StringRef symbol) {
  protocol_ir::MathematicalOp result;
  module.walk([&](protocol_ir::MathematicalOp function) {
    if (function.getSymName() == symbol)
      result = function;
  });
  require(bool(result), "emitted original omitted Protocol: " + symbol);
  return result;
}
auto pairedEntry(mlir::MLIRContext &context, const ClosedEntry &entry,
                 const Limits &limits = {}) {
  auto bytes = take(emitOriginal(entry, context, limits));
  auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(module), "real emitted original did not parse");
  require(mlir::succeeded(admitStage(*module)),
          "real emitted original failed native admission");
  take(compareOriginal(entry, *module, limits));
  std::vector<NativeCommonControlRequirement> rootRequirements;
  unsigned compared = 0;
  for (const auto &decl : entry.declarations()) {
    if (decl.kind != Declaration::Kind::Protocol || !decl.body ||
        decl.abstract || !decl.parameters.empty() ||
        !decl.scopedInputs.empty() || !decl.domainInputs.empty())
      continue;
    auto root = nativeProtocol(*module, decl.symbol);
    uint64_t remaining = 8000000;
    facts::Work work(remaining);
    auto native = take(zkc::deriveCommonControlRequirements(root, work));
    auto mapped =
        take(deriveNativeCommonControlRequirements(entry, decl.id, limits));
    std::vector<std::pair<std::string, std::set<std::string>>> actual, expected;
    for (const auto &requirement : native) {
      std::set<std::string> parts;
      for (const auto &component : requirement.components)
        parts.insert(componentKey(component.input, component.role.getValue(),
                                  component.path));
      actual.emplace_back(facetKey(requirement.type, requirement.tagOnly,
                                   requirement.extentAxis),
                          std::move(parts));
    }
    for (const auto &requirement : mapped) {
      std::set<std::string> parts;
      for (const auto &component : requirement.components) {
        auto role = nativeRoleName(component.role);
        require(component.originalInput < root.getInputRoles().size(),
                "source mapped outside actual original input telescope");
        unsigned participantInput = 0;
        for (unsigned i = 0; i < component.originalInput; ++i)
          if (!mlir::isa<protocol_ir::ServiceReferenceType>(
                  root.getBody().front().getArgument(i).getType()) &&
              llvm::any_of(
                  mlir::cast<mlir::ArrayAttr>(root.getInputRoles()[i]),
                  [&](mlir::Attribute r) {
                    return mlir::cast<mlir::StringAttr>(r).getValue() == role;
                  }))
            ++participantInput;
        require(component.participantInput == participantInput,
                "flat participant coordinate differs from actual original");
        parts.insert(
            componentKey(component.originalInput, role, component.path));
      }
      expected.emplace_back(
          facetKey(protocol::decodeBoundType(&context, requirement.type),
                   requirement.tagOnly, requirement.extentAxis),
          std::move(parts));
    }
    require(canonical(actual) == canonical(expected),
            "canonical source/native input/path/type/observation inventory "
            "differs: " +
                decl.name);
    ++compared;
    if (decl.id.index == entry.protocol().id.index)
      rootRequirements = std::move(mapped);
  }
  require(compared > 0, "no actual concrete Protocol inventories compared");
  return rootRequirements;
}
auto pairedProject(mlir::MLIRContext &context, const CheckedProject &project,
                   const Limits &limits = {}) {
  return pairedEntry(context, take(closeNativeRun(project, "m::Run", limits)),
                     limits);
}
Type naturalArgument(uint64_t value) {
  Type result(Type::Kind::Natural);
  result.dimension = Natural::constant(value);
  return result;
}
std::string arrayProtocol(StringRef length = "N", unsigned index = 1) {
  std::string parameters = length == "N" ? "<N:nat>" : "";
  return "module m;protocol Run" + parameters + " roles(P,V)(xs:[bool;" +
         length.str() + "]@(P,V))->(r:bool@(P,V)){let flag=xs[" +
         std::to_string(index) +
         "];let r=if flag {true}else{false};return(r=r);}";
}
std::string nestedProtocol() {
  return R"(module m;
protocol Run roles(P,V)(n:index@(P,V),flag:bool@(P,V))->(){
 for _ in 0..n roles(P,V) max 2 {
  for _ in 0..n roles(P,V) max 2 {if flag {()}else{()}}
 }
 return();
})";
}
auto paired(mlir::MLIRContext &context, StringRef source, bool legacy = false) {
  return pairedProject(context, take(check(source, legacy)));
}
void rawInputs(StringRef source, ArrayRef<unsigned> inputs) {
  auto project = take(check(source, true));
  auto rows = take(zkc::language::deriveCommonControlRequirements(
      project, named(project, "Run").id));
  std::set<unsigned> actual;
  for (const auto &row : rows) {
    require(row.components.size() == 2, "raw source obligation arity differs");
    for (const auto &component : row.components)
      actual.insert(component.input);
  }
  require(rows.size() == inputs.size() &&
              actual == std::set<unsigned>(inputs.begin(), inputs.end()),
          "raw checked-source observable dependencies differ");
}
void exactInputs(ArrayRef<NativeCommonControlRequirement> rows,
                 ArrayRef<unsigned> inputs) {
  require(rows.size() == inputs.size(), "nonminimal common input inventory");
  std::set<unsigned> actual;
  for (const auto &row : rows) {
    require(!row.tagOnly && !row.extentAxis && row.components.size() == 2,
            "wrong value observation");
    auto input = row.components[0].source.input;
    for (const auto &component : row.components)
      require(component.source.input == input &&
                  component.source.path.empty() && component.path.empty(),
              "input/path association differs");
    actual.insert(input);
  }
  require(actual == std::set<unsigned>(inputs.begin(), inputs.end()),
          "base or transition obligation omitted");
}
std::string cyclic(bool badBase = false, bool badStep = false) {
  return std::string("pub protocol Run roles(P,V)() -> () @(P,V):\n"
                     "    mut x = true\n    mut y = ") +
         (badBase ? "@(P = true, V = false)" : "true") +
         "\n    for i in 0..index<3>() roles(P,V) max 4:\n" + header("x") +
         "        previous = x\n        x := y\n        y := " +
         (badStep ? "@(P = previous, V = false)" : "previous") +
         "\n    return ()\n";
}
std::string variants(bool payloadControl = false, bool divergentTag = false) {
  std::string source = "enum Choice:\n    Left(bool)\n    Right(bool)\n"
                       "pub protocol Run roles(P,V)() -> () @(P,V):\n"
                       "    mut state = Choice::Left(true)\n"
                       "    for i in 0..index<2>() roles(P,V) max 4:\n"
                       "        match state:\n"
                       "            case Left(bit):\n";
  source += payloadControl ? header("bit", 16) : "                ()\n";
  source += "            case Right(bit):\n";
  source += payloadControl ? header("bit", 16) : "                ()\n";
  return source +
         "        payload = @(P = true, V = false)\n"
         "        left = Choice::Left(payload)\n        right = Choice::" +
         (divergentTag ? "Right" : "Left") +
         "(payload)\n        state := @(P = left, V = right)\n    return ()\n";
}
std::string variantInputs(bool payloadControl) {
  return std::string(
             "enum Choice:\n    Left(bool)\n    Right(bool)\n"
             "pub protocol Run roles(P,V)(base: Choice @(P,V), step: Choice "
             "@(P,V)) -> () @(P,V):\n"
             "    mut state = base\n"
             "    for i in 0..index<2>() roles(P,V) max 4:\n"
             "        match state:\n            case Left(bit):\n") +
         (payloadControl ? header("bit", 16) : "                ()\n") +
         "            case Right(bit):\n" +
         (payloadControl ? header("bit", 16) : "                ()\n") +
         "        state := step\n    return ()\n";
}
std::string nested(bool badStep) {
  return loop(
      std::string("        mut inner = state\n"
                  "        for j in 0..index<2>() roles(P,V) max 4:\n") +
      header("inner", 12) + "            inner := " +
      (badStep ? "@(P = inner, V = false)" : "inner") +
      "\n        state := inner\n");
}
} // namespace
int main() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("equal initializer cannot hide divergent second iteration",
            [&] { refuses(check(divergent()), "source.common-provenance"); });
  cases.run("safe pure recurrence has exact base and transition obligations",
            [&] { exactInputs(paired(context, pure()), {0, 1, 2}); });
  for (unsigned count : {0, 1}) {
    cases.run("body only observes base at count " + Twine(count), [&] {
      require(paired(context, divergent(count)).empty(),
              "unused step demanded");
    });
    cases.run("exit observes actual path at count " + Twine(count), [&] {
      if (count)
        refuses(check(divergent(count, true)), "source.common-provenance");
      else
        require(paired(context, divergent(count, true)).empty(),
                "zero exit demanded step");
    });
  }
  cases.run("dynamic at-most-one body needs count and base only", [&] {
    exactInputs(paired(context, replaceText(pure(false), "max 4", "max 1")),
                {0, 1});
  });
  cases.run("received transition refuses when demanded", [&] {
    auto source = loop("        received <- send state from P to V\n"
                       "        state := @(P = state, V = received)\n");
    refuses(check(source), "source.common-provenance");
    require(
        paired(context, replaceText(source, "index<2>", "index<1>")).empty(),
        "unused received transition demanded");
  });
  cases.run("Local transition refuses when demanded", [&] {
    auto source =
        std::string(
            "local def identity(bit: bool) -> bool:\n    return bit\n") +
        loop("        bit: bool @V <- identity(state)\n"
             "        state := @(P = state, V = bit)\n");
    refuses(check(source), "source.common-provenance");
    paired(context, replaceText(source, "index<2>", "index<1>"));
  });
  cases.run("service transition refuses when demanded", [&] {
    auto source =
        replaceText(loop("        sample <- coins.draw()\n"
                         "        bit = sample == sample\n"
                         "        state := @(P = state, V = bit)\n"),
                    "pub protocol Run roles(P,V)()",
                    "domain F = field(\"bls12-381.fr\")\n"
                    "pub protocol Run roles(P,V)(coins: Random<F> @V)");
    refuses(check(source), "source.common-provenance");
    paired(context, replaceText(source, "index<2>", "index<1>"));
  });
  cases.run("unrelated private ordered carry stays undemanded", [&] {
    auto source =
        replaceText(loop("        received <- send state from P to V\n"
                         "        private := received\n"),
                    "    mut state = true\n",
                    "    mut state = true\n    mut private: bool @V = false\n");
    require(paired(context, source).empty(), "private state gained obligation");
  });
  cases.run("grounded simultaneous cyclic slots are common", [&] {
    require(paired(context, cyclic()).empty(), "grounded cycle refused");
  });
  cases.run("cyclic equality cannot hide bad base",
            [&] { refuses(check(cyclic(true)), "source.common-provenance"); });
  cases.run("cyclic equality cannot hide bad transition", [&] {
    refuses(check(cyclic(false, true)), "source.common-provenance");
  });
  cases.run("nested grounded recurrence retains enclosing assumptions", [&] {
    require(paired(context, nested(false)).empty(),
            "nested common loop refused");
  });
  cases.run("inner recurrence cannot hide enclosing divergent step",
            [&] { refuses(check(nested(true)), "source.common-provenance"); });
  cases.run("pure enum constructor formation remains an explicit frontend gap",
            [&] { refuses(check(variants()), "source.mode"); });
  for (bool payloadControl : {false, true})
    cases.run(payloadControl ? "exact base and step alternative payload paths"
                             : "base and step tags omit payload obligations",
              [&] {
                auto rows = paired(context, variantInputs(payloadControl));
                require(rows.size() == (payloadControl ? 6 : 2),
                        "variant inventory count");
                for (unsigned input : {0, 1}) {
                  unsigned tags = 0, payloads = 0;
                  for (const auto &row : rows)
                    if (row.components[0].source.input == input) {
                      if (row.tagOnly) {
                        require(row.components[0].source.path.empty(),
                                "tag path differs");
                        ++tags;
                      } else {
                        const auto &path = row.components[0].source.path;
                        require(path.size() == 2 &&
                                    path[0].kind ==
                                        CommonControlStep::Kind::Alternative &&
                                    path[0].index < 2 &&
                                    path[1].kind ==
                                        CommonControlStep::Kind::Payload &&
                                    path[1].index == 0,
                                "typed payload path differs");
                        payloads |= 1u << path[0].index;
                      }
                    }
                  require(tags == 1 && payloads == (payloadControl ? 3 : 0),
                          "base/step observation missing");
                }
              });
  cases.run("zero-trip dormant body still refuses direct received control",
            [&] {
              auto source =
                  replaceText(divergent(0), header("state"),
                              "        received <- send state from P to V\n" +
                                  header("@(P = state, V = received)"));
              refuses(check(source), "source.common-provenance");
            });
  cases.run("every insufficient work allowance refuses exactly", [&] {
    auto project = take(check(pure()));
    auto target = named(project, "Run").id;
    uint64_t low = 0, high = 8000000;
    while (low < high) {
      uint64_t middle = low + (high - low) / 2;
      Limits limits;
      limits.work = middle;
      auto result = zkc::language::deriveCommonControlRequirements(
          project, target, limits);
      if (result)
        high = middle;
      else {
        require(namesIdentifier(toString(result.takeError()), "source.limit"),
                "work exhaustion changed diagnostic");
        low = middle + 1;
      }
    }
    require(low > 0 && low < 8000000, "no finite work boundary");
    for (uint64_t allowance = 0; allowance < low; ++allowance) {
      Limits limits;
      limits.work = allowance;
      refuses(zkc::language::deriveCommonControlRequirements(project, target,
                                                             limits),
              "source.limit");
    }
    Limits limits;
    limits.work = low;
    require(take(zkc::language::deriveCommonControlRequirements(project, target,
                                                                limits))
                    .size() == 3,
            "exact work boundary changed requirements");
    outs() << "source recurrence exact work boundary: " << low << '\n';
  });
  cases.run("dynamic one-trip exit retains transition and zero path", [&] {
    exactInputs(paired(context, replaceText(pure(), "max 4", "max 1")),
                {0, 1, 2});
  });
  cases.run("repeated helpers substitute exact inputs and ordered roles", [&] {
    auto source =
        booleanHelper() +
        R"(protocol Evolve roles(A,B)(count: index @(A,B), base: bool @(A,B), step: bool @(A,B)) -> bool @(A,B):
    mut state = base
    for i in 0..count roles(A,B) max 4:
        if state:
            ()
        else:
            ()
        state := xor(state, step)
    return state
pub protocol Run roles(P,V)(count: index @(P,V), a: bool @(P,V), b: bool @(P,V), c: bool @(P,V), d: bool @(P,V)) -> () @(P,V):
    first <- Evolve(count, a, b) @(V,P)
    second <- Evolve(count, c, d) @(P,V)
    return ()
)";
    auto rows = paired(context, source);
    exactInputs(rows, {0, 1, 2, 3, 4});
    for (const auto &row : rows) {
      unsigned input = row.components[0].source.input;
      require(row.components[0].role == (input < 3 ? 1u : 0u) &&
                  row.components[1].role == (input < 3 ? 0u : 1u),
              "actual helper role permutation was sorted away");
    }
  });
  cases.run("separate equal-looking helper clocks never share induction", [&] {
    refuses(
        check(R"(protocol Clock roles(A,B)(count: index @(A,B)) -> index @(A,B):
    mut last = index<0>()
    for i in 0..count roles(A,B) max 4:
        last := i
    return last
pub protocol Run roles(P,V)(leftCount: index @(P,V), rightCount: index @(P,V)) -> () @(P,V):
    left <- Clock(leftCount) @(P,V)
    right <- Clock(rightCount) @(P,V)
    both = @(P = left, V = right)
    if both == index<0>():
        ()
    else:
        ()
    return ()
)"),
        "source.common-provenance");
  });
  cases.run(
      "nested source fields flatten before conditional payload paths", [&] {
        auto source = replaceText(variantInputs(true), "pub protocol Run",
                                  "struct Box:\n    pub padding: bool\n    pub "
                                  "choice: Choice\npub protocol Run");
        source = replaceText(source, "base: Choice", "base: Box");
        source = replaceText(source, "step: Choice", "step: Box");
        source = replaceText(source, "match state:", "match state.choice:");
        auto rows = paired(context, source);
        require(rows.size() == 6, "nested field observation missing");
        for (const auto &row : rows) {
          const auto &component = row.components[0];
          require(
              component.source.path[0].kind == CommonControlStep::Kind::Field &&
                  component.source.path[0].index == 1 &&
                  component.originalInput == component.source.input * 2 + 1 &&
                  component.path.size() == (row.tagOnly ? 0u : 2u),
              "source field confused with native variant payload");
        }
      });
  cases.run("nested variant payload projections retain every alternative", [&] {
    auto source = replaceText(variantInputs(true), "pub protocol Run",
                              "enum Box:\n    Wrap(Choice)\npub protocol Run");
    source = replaceText(source, "base: Choice", "base: Box");
    source = replaceText(source, "step: Choice", "step: Box");
    source = replaceText(
        source,
        "        match state:\n            case Left(bit):\n" +
            header("bit", 16) + "            case Right(bit):\n" +
            header("bit", 16),
        "        match state:\n            case Wrap(choice):\n"
        "                match choice:\n                    case Left(bit):\n" +
            header("bit", 24) + "                    case Right(bit):\n" +
            header("bit", 24));
    auto rows = paired(context, source);
    require(rows.size() == 8, "nested conditional inventory differs");
    for (const auto &row : rows)
      require(row.components[0].source.path.size() ==
                  row.components[0].path.size(),
              "nested native alternative path truncated");
  });
  cases.run("selected enum recurrence transports only tag obligations", [&] {
    auto source = replaceText(variantInputs(false), "        state := step\n",
                              "        state := if true:\n            step\n"
                              "        else:\n            state\n");
    auto rows = paired(context, source);
    require(rows.size() == 2 &&
                llvm::all_of(rows, [](const auto &r) { return r.tagOnly; }),
            "selected tag gained payload requirements");
  });
  cases.run("recurrence extents remain independent of container values", [&] {
    auto rows = paired(context, R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
math fn extent(xs:Vector<Fr>)->index { return intrinsic<Fr>("vector.length",xs); }
protocol Run roles(P,V)(base:Vector<Fr>@(P,V),step:Vector<Fr>@(P,V))->() {
 let mut state=base;
 for _ in 0..2 roles(P,V) max 4 {
   let n=extent(state);
   for _ in 0..n roles(P,V) max 4 {}
   state=step;
 }
 return();
})",
                       true);
    require(rows.size() == 2, "extent gained container value obligations");
    std::set<unsigned> inputs;
    for (const auto &row : rows) {
      require(!row.tagOnly && row.extentAxis == 0 &&
                  row.components[0].source.path.empty(),
              "extent facet or axis differs");
      inputs.insert(row.components[0].source.input);
    }
    require(inputs == std::set<unsigned>({0, 1}),
            "extent base or step missing");
  });
  cases.run(
      "actual admitted candidate yield mutation invalidates recurrence", [&] {
        auto project = take(check(loop("        state := state\n")));
        auto entry = take(closeNativeRun(project, "m::Run"));
        auto bytes = take(emitOriginal(entry, context));
        auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
        require(bool(module) && mlir::succeeded(admitStage(*module)),
                "safe real candidate failed admission");
        protocol_ir::RepeatOp repeat;
        module->walk([&](protocol_ir::RepeatOp op) { repeat = op; });
        require(bool(repeat), "candidate has no actual loop");
        auto &body = repeat.getBody().front();
        mlir::OpBuilder builder(&body.back());
        mlir::OperationState constant(repeat.getLoc(), "arith.constant");
        constant.addTypes(builder.getI1Type());
        constant.addAttribute("value", builder.getBoolAttr(false));
        auto bit = builder.create(constant)->getResult(0);
        mlir::OperationState assembly(repeat.getLoc(),
                                      "protocol.assemble_roles");
        assembly.addOperands({body.getArgument(1), bit});
        assembly.addTypes(builder.getI1Type());
        assembly.addAttribute("roles", repeat.getRoles());
        body.back().setOperand(0, builder.create(assembly)->getResult(0));
        uint64_t remaining = 8000000;
        facts::Work work(remaining);
        refuses(zkc::deriveCommonControlRequirements(
                    nativeProtocol(*module, entry.protocol().symbol), work),
                "common-control-provenance");
        bool exact = false;
        mlir::ScopedDiagnosticHandler capture(
            &context, [&](mlir::Diagnostic &d) {
              exact |= namesIdentifier(d.str(), "common-control-provenance");
              return mlir::success();
            });
        require(mlir::failed(admitStage(*module)) && exact,
                "mutated actual candidate reused initializer evidence");
        refuses(check(divergent()), "source.common-provenance");
      });
  cases.run("asymmetric peer inputs retain exact participant positions", [&] {
    auto source =
        replaceText(pure(), "(count: index", "(private: bool @V, count: index");
    auto rows = paired(context, source);
    exactInputs(rows, {1, 2, 3});
    for (const auto &row : rows)
      for (const auto &component : row.components)
        require(component.participantInput ==
                    component.originalInput - (component.role == 0 ? 1u : 0u),
                "absent peer input shifted the wrong participant");
  });
  cases.run("three-role equality classes retain every base and step edge", [&] {
    auto source = pure();
    while (source.find("P,V") != std::string::npos)
      source = replaceText(source, "P,V", "P,Q,V");
    source = replaceText(source, "if state:", "if state roles(V,P,Q):");
    auto rows = paired(context, source);
    require(rows.size() == 6, "three-role inventory lost or gained an edge");
    for (unsigned input : {0, 1, 2}) {
      std::set<unsigned> roles;
      unsigned edges = 0;
      for (const auto &row : rows)
        if (row.components[0].source.input == input) {
          ++edges;
          for (const auto &component : row.components) {
            require(component.source.input == input && component.path.empty(),
                    "three-role input association differs");
            roles.insert(component.role);
          }
        }
      require(edges == 2 && roles == std::set<unsigned>({0, 1, 2}),
              "three-role equality class is incomplete");
    }
  });
  cases.run("iteration index belongs to its own shared invocation", [&] {
    require(paired(context, replaceText(loop("        state := state\n"),
                                        "if state:", "if i == index<0>():"))
                .empty(),
            "same loop index gained an input obligation");
  });
  cases.run(
      "obligations retain their actual establishing source controls", [&] {
        auto source = pure();
        auto rows = paired(context, source);
        for (const auto &row : rows) {
          auto span =
              StringRef(source).slice(row.control.begin, row.control.end);
          require(span.starts_with(row.components[0].source.input == 0
                                       ? "for "
                                       : "if state"),
                  "requirement lost the actual source establishing control");
        }
      });
  cases.run("retained Protocol overload refuses non-Protocol targets", [&] {
    auto project = take(check(pure()));
    auto entry = take(closeNativeRun(project, "m::Run"));
    require(take(deriveNativeCommonControlRequirements(entry, {})).size() == 3,
            "existing braced Limits call changed meaning");
    refuses(deriveNativeCommonControlRequirements(entry,
                                                  named(project, "xor").id, {}),
            "source.common-component");
    refuses(deriveNativeCommonControlRequirements(
                entry, DeclarationId{0xffffffffu}, {}),
            "source.common-component");
  });
  cases.run("lowered source derivation depth ceilings refuse exactly", [&] {
    auto project = take(check(pure()));
    auto target = named(project, "Run").id;
    Limits limits;
    limits.callDepth = 0;
    refuses(
        zkc::language::deriveCommonControlRequirements(project, target, limits),
        "source.limit");
    limits = Limits{};
    limits.expressionDepth = 0;
    refuses(
        zkc::language::deriveCommonControlRequirements(project, target, limits),
        "source.limit");
  });
  cases.run("received enum tags refuse only on demanded transitions", [&] {
    auto source = replaceText(variantInputs(false), "        state := step\n",
                              "        received <- send step from P to V\n"
                              "        state := @(P = step, V = received)\n");
    refuses(check(source), "source.common-provenance");
    auto rows = paired(context, replaceText(source, "index<2>", "index<1>"));
    require(rows.size() == 1 && rows[0].tagOnly &&
                rows[0].components[0].source.input == 0,
            "one-trip body demanded a received successor tag");
  });
  cases.run("generic finite state retains actual product type and provenance",
            [&] {
              exactInputs(paired(context, R"zkc(module m;
domain fn range(lower:index,upper:index)->domain<index> = domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn first(x:bool)->bool {
 let result=fold(range(0,2),(x,x),fn(state,i)=>state);
 return result.0;
}
protocol Run roles(P,V)(x:bool@(P,V))->(r:bool@(P,V)) {let condition=first(x);let r=if condition {true}else{false};return(r=r);}
)zkc",
                                 true),
                          {0});
            });
  cases.run("pure equal-arm result discards only its selector dependency", [&] {
    exactInputs(paired(context, R"zkc(module m;
math fn apply(x:bool,body:math fn(bool)->bool)->bool{return body(x);}
math fn choose(flag:bool,x:bool)->bool{return if flag{x}else{x};}
protocol Run roles(P,V)(flag:bool@(P,V),other:bool@(P,V))->(r:bool@(P,V)){
 let condition=apply(flag,fn(y)=>choose(y,other));
 let r=if condition {true}else{false};return(r=r);
}
entry fn Main(inputs:Run::Inputs){return Run::run(inputs);}
)zkc",
                       true),
                {1});
  });
  for (bool shared : {false, true})
    cases.run(
        shared ? "generic staged index controls shared scheduling"
               : "generic unused staged index remains well formed",
        [&] {
          std::string source = R"(module m;
math fn number<N:nat>()->index{return index<N>();}
math fn inner<N:nat>()->index{return number<pow2(N)>();}
math fn outer<M:nat>()->index{return inner<pow2(M)>();}
protocol Run<N:nat> roles(P,V)()->(){let n=outer<N>();
)";
          if (shared)
            source += "for _ in 0..n roles(P,V) max 4 {}";
          source += "return();}";
          auto project = take(check(source, true));
          require(take(zkc::language::deriveCommonControlRequirements(
                           project, named(project, "Run").id))
                      .empty(),
                  "generic static count acquired input obligations");
          for (unsigned actual : {0, 5}) {
            auto entry = take(closeNativeRun(project, "m::Run", {},
                                             {naturalArgument(actual)}));
            bool found = false;
            for (const auto &decl : entry.declarations())
              if (decl.body)
                for (const auto &op : decl.body->operations)
                  if (const auto *math = std::get_if<MathValue>(&op.action))
                    if (math->identity == MathematicalIdentity::IndexConstant &&
                        !math->staticArguments.empty()) {
                      require(math->staticArguments.front().dimension ==
                                  Natural::constant(
                                      actual == 0 ? 2 : 4294967296ULL),
                              "closed staged index has the wrong value");
                      found = true;
                    }
            require(found, "closed staged index was not inspected");
            require(pairedEntry(context, entry).empty(),
                    "closed staged index acquired native input premises");
          }
          refuses(closeNativeRun(project, "m::Run", {}, {naturalArgument(6)}),
                  "source.natural");
        });
  for (bool distinct : {false, true})
    for (bool receivedSelector : {false, true})
      cases.run(
          std::string("staged math statics ") +
              (distinct ? "preserve distinct lexical bindings"
                        : "agree through irrelevant relay frames") +
              (receivedSelector ? " with received selector"
                                : " with input selector"),
          [&] {
            std::string source = R"(module m;
math fn number<N:nat>()->index{return index<N>();}
math fn inner<N:nat>()->index{return number<pow2(N)>();}
math fn outer<M:nat>()->index{return inner<pow2(M)>();}
math fn relay<N:nat,Unused:nat>()->index{return outer<N>();}
math fn choose<N:nat,M:nat>(flag:bool)->index{return if flag{outer<N>()}else{relay<M,17>()};}
protocol Run<N:nat,M:nat> roles(P,V)(flag:bool@(P,V))->(){
)";
            if (receivedSelector)
              source += "let received=send P->V(flag);let "
                        "both=@(P=flag,V=received);";
            source += std::string("let n=choose<N,") + (distinct ? "M" : "N") +
                      ">(" + (receivedSelector ? "both" : "flag") +
                      ");for _ in 0..n roles(P,V) max 4 {}return();}";
            if (distinct && receivedSelector) {
              refuses(check(source, true), "source.common-provenance");
              return;
            }
            auto project = take(check(source, true));
            auto raw = take(zkc::language::deriveCommonControlRequirements(
                project, named(project, "Run").id));
            require(raw.size() == unsigned(distinct),
                    "staged math identity changed selector demand");
            auto entry =
                take(closeNativeRun(project, "m::Run", {},
                                    {naturalArgument(0), naturalArgument(1)}));
            exactInputs(pairedEntry(context, entry),
                        distinct ? std::vector<unsigned>{0}
                                 : std::vector<unsigned>{});
          });
  cases.run("staged math statics do not equate received count operands", [&] {
    refuses(check(R"(module m;
math fn number<N:nat>(x:bool)->index{return if x{index<N>()}else{index<0>()};}
math fn inner<N:nat>(x:bool)->index{return number<pow2(N)>(x);}
math fn outer<M:nat>(x:bool)->index{return inner<pow2(M)>(x);}
protocol Run<N:nat> roles(P,V)(x:bool@(P,V))->(){
 let received=send P->V(x);let both=@(P=x,V=received);let n=outer<N>(both);
 for _ in 0..n roles(P,V) max 4 {}return();
})",
                  true),
            "source.common-provenance");
  });
  cases.run("staged identity keeps authored natural and schema refusals", [&] {
    refuses(check(R"(module m;
protocol Run<N:nat> roles(P,V)()->(){let n=index<pow2(pow2(N))>();return();}
)",
                  true),
            "source.natural");
    refuses(check(R"(module m;
math fn accept<N:nat>(x:[bool;pow2(N)])->bool{return x[0];}
math fn bad<M:nat>(x:[bool;pow2(M)])->bool{return accept<pow2(M)>(x);}
)",
                  true),
            "source.natural");
    refuses(check(R"(module m;
math fn accept<N:nat>()->bool where 1<=pow2(N){return true;}
math fn bad<M:nat>()->bool{return accept<pow2(M)>();}
)",
                  true),
            "source.natural");
    refuses(check(R"(module m;
interface Operation {math fn number<N:nat>()->index;}
module Concrete:Operation {math fn number<N:nat>()->index{return index<N>();}}
)",
                  true),
            "source.unsupported");
    // This abstract Math member schema is already refused by the source
    // checker without any Protocol/common-control traversal.
    refuses(check(R"(module m;
interface Operation {math fn number<N:nat>()->index;}
math fn inner<N:nat,C:Operation>()->index{return C::number<pow2(N)>();}
math fn outer<M:nat,C:Operation>()->index{return inner<pow2(M),C>();}
)",
                  true),
            "source.natural");
  });
  cases.run("abstract factory identity suspends checked body statics", [&] {
    auto project = take(check(R"(module m;
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
interface Operation {domain fn rows<N:nat>(n:index)->domain<index>;}
math fn calc<N:nat,C:Operation>(n:index,x:bool)->bool{return fold(C::rows<N>(n),x,fn(s,i)=>s);}
math fn inner<N:nat,C:Operation>(n:index,x:bool)->bool{return calc<pow2(N),C>(n,x);}
math fn outer<M:nat,C:Operation>(n:index,x:bool)->bool{return inner<pow2(M),C>(n,x);}
protocol Run<N:nat,C:Operation> roles(P,V)(n:index@(P,V),x:bool@(P,V))->(){
 let condition=outer<N,C>(n,x);if condition{()}else{()};return();
})",
                              true));
    auto rows = take(zkc::language::deriveCommonControlRequirements(
        project, named(project, "Run").id));
    std::set<unsigned> inputs;
    for (const auto &row : rows)
      for (const auto &component : row.components)
        inputs.insert(component.input);
    require(rows.size() == 2 && inputs == std::set<unsigned>{0, 1},
            "abstract staged factory lost its checked data dependencies");
  });
  for (bool distinct : {false, true})
    cases.run(distinct ? "distinct pure arms retain selector and both values"
                       : "equal pure arms retain only the forwarded value",
              [&] {
                auto source = std::string(R"(module m;
math fn choose<T:Type+Copy+Drop>(flag:bool,x:T,y:T)->T{return if flag{x}else{y};}
protocol Run roles(P,V)(flag:bool@(P,V),x:bool@(P,V),y:bool@(P,V))->(r:bool@(P,V)){
 let condition=choose(flag,x,)") +
                              (distinct ? "y" : "x") + R"();
 let r=if condition {true}else{false};return(r=r);
})";
                std::vector<unsigned> expected =
                    distinct ? std::vector<unsigned>{0, 1, 2}
                             : std::vector<unsigned>{1};
                rawInputs(source, expected);
                exactInputs(paired(context, source, true), expected);
              });
  for (unsigned field : {0, 1})
    cases.run(
        "generic selected tuple observes only field " + Twine(field), [&] {
          auto source = std::string(R"(module m;
math fn choose<T:Type+Copy+Drop>(flag:bool,x:T,y:T)->T{return if flag{x}else{y};}
math fn view(flag:bool,x:bool,y:bool,z:bool)->bool {
 let tuple=choose(flag,(x,y),(x,z));return tuple.)") +
                        std::to_string(field) + R"(;}
protocol Run roles(P,V)(flag:bool@(P,V),x:bool@(P,V),y:bool@(P,V),z:bool@(P,V))->(r:bool@(P,V)){
 let condition=view(flag,x,y,z);let r=if condition {true}else{false};return(r=r);
})";
          std::vector<unsigned> expected =
              field ? std::vector<unsigned>{0, 2, 3} : std::vector<unsigned>{1};
          rawInputs(source, expected);
          exactInputs(paired(context, source, true), expected);
        });
  cases.run("nested generic callbacks substitute captures and scoped formals",
            [&] {
              auto source = R"(module m;
math fn apply<A:Type+Copy+Drop,B:Type+Copy+Drop>(x:A,body:math fn(A)->B)->B{return body(x);}
math fn forward<A:Type+Copy+Drop,B:Type+Copy+Drop>(x:A,body:math fn(A)->B)->B{
 return apply(x,fn(y)=>body(y));
}
math fn choose(flag:bool,x:bool)->bool{return if flag{x}else{x};}
protocol Run roles(P,V)(flag:bool@(P,V),other:bool@(P,V))->(r:bool@(P,V)){
 let condition=forward(flag,fn(y)=>choose(y,other));
 let r=if condition {true}else{false};return(r=r);
})";
              rawInputs(source, {1});
              exactInputs(paired(context, source, true), {1});
            });
  cases.run("separate callbacks never share a formal ordinal as identity", [&] {
    auto source = R"(module m;
math fn apply(x:bool,body:math fn(bool)->bool)->bool{return body(x);}
math fn choose(flag:bool,x:bool,y:bool)->bool{return if flag{x}else{y};}
protocol Run roles(P,V)(flag:bool@(P,V),left:bool@(P,V),right:bool@(P,V))->(r:bool@(P,V)){
 let a=apply(flag,fn(y)=>left);let b=apply(flag,fn(y)=>right);
 let condition=choose(flag,a,b);let r=if condition {true}else{false};return(r=r);
})";
    rawInputs(source, {0, 1, 2});
    exactInputs(paired(context, source, true), {0, 1, 2});
  });
  for (bool protocolControl : {false, true})
    cases.run(protocolControl
                  ? "ordered equal-result branch still demands its header"
                  : "pure equal-result branch ignores an ordered selector",
              [&] {
                auto source = std::string(R"(module m;
math fn constant(flag:bool)->bool{return if flag{true}else{true};}
protocol Run roles(P,V)(seed:bool@(P,V))->(r:bool@(P,V)){
 let received=send P->V(seed);let both=@(P=seed,V=received);
 let condition=)") +
                              (protocolControl ? "if both {true}else{true}"
                                               : "constant(both)") +
                              R"(;
 let r=if condition {true}else{false};return(r=r);
})";
                if (protocolControl)
                  refuses(check(source, true), "source.common-provenance");
                else {
                  rawInputs(source, {});
                  require(paired(context, source, true).empty(),
                          "pure constant gained agreement");
                }
              });
  cases.run("generic tuple result preserves tag-only dependence", [&] {
    auto source = R"(module m;
enum Choice{Some(bool),None()}
math fn choose<T:Type+Copy+Drop>(flag:bool,x:T,y:T)->T{return if flag{x}else{y};}
protocol Run roles(P,V)(flag:bool@(P,V),choice:Choice@(P,V),a:bool@(P,V),b:bool@(P,V))->(r:bool@(P,V)){
 let tuple=choose(flag,(choice,a),(choice,b));
 let r=match tuple.0{Some(bit)=>{true},None()=>{false}};return(r=r);
})";
    rawInputs(source, {1});
    auto rows = paired(context, source, true);
    require(rows.size() == 1 && rows[0].tagOnly && !rows[0].extentAxis &&
                rows[0].components[0].source.input == 1,
            "tag projection demanded selector, sibling or payload");
  });
  for (bool distinct : {false, true})
    cases.run(
        distinct
            ? "distinct pure vector results retain exact extents and selector"
            : "generic tuple result transports only its vector extent",
        [&] {
          auto source = std::string(R"(module m;
domain Fr=field("koala-bear");type Vector<F:Field>=builtin("vector",F);
math fn extent(xs:Vector<Fr>)->index{return intrinsic<Fr>("vector.length",xs);}
math fn choose<T:Type+Copy+Drop>(flag:bool,x:T,y:T)->T{return if flag{x}else{y};}
protocol Run roles(P,V)(flag:bool@(P,V),xs:Vector<Fr>@(P,V),ys:Vector<Fr>@(P,V))->(){
 let tuple=choose(flag,(xs,true),()") +
                        (distinct ? "ys" : "xs") + R"(,false));
 let count=extent(tuple.0);for _ in 0..count roles(P,V) max 4 {}return();
})";
          std::vector<unsigned> expected = distinct
                                               ? std::vector<unsigned>{0, 1, 2}
                                               : std::vector<unsigned>{1};
          rawInputs(source, expected);
          auto rows = paired(context, source, true);
          require(rows.size() == expected.size(),
                  "extent observation count differs");
          for (const auto &row : rows)
            require(!row.tagOnly &&
                        row.extentAxis == (row.components[0].source.input == 0
                                               ? std::optional<unsigned>{}
                                               : std::optional<unsigned>{0}),
                    "extent was confused with whole-vector equality");
        });
  for (bool distinct : {false, true})
    cases.run(
        distinct
            ? "different generic natural instantiations preserve selection"
            : "identical generic natural instantiations eliminate selection",
        [&] {
          auto source = std::string(R"(module m;
math fn number<N:nat>()->index{return index<N>();}
math fn count(flag:bool)->index{return if flag{number<1>()}else{number<)") +
                        (distinct ? "2" : "1") + R"(>()};}
protocol Run roles(P,V)(flag:bool@(P,V))->(){let n=count(flag);for _ in 0..n roles(P,V) max 4 {}return();}
)";
          std::vector<unsigned> expected =
              distinct ? std::vector<unsigned>{0} : std::vector<unsigned>{};
          rawInputs(source, expected);
          exactInputs(paired(context, source, true), expected);
        });
  cases.run("domain factories retain unused constructor input dependence", [&] {
    auto source = R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
domain fn recipe(lower:index,n:index,extra:index)->domain<index>{let unused=range(lower,extra);return range(lower,n);}
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn first(n:index,extra:index,x:bool)->bool{let result=fold(recipe(0,n,extra),(x,x),fn(s,i)=>s);return result.0;}
protocol Run roles(P,V)(n:index@(P,V),extra:index@(P,V),x:bool@(P,V))->(r:bool@(P,V)){
 let condition=first(n,extra,x);let r=if condition {true}else{false};return(r=r);
})";
    rawInputs(source, {0, 1, 2});
    exactInputs(paired(context, source, true), {0, 1, 2});
  });
  cases.run("concrete module members use actual scoped and static environments",
            [&] {
              auto source = R"(module m;
interface MathOps<T:Type+Copy+Drop>{math fn run(x:T,body:math fn(T)->T)->T;}
module Impl<T:Type+Copy+Drop>:MathOps<T>{math fn run(x:T,body:math fn(T)->T)->T{return body(x);}}
math fn indirect<T:Type+Copy+Drop,C:MathOps<T>>(x:T,body:math fn(T)->T)->T{return C::run(x,body);}
protocol Run roles(P,V)(flag:bool@(P,V),other:bool@(P,V))->(r:bool@(P,V)){
 let condition=indirect<bool,Impl<bool>>(flag,fn(y)=>other);
 let r=if condition {true}else{false};return(r=r);
})";
              rawInputs(source, {1});
              exactInputs(paired(context, source, true), {1});
            });
  cases.run("real scalar power_word closure retains concrete fold state", [&] {
    auto sources = sourceProject(ZKC_SOURCE_PROJECT);
    sources.push_back({"m", R"(module m;
use zkc::scalar as scalar;domain F=field("koala-bear");
protocol Run roles(P,V)(base:F@(P,V),exponent:index@(P,V))->(r:bool@(P,V)){
 let value=scalar::power_word(base,exponent);
 let r=if value==base {true}else{false};return(r=r);
})",
                       "scalar-common.zkc"});
    auto project =
        take(analyze(take(capture(std::move(sources)))).checkedProject());
    auto raw = take(zkc::language::deriveCommonControlRequirements(
        project, named(project, "Run").id));
    require(raw.size() == 2, "real scalar raw source dependencies differ");
    exactInputs(pairedProject(context, project), {0, 1});
  });
  cases.run("nested callbacks retain actual captured domain parameters", [&] {
    auto source = R"(module m;
domain fn range(lower:index,upper:index)->domain<index> = domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S = finite("math.fold");
math fn apply(x:bool,body:math fn(bool)->bool)->bool{return body(x);}
math fn first(rows:domain<index>,x:bool)->bool{
 return apply(x,fn(seed)=>{let result=fold(rows,(seed,seed),fn(s,i)=>s);result.0});
}
protocol Run roles(P,V)(n:index@(P,V),x:bool@(P,V))->(r:bool@(P,V)){
 let condition=first(range(0,n),x);let r=if condition {true}else{false};return(r=r);
})";
    rawInputs(source, {0, 1});
    exactInputs(paired(context, source, true), {0, 1});
  });
  cases.run("finite predicates retain independently captured data", [&] {
    auto source = R"(module m;
domain fn range(lower:index,upper:index)->domain<index> = domain("range");
math fn fold_where<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,keep:math fn(item:I)->bool where item_from(item,rows),step:math fn(S,item:I)->S where item_from(item,rows))->S = finite("math.fold_where");
math fn first(n:index,keep:bool,x:bool)->bool{
 let result=fold_where(range(0,n),(x,x),fn(i)=>keep,fn(s,i)=>s);return result.0;
}
protocol Run roles(P,V)(n:index@(P,V),keep:bool@(P,V),x:bool@(P,V))->(r:bool@(P,V)){
 let condition=first(n,keep,x);let r=if condition {true}else{false};return(r=r);
})";
    rawInputs(source, {0, 1, 2});
    exactInputs(paired(context, source, true), {0, 1, 2});
  });
  for (bool demanded : {false, true})
    cases.run(demanded ? "actual scoped capture cannot hide received provenance"
                       : "unused received scoped capture creates no obligation",
              [&] {
                auto source = std::string(R"(module m;
math fn apply(x:bool,body:math fn(bool)->bool)->bool{return body(x);}
protocol Run roles(P,V)(flag:bool@(P,V),seed:bool@(P,V))->(r:bool@(P,V)){
 let received=send P->V(seed);let both=@(P=seed,V=received);
 let condition=apply(flag,fn(y)=>)") +
                              (demanded ? "both" : "{let ignored=both;true}") +
                              R"();
 let r=if condition {true}else{false};return(r=r);
})";
                if (demanded)
                  refuses(check(source, true), "source.common-provenance");
                else {
                  rawInputs(source, {});
                  require(paired(context, source, true).empty(),
                          "unused captured data was demanded");
                }
              });
  for (bool demanded : {false, true})
    cases.run(
        demanded
            ? "generic domain contracts transport exact argument provenance"
            : "unused generic domain factories remain well formed",
        [&] {
          auto source = std::string(R"(module m;
domain fn range(lower:index,upper:index)->domain<index> = domain("range");
interface Domains {domain fn rows(n:index)->domain<index>;}
module Direct:Domains {domain fn rows(n:index)->domain<index>{return range(n,n);}}
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S = finite("math.fold");
math fn evaluate<C:Domains>(n:index)->bool {let value=fold(C::rows(n),true,fn(s,i)=>s);return )") +
                        (demanded ? "value" : "true") + R"(;}
protocol Generic<C:Domains> roles(P,V)(n:index@(P,V))->(r:bool@(P,V)){
 let condition=evaluate<C>(n);let r=if condition {true}else{false};return(r=r);
}
protocol Run roles(P,V)(n:index@(P,V))->(r:bool@(P,V)){
 let r=Generic<Direct> roles(P,V)(n);return(r=r);
})";
          std::vector<unsigned> expected =
              demanded ? std::vector<unsigned>{0} : std::vector<unsigned>{};
          auto project = take(check(source, true));
          auto generic = take(zkc::language::deriveCommonControlRequirements(
              project, named(project, "Generic").id));
          require(
              generic.size() == expected.size(),
              "abstract domain contract lost its ordinary input dependence");
          for (const auto &row : generic)
            require(row.type.kind == Type::Kind::Index && !row.tagOnly &&
                        !row.extentAxis && row.components.size() == 2 &&
                        row.components[0].input == 0 &&
                        row.components[1].input == 0 &&
                        row.components[0].role == 0 &&
                        row.components[1].role == 1 &&
                        row.components[0].path.empty() &&
                        row.components[1].path.empty(),
                    "abstract domain contract observation differs");
          rawInputs(source, expected);
          exactInputs(paired(context, source, true), expected);
        });
  cases.run(
      "symbolic fixed-array projection retains its exact source path", [&] {
        auto project = take(check(arrayProtocol(), true));
        const auto &decl = named(project, "Run");
        require(decl.bounds.size() == 1 &&
                    decl.bounds[0].lhs == Natural::constant(2) &&
                    decl.bounds[0].rhs == decl.inputs[0].type.dimension,
                "source checker lost the projection's inferred natural bound");
        auto rows = take(
            zkc::language::deriveCommonControlRequirements(project, decl.id));
        require(rows.size() == 1 && rows[0].type.kind == Type::Kind::Boolean &&
                    !rows[0].tagOnly && !rows[0].extentAxis &&
                    rows[0].components.size() == 2,
                "symbolic projection observation differs");
        for (unsigned role = 0; role < 2; ++role) {
          const auto &component = rows[0].components[role];
          require(component.input == 0 && component.role == role &&
                      component.path.size() == 1 &&
                      component.path[0].kind ==
                          CommonControlStep::Kind::Field &&
                      component.path[0].index == 1,
                  "symbolic array component path differs");
        }
        auto entry =
            take(closeNativeRun(project, "m::Run", {}, {naturalArgument(3)}));
        auto mapped = pairedEntry(context, entry);
        require(mapped.size() == 1, "closed projected array inventory differs");
        for (const auto &component : mapped[0].components)
          require(
              component.source.input == 0 && component.originalInput == 1 &&
                  component.participantInput == 1 && component.path.empty() &&
                  component.source.path == rows[0].components[0].path,
              "closed array element was not mapped to its actual native port");
        for (uint64_t n : {0, 1})
          refuses(closeNativeRun(project, "m::Run", {}, {naturalArgument(n)}),
                  "source.bound");
      });
  cases.run("one callable level admits nested protocol control regions", [&] {
    Limits limits;
    limits.callDepth = 1;
    auto project = take(check(nestedProtocol(), true, limits));
    auto rows = take(zkc::language::deriveCommonControlRequirements(
        project, named(project, "Run").id, limits));
    require(rows.size() == 2, "nested control dependencies differ");
    auto entry = take(closeNativeRun(project, "m::Run", limits));
    exactInputs(take(deriveNativeCommonControlRequirements(entry, limits)),
                {0, 1});
    // Common-control limits are checked above. The original/correspondence
    // validators have their own independently bounded traversal.
    exactInputs(pairedEntry(context, entry), {0, 1});
    limits.expressionDepth = 1;
    refuses(zkc::language::deriveCommonControlRequirements(
                project, named(project, "Run").id, limits),
            "source.limit");
  });
  cases.run(
      "generic selected Host array example retains its checked bound", [&] {
        auto project = take(check(R"(module m;
interface Algebra {fn identity(value:index)->index effects();}
module Identity:Algebra {fn identity(value:index)->index{return value;}}
protocol Work<M:Algebra,N:nat> roles(P)(values:[index;N]@P)->(out:index@P){
 return M::identity(values[0]);
})",
                                  true));
        const auto &work = named(project, "Work");
        require(work.bounds.size() == 1 &&
                    work.bounds[0].lhs == Natural::constant(1) &&
                    work.bounds[0].rhs == work.inputs[0].type.dimension,
                "generic Host projection lost its target natural requirement");
        auto positional = take(closeEntry(project, "m::Work<Identity,1+2>"));
        auto namedEntry = take(closeEntry(project, "m::Work<N=3,M=Identity>"));
        require(positional.root().symbol == namedEntry.root().symbol &&
                    positional.invocations().size() == 1 &&
                    namedEntry.invocations().size() == 1 &&
                    positional.root().body->stage == Body::Stage::Host,
                "selected generic Host closure changed its source arguments");
        auto entry =
            take(closeProtocolDeployment(project, "m::Work<Identity,3>"));
        require(pairedEntry(context, entry).empty(),
                "role-local Host acquired common inputs");
        refuses(closeEntry(project, "m::Work<Identity,0>"), "source.bound");
      });
  cases.run("nested generic arrays preserve every projection coordinate", [&] {
    auto project = take(check(R"(module m;
protocol Run<N:nat> roles(P,V)(xs:[[bool;N];2]@(P,V))->(r:bool@(P,V)){
 let flag=xs[1][1];let r=if flag {true}else{false};return(r=r);
})",
                              true));
    auto raw = take(zkc::language::deriveCommonControlRequirements(
        project, named(project, "Run").id));
    require(raw.size() == 1 && raw[0].components[0].path.size() == 2 &&
                raw[0].components[0].path[0].index == 1 &&
                raw[0].components[0].path[1].index == 1,
            "nested array path was truncated");
    auto entry =
        take(closeNativeRun(project, "m::Run", {}, {naturalArgument(3)}));
    auto rows = pairedEntry(context, entry);
    require(rows.size() == 1 && rows[0].components[0].originalInput == 4 &&
                rows[0].components[1].originalInput == 4,
            "nested array did not flatten to the exact fourth port");
  });
  cases.run(
      "projected array variants retain separate tag and payload paths", [&] {
        auto project = take(check(R"(module m;
enum Choice {Some(bool),None()}
protocol Run<N:nat> roles(P,V)(xs:[Choice;N]@(P,V))->(r:bool@(P,V)){
 let r=match xs[1]{Some(bit)=>{if bit {true}else{false}},None()=>{false}};return(r=r);
})",
                                  true));
        auto entry =
            take(closeNativeRun(project, "m::Run", {}, {naturalArgument(3)}));
        auto rows = pairedEntry(context, entry);
        require(rows.size() == 2, "array variant lost an observation");
        for (const auto &row : rows)
          for (const auto &component : row.components) {
            require(component.originalInput == 1 &&
                        component.source.path[0].kind ==
                            CommonControlStep::Kind::Field &&
                        component.source.path[0].index == 1 && !row.extentAxis,
                    "variant array element association differs");
            require(component.path == (row.tagOnly
                                           ? std::vector<unsigned>{}
                                           : std::vector<unsigned>{0, 0}),
                    "variant payload was confused with a flat array element");
          }
      });
  cases.run("closed zero and out-of-range array reads remain invalid", [&] {
    refuses(check(arrayProtocol("0", 0), true), "source.index");
    refuses(check(arrayProtocol("2", 2), true), "source.index");
    refuses(check(arrayProtocol("2", 0xffffffffu), true), "source.index");
  });
  for (bool zero : {false, true})
    cases.run(
        zero ? "defensive closed zero projection refuses in direct derivation"
             : "defensive closed invalid index refuses in direct derivation",
        [&] {
          auto project = take(check(arrayProtocol("2", 0), true));
          auto &decl = const_cast<Declaration &>(named(project, "Run"));
          auto candidate = std::make_shared<Body>(*decl.body);
          if (zero) {
            decl.inputs[0].type.dimension = Natural::constant(0);
            candidate->values[0].type.dimension = Natural::constant(0);
          } else {
            bool changed = false;
            for (auto &op : candidate->operations)
              if (auto *projection = std::get_if<Projection>(&op.action)) {
                projection->path[0] = 2;
                changed = true;
                break;
              }
            require(changed, "missing actual checked array projection");
          }
          decl.body = std::move(candidate);
          refuses(
              zkc::language::deriveCommonControlRequirements(project, decl.id),
              "source.common-provenance");
        });
  cases.run(
      "maximum array observation has bounded dimension-independent work", [&] {
        auto cost = [&](unsigned length) {
          auto project =
              take(check(arrayProtocol(std::to_string(length), 1), true));
          auto target = named(project, "Run").id;
          Limits limits;
          limits.aggregateLeaves = 2;
          auto rows = take(zkc::language::deriveCommonControlRequirements(
              project, target, limits));
          require(rows.size() == 1 && rows[0].components[0].path[0].index == 1,
                  "one array observation expanded its whole source layout");
          uint64_t low = 0, high = limits.work;
          while (low < high) {
            limits.work = low + (high - low) / 2;
            auto result = zkc::language::deriveCommonControlRequirements(
                project, target, limits);
            if (result)
              high = limits.work;
            else {
              require(
                  namesIdentifier(toString(result.takeError()), "source.limit"),
                  "array work refusal changed identifier");
              low = limits.work + 1;
            }
          }
          limits.work = low;
          require(take(zkc::language::deriveCommonControlRequirements(
                           project, target, limits))
                          .size() == 1,
                  "exact array observation budget failed");
          --limits.work;
          refuses(zkc::language::deriveCommonControlRequirements(
                      project, target, limits),
                  "source.limit");
          return low;
        };
        auto small = cost(2), maximum = cost(1024);
        require(small == maximum,
                "projection work grows with an unobserved array dimension");
        outs() << "array observation exact work boundary: " << maximum << '\n';
        refuses(check(arrayProtocol("1000000", 1), true), "source.limit");
      });
  cases.run("closed inventory still enforces array layout capacity", [&] {
    auto project = take(check(arrayProtocol("4", 1), true));
    auto entry = take(closeNativeRun(project, "m::Run"));
    Limits limits;
    limits.aggregateLeaves = 2;
    require(take(zkc::language::deriveCommonControlRequirements(entry, limits))
                    .size() == 1,
            "one observed element required a whole interface layout");
    refuses(deriveNativeCommonControlRequirements(entry, limits),
            "source.limit");
  });
  cases.run(
      "actual array operand mutation changes native inventory and refuses "
      "correspondence",
      [&] {
        auto project = take(check(arrayProtocol(), true));
        auto entry =
            take(closeNativeRun(project, "m::Run", {}, {naturalArgument(3)}));
        auto mapped = pairedEntry(context, entry);
        auto bytes = take(emitOriginal(entry, context));
        auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
        require(bool(module), "array original did not parse");
        auto root = nativeProtocol(*module, entry.protocol().symbol);
        protocol_ir::BranchOp branch;
        root.walk([&](protocol_ir::BranchOp op) { branch = op; });
        require(bool(branch), "array original omitted its actual branch");
        branch->setOperand(0, root.getBody().front().getArgument(0));
        require(mlir::succeeded(admitStage(*module)),
                "equal-typed mutation did not reach independent comparison");
        uint64_t remaining = 8000000;
        facts::Work work(remaining);
        auto native = take(zkc::deriveCommonControlRequirements(root, work));
        require(
            native.size() == 1 && native[0].components[0].input == 0 &&
                mapped.size() == 1 &&
                mapped[0].components[0].originalInput == 1,
            "mutated candidate retained a stale array requirement inventory");
        refuses(compareOriginal(entry, *module), "source.correspondence");
      });
  cases.run("actual helper calls retain their callable depth boundary", [&] {
    auto project = take(check(R"(module m;
math fn inner(x:bool)->bool{return x;}
math fn outer(x:bool)->bool{return inner(x);}
protocol Run roles(P,V)(flag:bool@(P,V))->(r:bool@(P,V)){
 let condition=outer(flag);let r=if condition {true}else{false};return(r=r);
})",
                              true));
    auto target = named(project, "Run").id;
    Limits limits;
    limits.callDepth = 2;
    refuses(
        zkc::language::deriveCommonControlRequirements(project, target, limits),
        "source.limit");
    limits.callDepth = 3;
    require(take(zkc::language::deriveCommonControlRequirements(project, target,
                                                                limits))
                    .size() == 1,
            "exact helper call boundary changed obligations");
    exactInputs(pairedProject(context, project), {0});
  });
  cases.run("actual Protocol calls retain their callable depth boundary", [&] {
    auto project = take(check(R"(module m;
protocol Child roles(A,B)(flag:bool@(A,B))->(r:bool@(A,B)){
 let r=if flag {true}else{false};return(r=r);
}
protocol Run roles(P,V)(flag:bool@(P,V))->(r:bool@(P,V)){
 let r=Child roles(P,V)(flag);return(r=r);
})",
                              true));
    auto target = named(project, "Run").id;
    Limits limits;
    limits.callDepth = 1;
    refuses(
        zkc::language::deriveCommonControlRequirements(project, target, limits),
        "source.limit");
    limits.callDepth = 2;
    require(take(zkc::language::deriveCommonControlRequirements(project, target,
                                                                limits))
                    .size() == 1,
            "exact Protocol call boundary changed obligations");
    exactInputs(pairedProject(context, project), {0});
  });
  cases.run("actual scoped invocations retain their callable depth boundary",
            [&] {
              auto project = take(check(R"(module m;
math fn apply(x:bool,body:math fn(bool)->bool)->bool{return body(x);}
protocol Run roles(P,V)(flag:bool@(P,V))->(r:bool@(P,V)){
 let condition=apply(flag,fn(y)=>y);let r=if condition {true}else{false};return(r=r);
})",
                                        true));
              auto target = named(project, "Run").id;
              Limits limits;
              limits.callDepth = 2;
              refuses(zkc::language::deriveCommonControlRequirements(
                          project, target, limits),
                      "source.limit");
              limits.callDepth = 3;
              require(take(zkc::language::deriveCommonControlRequirements(
                               project, target, limits))
                              .size() == 1,
                      "exact scoped call boundary changed obligations");
              exactInputs(pairedProject(context, project), {0});
            });
  cases.run("calls inside nested regions use call and structural budgets "
            "independently",
            [&] {
              auto project = take(check(R"(module m;
math fn identity(x:bool)->bool{return x;}
protocol Run roles(P,V)(n:index@(P,V),flag:bool@(P,V))->(){
 for _ in 0..n roles(P,V) max 2 {
  for _ in 0..n roles(P,V) max 2 {
   let condition=identity(flag);if condition {()}else{()}
  }
 }
 return();
})",
                                        true));
              auto target = named(project, "Run").id;
              Limits limits;
              limits.callDepth = 1;
              refuses(zkc::language::deriveCommonControlRequirements(
                          project, target, limits),
                      "source.limit");
              limits.callDepth = 2;
              require(take(zkc::language::deriveCommonControlRequirements(
                               project, target, limits))
                              .size() == 2,
                      "nested regions consumed callable depth");
              limits.expressionDepth = 2;
              refuses(zkc::language::deriveCommonControlRequirements(
                          project, target, limits),
                      "source.limit");
              exactInputs(pairedProject(context, project), {0, 1});
            });
  cases.run("zero callable allowance still refuses an otherwise flat body",
            [&] {
              auto project = take(check(R"(module m;
protocol Run roles(P,V)(flag:bool@(P,V))->(r:bool@(P,V)){
 let r=if flag {true}else{false};return(r=r);
})",
                                        true));
              Limits limits;
              limits.callDepth = 0;
              refuses(zkc::language::deriveCommonControlRequirements(
                          project, named(project, "Run").id, limits),
                      "source.limit");
            });
  cases.run(
      "projected array collections observe extent independently of values",
      [&] {
        auto project = take(check(R"(module m;
domain Fr=field("koala-bear");type Vector<F:Field>=builtin("vector",F);
math fn extent(xs:Vector<Fr>)->index{return intrinsic<Fr>("vector.length",xs);}
protocol Run<N:nat> roles(P,V)(xs:[Vector<Fr>;N]@(P,V))->(){
 let count=extent(xs[1]);for _ in 0..count roles(P,V) max 4 {}return();
})",
                                  true));
        auto entry =
            take(closeNativeRun(project, "m::Run", {}, {naturalArgument(3)}));
        auto rows = pairedEntry(context, entry);
        require(rows.size() == 1 && !rows[0].tagOnly && rows[0].extentAxis == 0,
                "projected collection gained whole-value obligations");
        for (const auto &component : rows[0].components)
          require(component.originalInput == 1 && component.path.empty() &&
                      component.source.path.size() == 1 &&
                      component.source.path[0].kind ==
                          CommonControlStep::Kind::Field &&
                      component.source.path[0].index == 1,
                  "collection extent lost the selected array element");
      });
  cases.run("projected array tuples observe only the selected field", [&] {
    auto project = take(check(R"(module m;
protocol Run<N:nat> roles(P,V)(xs:[(index,bool);N]@(P,V))->(r:bool@(P,V)){
 let flag=xs[1].1;let r=if flag {true}else{false};return(r=r);
})",
                              true));
    auto entry =
        take(closeNativeRun(project, "m::Run", {}, {naturalArgument(3)}));
    auto rows = pairedEntry(context, entry);
    require(rows.size() == 1 && !rows[0].tagOnly && !rows[0].extentAxis,
            "tuple array observation differs");
    for (const auto &component : rows[0].components)
      require(component.originalInput == 3 && component.path.empty() &&
                  component.source.path.size() == 2 &&
                  component.source.path[0].index == 1 &&
                  component.source.path[1].index == 1,
              "array tuple sibling leaked into the input inventory");
  });
  cases.run(
      "symbolic array access still requires its source natural premise", [&] {
        refuses(check(R"(module m;
protocol Run<N:nat> roles(P,V)(xs:[bool;N]@(P,V))->(r:bool@(P,V)) where () {
 let flag=xs[1];let r=if flag {true}else{false};return(r=r);
})",
                      true),
                "source.bound");
        auto project = take(check(R"(module m;
protocol Run<N:nat> roles(P,V)(xs:[bool;N]@(P,V))->(r:bool@(P,V)) where 2<=N {
 let flag=xs[1];let r=if flag {true}else{false};return(r=r);
})",
                                  true));
        auto entry =
            take(closeNativeRun(project, "m::Run", {}, {naturalArgument(3)}));
        auto rows = pairedEntry(context, entry);
        require(rows.size() == 1 && rows[0].components[0].originalInput == 1,
                "declared array premise changed the demanded component");
        refuses(closeNativeRun(project, "m::Run", {}, {naturalArgument(1)}),
                "source.bound");
      });
  for (bool demanded : {false, true})
    cases.run(
        demanded ? "staged helper statics retain demanded common data"
                 : "unused staged helper statics admit two-role bodies",
        [&] {
          std::string source = R"(module m;
math fn ignore<N:nat>(x:bool)->bool{return x;}
math fn inner<N:nat>(x:bool)->bool{return ignore<pow2(N)>(x);}
math fn outer<M:nat>(x:bool)->bool{return inner<pow2(M)>(x);}
protocol Run<M:nat> roles(P,V)(flag:bool@(P,V))->(r:bool@(P,V)){
 let condition=outer<M>(flag);
)";
          source += demanded
                        ? "let r=if condition {true}else{false};return(r=r);}"
                        : "return(r=condition);}";
          auto project = take(check(source, true));
          auto raw = take(zkc::language::deriveCommonControlRequirements(
              project, named(project, "Run").id));
          require(raw.size() == unsigned(demanded),
                  "staged call changed common input demand");
          auto entry =
              take(closeNativeRun(project, "m::Run", {}, {naturalArgument(5)}));
          auto mapped = pairedEntry(context, entry);
          if (demanded)
            exactInputs(mapped, {0});
          else
            require(mapped.empty(), "unused result acquired a common premise");
          refuses(closeNativeRun(project, "m::Run", {}, {naturalArgument(6)}),
                  "source.natural");
        });
  cases.run("staged helper traversal does not equate received data", [&] {
    refuses(check(R"(module m;
math fn ignore<N:nat>(x:bool)->bool{return x;}
math fn inner<N:nat>(x:bool)->bool{return ignore<pow2(N)>(x);}
math fn outer<M:nat>(x:bool)->bool{return inner<pow2(M)>(x);}
protocol Run<M:nat> roles(P,V)(flag:bool@(P,V))->(){
 let received=send P->V(flag);
 let shared=@(P=flag,V=received);
 let condition=outer<M>(shared);
 if condition {()}else{()};return();
})",
                  true),
            "source.common-provenance");
  });
  cases.run("staged environments substitute demanded array shapes", [&] {
    auto project = take(check(R"(module m;
math fn head<N:nat>(xs:[bool;N])->bool{return xs[0];}
math fn inner<N:nat>(xs:[bool;pow2(N)])->bool{return head<pow2(N)>(xs);}
math fn outer<M:nat>(xs:[bool;pow2(M+1)])->bool{return inner<M+1>(xs);}
protocol Run<M:nat> roles(P,V)(xs:[bool;pow2(M+1)]@(P,V))->(r:bool@(P,V)){
 let condition=outer<M>(xs);let r=if condition {true}else{false};return(r=r);
})",
                              true));
    auto raw = take(zkc::language::deriveCommonControlRequirements(
        project, named(project, "Run").id));
    require(raw.size() == 1 && raw[0].components[0].path.size() == 1 &&
                raw[0].components[0].path[0].index == 0,
            "demanded shape lost its exact source element");
    auto entry =
        take(closeNativeRun(project, "m::Run", {}, {naturalArgument(1)}));
    auto mapped = pairedEntry(context, entry);
    require(mapped.size() == 1 && mapped[0].components.size() == 2,
            "demanded array shape changed the common inventory");
    for (const auto &component : mapped[0].components)
      require(component.source.input == 0 && component.originalInput == 0 &&
                  component.participantInput == 0 && component.path.empty() &&
                  component.source.path == raw[0].components[0].path,
              "demanded array shape lost its exact native element");
  });
  for (bool shared : {false, true})
    for (bool demanded : {false, true})
      for (unsigned actual : {0, 5, 6})
        cases.run("demanded static stages " + std::to_string(actual) +
                      (shared ? " shared" : " single role") +
                      (demanded ? " observed" : " unused result"),
                  [&] {
                    auto source = std::string(R"(module m;
math fn number<N:nat>()->index{return index<N>();}
math fn inner<N:nat>()->index{return number<pow2(N)>();}
math fn outer<M:nat>()->index{return inner<pow2(M)>();}
protocol Run roles()") + (shared ? "P,V" : "P") +
                                  ")()->(){let n=outer<" +
                                  std::to_string(actual) + ">();";
                    if (demanded)
                      source += std::string("for _ in 0..n roles(") +
                                (shared ? "P,V" : "P") + ") max 4 {}";
                    source += "return();}";
                    if (actual == 6) {
                      refuses(check(source, true), "source.natural");
                      return;
                    }
                    auto project = take(check(source, true));
                    require(take(zkc::language::deriveCommonControlRequirements(
                                     project, named(project, "Run").id))
                                .empty(),
                            "closed static count acquired input obligations");
                    auto entry = take(closeNativeRun(project, "m::Run"));
                    require(take(zkc::language::deriveCommonControlRequirements(
                                     entry))
                                .empty(),
                            "closed static stages changed requirements");
                  });
  for (bool distinct : {false, true})
    for (bool receivedSelector : {false, true})
      cases.run(
          std::string("finite callback lexical statics ") +
              (distinct ? "differ" : "agree through relay") +
              (receivedSelector ? " with received selector"
                                : " with input selector"),
          [&] {
            auto source = std::string(R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn calc<N:nat>(x:bool)->bool{return fold(range(0,1),x,fn(s,i)=>if index<N>()==index<1>(){s}else{false});}
math fn relay<M:nat>(x:bool)->bool{return calc<M>(x);}
math fn choose(flag:bool,x:bool)->bool{return if flag{calc<1>(x)}else{relay<)") +
                          (distinct ? "2" : "1") + R"(>(x)};}
protocol Run roles(P,V)(flag:bool@(P,V),x:bool@(P,V))->(){
)";
            if (receivedSelector)
              source +=
                  "let received=send P->V(flag);let both=@(P=flag,V=received);";
            source += std::string("let condition=choose(") +
                      (receivedSelector ? "both" : "flag") +
                      ",x);if condition {()}else{()};return();}";
            if (distinct && receivedSelector) {
              refuses(check(source, true), "source.common-provenance");
              return;
            }
            auto expected = distinct ? std::vector<unsigned>{0, 1}
                                     : std::vector<unsigned>{1};
            rawInputs(source, expected);
            exactInputs(paired(context, source, true), expected);
          });
  for (StringRef difference :
       {"same", "data", "scoped", "domain", "module", "body"})
    cases.run("finite callback lexical bindings preserve " + difference, [&] {
      auto source = std::string(R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
interface Operation{math fn apply(x:bool)->bool;}
module Direct:Operation{math fn apply(x:bool)->bool{return x;}}
module Inverted:Operation{math fn apply(x:bool)->bool{return !x;}}
math fn calc<N:nat,C:Operation>(rows:domain<index>,x:bool,cap:bool,step:math fn(bool)->bool)->bool{
 return fold(range(0,1),x,fn(s,i)=>{let value=fold(rows,s,fn(t,j)=>t);if index<N>()==index<1>(){C::apply(step(value))}else{cap}});
}
math fn alternate<N:nat,C:Operation>(rows:domain<index>,x:bool,cap:bool,step:math fn(bool)->bool)->bool{
 return fold(range(0,1),x,fn(s,i)=>{let value=fold(rows,s,fn(t,j)=>t);if index<N>()==index<1>(){C::apply(step(value))}else{!cap}});
}
math fn relay<M:nat,C:Operation>(rows:domain<index>,x:bool,cap:bool,step:math fn(bool)->bool)->bool{return calc<M,C>(rows,x,cap,step);}
math fn choose(flag:bool,x:bool,cap:bool,other:bool,n:index,m:index,identity:math fn(bool)->bool)->bool{
 return if flag{calc<1,Direct>(range(0,n),x,cap,identity)}else{)");
      source += difference == "body" ? "alternate" : "relay";
      source += std::string("<1,") +
                (difference == "module" ? "Inverted" : "Direct") +
                ">(range(0," + (difference == "domain" ? "m" : "n") + "),x," +
                (difference == "data" ? "other" : "cap") + "," +
                (difference == "scoped" ? "fn(y)=>!y" : "identity") + R"()};
}
protocol Run roles(P,V)(flag:bool@(P,V),x:bool@(P,V),cap:bool@(P,V),other:bool@(P,V),n:index@(P,V),m:index@(P,V))->(){
 let condition=choose(flag,x,cap,other,n,m,fn(y)=>y);if condition {()}else{()};return();
})";
      std::vector<unsigned> expected{1, 2, 4};
      if (difference != "same")
        expected.insert(expected.begin(), 0);
      if (difference == "data")
        expected.insert(expected.end() - 1, 3);
      if (difference == "domain")
        expected.push_back(5);
      rawInputs(source, expected);
      exactInputs(paired(context, source, true), expected);
      source = replaceText(
          source, "let condition=choose(flag,x,cap,other,n,m,fn(y)=>y);",
          "let received=send P->V(flag);let both=@(P=flag,V=received);let "
          "condition=choose(both,x,cap,other,n,m,fn(y)=>y);");
      if (difference == "same") {
        rawInputs(source, expected);
        exactInputs(paired(context, source, true), expected);
      } else
        refuses(check(source, true), "source.common-provenance");
    });
  cases.run("finite callback identity closes nested static actuals in stages",
            [&] {
              auto source = R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn calc<N:nat>(x:bool)->bool{return fold(range(0,1),x,fn(s,i)=>if index<N>()==index<1>(){s}else{false});}
math fn relay<M:nat>(x:bool)->bool{return calc<pow2(M)>(x);}
math fn outer<K:nat>(x:bool)->bool{return relay<pow2(K)>(x);}
math fn choose(flag:bool,x:bool)->bool{return if flag{calc<4294967296>(x)}else{outer<5>(x)};}
protocol Run roles(P,V)(flag:bool@(P,V),x:bool@(P,V))->(){
 let received=send P->V(flag);let both=@(P=flag,V=received);
 let condition=choose(both,x);if condition {()}else{()};return();
})";
              rawInputs(source, {1});
              exactInputs(paired(context, source, true), {1});
            });
  cases.run(
      "demanded lexical statics retain work and callable depth bounds", [&] {
        auto project = take(check(R"(module m;
math fn number<N:nat>()->index{return index<N>();}
math fn inner<N:nat>()->index{return number<pow2(N)>();}
math fn outer<M:nat>()->index{return inner<pow2(M)>();}
protocol Run roles(P,V)()->(){let n=outer<5>();for _ in 0..n roles(P,V) max 4 {}return();}
)",
                                  true));
        auto target = named(project, "Run").id;
        Limits limits;
        limits.callDepth = 3;
        refuses(zkc::language::deriveCommonControlRequirements(project, target,
                                                               limits),
                "source.limit");
        limits.callDepth = 4;
        require(take(zkc::language::deriveCommonControlRequirements(
                         project, target, limits))
                    .empty(),
                "exact demanded-static call depth changed obligations");
        uint64_t low = 1, high = limits.work;
        while (low < high) {
          limits.work = low + (high - low) / 2;
          auto result = zkc::language::deriveCommonControlRequirements(
              project, target, limits);
          if (result)
            high = limits.work;
          else {
            require(
                namesIdentifier(toString(result.takeError()), "source.limit"),
                "static work refusal changed identifier");
            low = limits.work + 1;
          }
        }
        limits.work = low;
        require(take(zkc::language::deriveCommonControlRequirements(
                         project, target, limits))
                    .empty(),
                "exact demanded-static work allowance failed");
        --limits.work;
        refuses(zkc::language::deriveCommonControlRequirements(project, target,
                                                               limits),
                "source.limit");
      });
  cases.run("finite callbacks retain unused staged generic statics", [&] {
    auto project = take(check(R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn ignore<N:nat>(x:bool)->bool{return fold(range(0,1),x,fn(s,i)=>s);}
math fn inner<N:nat>(x:bool)->bool{return ignore<pow2(N)>(x);}
math fn outer<M:nat>(x:bool)->bool{return inner<pow2(M)>(x);}
protocol Run<M:nat> roles(P,V)(flag:bool@(P,V))->(){
 let condition=outer<M>(flag);if condition {()}else{()};return();
})",
                              true));
    auto rows = take(zkc::language::deriveCommonControlRequirements(
        project, named(project, "Run").id));
    require(rows.size() == 1 && rows[0].components[0].input == 0,
            "unused callback static changed its data dependency");
    exactInputs(
        pairedEntry(context, take(closeNativeRun(project, "m::Run", {},
                                                 {naturalArgument(5)}))),
        {0});
    refuses(closeNativeRun(project, "m::Run", {}, {naturalArgument(6)}),
            "source.natural");
  });
  cases.run("generic callback aliases ignore irrelevant caller statics", [&] {
    auto source = R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn calc<N:nat>(x:bool)->bool{return fold(range(0,1),x,fn(s,i)=>s);}
math fn relay<M:nat,Unused:nat>(x:bool)->bool{return calc<M>(x);}
math fn choose<N:nat>(flag:bool,x:bool)->bool{return if flag{calc<N>(x)}else{relay<N,17>(x)};}
protocol Run<N:nat> roles(P,V)(flag:bool@(P,V),x:bool@(P,V))->(){
 let received=send P->V(flag);let both=@(P=flag,V=received);
 let condition=choose<N>(both,x);if condition {()}else{()};return();
})";
    rawInputs(source, {1});
    auto project = take(check(source, true));
    exactInputs(
        pairedEntry(context, take(closeNativeRun(project, "m::Run", {},
                                                 {naturalArgument(5)}))),
        {1});
  });
  cases.run(
      "generic callback powers compare their defining lexical atoms", [&] {
        auto source = R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn calc<N:nat>(x:bool)->bool{return fold(range(0,1),x,fn(s,i)=>s);}
math fn relay<M:nat>(x:bool)->bool{return calc<pow2(M)>(x);}
math fn choose<N:nat>(flag:bool,x:bool)->bool{return if flag{calc<pow2(N)>(x)}else{relay<N>(x)};}
protocol Run<N:nat> roles(P,V)(flag:bool@(P,V),x:bool@(P,V))->(){
 let received=send P->V(flag);let both=@(P=flag,V=received);
 let condition=choose<N>(both,x);if condition {()}else{()};return();
})";
        rawInputs(source, {1});
        auto project = take(check(source, true));
        exactInputs(
            pairedEntry(context, take(closeNativeRun(project, "m::Run", {},
                                                     {naturalArgument(5)}))),
            {1});
      });
  cases.run(
      "generic callback polynomials compare lexical monomial multisets", [&] {
        auto source = R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn calc<N:nat>(x:bool)->bool{return fold(range(0,1),x,fn(s,i)=>s);}
math fn relay<A:nat,B:nat>(x:bool)->bool{return calc<pow2(A)+pow2(B)>(x);}
math fn choose<N:nat,M:nat>(flag:bool,x:bool)->bool{return if flag{calc<pow2(N)+pow2(M)>(x)}else{relay<N,M>(x)};}
protocol Run<N:nat,M:nat> roles(P,V)(flag:bool@(P,V),x:bool@(P,V))->(){
 let received=send P->V(flag);let both=@(P=flag,V=received);
 let condition=choose<N,M>(both,x);if condition {()}else{()};return();
})";
        rawInputs(source, {1});
        auto project = take(check(source, true));
        exactInputs(
            pairedEntry(context, take(closeNativeRun(project, "m::Run", {},
                                                     {naturalArgument(5),
                                                      naturalArgument(1)}))),
            {1});
      });
  return cases.result();
}
