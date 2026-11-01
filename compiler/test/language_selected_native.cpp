#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/ApplicationMap.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/SourceCorrespondence.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/BindingTypes.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Language/CommonControl.h"
#include "zkc/Language/Names.h"
#if __has_include("zkc/Analysis/CommonControl.h")
#include "zkc/Analysis/CommonControl.h"
#define ZKC_HAS_NATIVE_COMMON_CONTROL 1
#endif
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject check(StringRef source, bool legacy = false) {
  CaptureOptions options;
  options.format = legacy ? "zkc" : "zkc-layout";
  return take(analyze(take(capture({{"m", source.str(), "selected-native.zkc"}},
                                   options)))
                  .checkedProject());
}
std::string fixture(StringRef name) {
  auto file = MemoryBuffer::getFile(std::string(ZKC_SELECTED_CONTROL_FIXTURES) +
                                    "/" + name.str() + ".zkc");
  require(bool(file), "missing selected source fixture");
  return (*file)->getBuffer().str();
}
mlir::Operation *branch(mlir::ModuleOp module) {
  mlir::Operation *result = nullptr;
  module.walk([&](mlir::Operation *op) {
    if (op->getName().getStringRef() == "protocol.branch")
      result = op;
  });
  require(result, "missing actual Protocol selected region");
  return result;
}
} // namespace
int main() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  if (!context.isOperationRegistered("protocol.branch") ||
      !context.isOperationRegistered("data.branch")) {
    auto entry = take(closeSubject(check(fixture("shared")), "m::Run"));
    refuses(emitOriginal(entry, context), "source.control-native-unavailable");
    outs() << "native selected-control dependency unavailable; source checks "
              "have a separate test\n";
    return 77;
  }
#ifndef ZKC_HAS_NATIVE_COMMON_CONTROL
  outs() << "native common-control analysis dependency unavailable\n";
  return 77;
#endif
  Cases cases;
  const auto booleanSource = fixture("shared");
  cases.run("real source reaches actual independent candidate comparison", [&] {
    auto entry = take(closeSubject(check(booleanSource), "m::Run"));
    auto original = take(prepareOriginal(entry));
    auto candidate =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(candidate), "emitted original did not parse");
    auto compared = take(compareOriginal(entry, *candidate));
    require(compared.operations >= 3,
            "dormant arm operations were not compared");
    require(!take(exportSourceCorrespondence(original)).empty(),
            "missing retained source/control maps");
  });
  for (StringRef mutation : {"dormant-yield", "equal-typed-capture", "roles",
                             "output-roles", "site", "arm-order"})
    cases.run("actual source candidate mutation: " + mutation, [&] {
      auto entry = take(closeSubject(check(booleanSource), "m::Run"));
      auto original = take(prepareOriginal(entry));
      auto candidate =
          mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
      require(bool(candidate), "emitted original did not parse");
      auto *selected = branch(*candidate);
      auto &dormant = selected->getRegion(1).front();
      if (mutation == "dormant-yield") {
        require(dormant.getNumArguments() >= 2, "missing capture ports");
        dormant.back().setOperand(0, dormant.getArgument(0));
      } else if (mutation == "equal-typed-capture") {
        require(selected->getNumOperands() >= 3, "missing exact captures");
        selected->setOperand(1, selected->getOperand(2));
      } else if (mutation == "roles")
        selected->setAttr(
            "roles", mlir::ArrayAttr::get(
                         &context, {mlir::StringAttr::get(&context, "r0")}));
      else if (mutation == "output-roles")
        selected->setAttr("output_roles", mlir::ArrayAttr::get(&context, {}));
      else if (mutation == "site")
        selected->setAttr("site", mlir::StringAttr::get(&context, "changed"));
      else {
        mlir::Region saved;
        saved.takeBody(selected->getRegion(0));
        selected->getRegion(0).takeBody(selected->getRegion(1));
        selected->getRegion(1).takeBody(saved);
      }
      if (mutation == "dormant-yield" || mutation == "equal-typed-capture" ||
          mutation == "site" || mutation == "arm-order") {
        require(mlir::succeeded(admitStage(*candidate)),
                "mutation did not reach source comparison");
        refuses(compareOriginal(entry, *candidate), "source.correspondence");
      } else {
        auto result = compareOriginal(entry, *candidate);
        require(!result, "changed actual candidate was accepted");
        consumeError(result.takeError());
      }
    });
  cases.run("ordinary enums retain all arms and exact tag requirements", [&] {
    auto project = check(fixture("match"));
    auto original =
        take(prepareOriginal(take(closeSubject(project, "m::Run"))));
    require(!take(exportSourceCorrespondence(original)).empty(),
            "enum arms lost retained associations");
  });
  cases.run("Math control emits a registered selected region", [&] {
    auto project = check(fixture("math"));
    auto original =
        take(prepareOriginal(take(closeSubject(project, "m::Run"))));
    require(original.bytes().contains("data.branch"),
            "Math branch became eager or unregistered control");
    require(!take(exportSourceCorrespondence(original)).empty(),
            "Math arms lost retained associations");
  });
  cases.run(
      "actual application-map comparison preserves lexical arm paths", [&] {
        auto entry =
            take(closeSubject(check(fixture("applications")), "m::Run"));
        auto original = take(prepareOriginal(entry));
        auto candidate =
            mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
        auto prepared = mathematical::prepareProtocol(*candidate, false);
        require(bool(prepared), "application preparation failed");
        std::string bytes;
        raw_string_ostream stream(bytes);
        prepared->print(stream);
        auto map = take(protocol::produceApplicationMap(
            original.bytes(), bytes, entry.protocol().symbol, context));
        if (auto error = protocol::checkApplicationMap(
                original.bytes(), bytes, entry.protocol().symbol, map, context))
          throw std::runtime_error(toString(std::move(error)));
      });
  cases.run("application expansion renames placed selected results", [&] {
    // The arms yield values held only at Choose's first role, which the
    // application maps to Run's second role. Expansion must rename the
    // selected region's result placement with its roster.
    auto entry = take(closeSubject(
        check(
            R"(protocol Choose roles(A,B)(flag: bool @(A,B), x: bool @(A), y: bool @(A)) -> bool @(A):
    #[site(choice)]
    result = if flag:
        x
    else:
        y
    return result
pub protocol Run roles(P,V)(flag: bool @(P,V), x: bool @(V), y: bool @(V)) -> bool @(V):
    result <- Choose(flag, x, y) @(V,P)
    return result
)"),
        "m::Run"));
    auto original = take(prepareOriginal(entry));
    auto candidate =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(candidate), "placed original did not parse");
    auto prepared = mathematical::prepareProtocol(*candidate, false);
    require(bool(prepared), "placed application preparation failed");
    std::string bytes;
    raw_string_ostream stream(bytes);
    prepared->print(stream);
    auto map = take(protocol::produceApplicationMap(
        original.bytes(), bytes, entry.protocol().symbol, context));
    if (auto error = protocol::checkApplicationMap(
            original.bytes(), bytes, entry.protocol().symbol, map, context))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("actual linear branch successors retain zero-trip loop roots", [&] {
    auto entry = take(closeSubject(check(fixture("resources")), "m::Run"));
    auto original = take(prepareOriginal(entry));
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "resource original did not parse");
    take(compareOriginal(entry, *module));
    auto prepared = mathematical::prepareProtocol(*module, false);
    require(bool(prepared),
            "exact resource branch successors failed preparation");
  });
  cases.run("enum payload association survives equal-typed mutations", [&] {
    auto project = check(R"(enum Choice:
    Pair(bool,bool)
    None()
pub protocol Run roles(P,V)(value: Choice @(P,V)) -> bool @(P,V):
    result = match value:
        case Pair(first,second):
            first
        case None():
            false
    return result
)");
    auto entry = take(closeSubject(project, "m::Run"));
    auto original = take(prepareOriginal(entry));
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "enum original did not parse");
    auto &arm = branch(*module)->getRegion(0).front();
    require(arm.getNumArguments() == 2, "payload port count differs");
    arm.back().setOperand(0, arm.getArgument(1));
    require(mlir::succeeded(admitStage(*module)),
            "payload mutation did not reach source comparison");
    refuses(compareOriginal(entry, *module), "source.correspondence");
  });
#ifdef ZKC_HAS_NATIVE_COMMON_CONTROL
  for (StringRef name : {"shared", "math", "match", "applications", "resources",
                         "payload", "placed-oracles", "multireceiver",
                         "static-selection", "extent", "services"})
    cases.run("independent source/native common inventory: " + name, [&] {
      auto entry =
          take(closeSubject(check(fixture(name), name == "extent"), "m::Run"));
      auto original = take(prepareOriginal(entry));
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
      require(bool(module), "original did not parse");
      protocol_ir::MathematicalOp root;
      module->walk([&](protocol_ir::MathematicalOp function) {
        if (function.getSymName() == entry.protocol().symbol)
          root = function;
      });
      require(bool(root), "original omitted the selected protocol");
      uint64_t remaining = 8000000;
      facts::Work work(remaining);
      auto native = take(zkc::deriveCommonControlRequirements(root, work));
      auto source =
          take(zkc::language::deriveNativeCommonControlRequirements(entry));
      auto key = [&](mlir::Type type, bool tagOnly,
                     std::optional<unsigned> extentAxis, auto components,
                     auto getRole, auto getInput) {
        std::string result;
        raw_string_ostream stream(result);
        type.print(stream);
        stream << (tagOnly ? ":tag" : ":value");
        if (extentAxis)
          stream << ":extent=" << *extentAxis;
        std::vector<std::string> parts;
        for (const auto &component : components) {
          std::string part =
              std::to_string(getInput(component)) + ":" + getRole(component);
          for (auto index : component.path)
            part += ":" + std::to_string(index);
          parts.push_back(std::move(part));
        }
        llvm::sort(parts);
        for (const auto &part : parts)
          stream << "/" << part;
        return result;
      };
      std::vector<std::string> actual, expected;
      for (const auto &requirement : native)
        actual.push_back(key(
            requirement.type, requirement.tagOnly, requirement.extentAxis,
            requirement.components,
            [](const auto &component) {
              return component.role.getValue().str();
            },
            [](const auto &component) { return component.input; }));
      for (const auto &requirement : source)
        expected.push_back(key(
            protocol::decodeBoundType(&context, requirement.type),
            requirement.tagOnly, requirement.extentAxis, requirement.components,
            [](const auto &component) {
              return nativeRoleName(component.role);
            },
            [](const auto &component) { return component.originalInput; }));
      llvm::sort(actual);
      llvm::sort(expected);
      require(actual == expected,
              "independent exact component/type/tag obligations differ");
    });
#endif
  cases.run("placed branch yields preserve independent oracle holders", [&] {
    auto entry = take(closeSubject(check(fixture("placed-oracles")), "m::Run"));
    auto original = take(prepareOriginal(entry));
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "placed original did not parse");
    take(compareOriginal(entry, *module));
    auto *selected = branch(*module);
    require(selected->getNumOperands() == 4 && selected->getNumResults() == 3,
            "logical branch manufactured an aggregate holder or flattened a "
            "handle");
  });
  cases.run("branch forwarding retains one holder and multiple receivers", [&] {
    auto project = check(fixture("multireceiver"));
    refuses(closeNativeRun(project, "m::Run"), "source.ingress");
    auto entry = take(closeSubject(project, "m::Run"));
    auto original = take(prepareOriginal(entry));
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "multiple-receiver original did not parse");
    take(compareOriginal(entry, *module));
    require(branch(*module)->getNumResults() == 1,
            "branch manufactured independent logical handles");
  });
  cases.run("equal-contract service captures retain their actual root", [&] {
    auto entry = take(closeSubject(check(fixture("services")), "m::Run"));
    auto original = take(prepareOriginal(entry));
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "service original did not parse");
    auto *selected = branch(*module);
    auto &function = selected->getParentOp()->getRegion(0).front();
    require(selected->getNumOperands() == 2 && function.getNumArguments() == 3,
            "service-root capture shape differs");
    for (unsigned arm = 0; arm != 2; ++arm) {
      auto &query = selected->getRegion(arm).front().front();
      require(query.getName().getStringRef() == "protocol.query" &&
                  query.getAttrOfType<mlir::StringAttr>("site").getValue() ==
                      nativeSelectedSite(nativeSiteName("choice", 0),
                                         arm ? "else" : "then",
                                         nativeSiteName("challenge", 0)),
              "authored arm sites lost their exact lexical association");
    }
    selected->setOperand(1, function.getArgument(2));
    require(mlir::succeeded(admitStage(*module)),
            "service mutation did not reach source comparison");
    refuses(compareOriginal(entry, *module), "source.correspondence");
  });
  return cases.result();
}
