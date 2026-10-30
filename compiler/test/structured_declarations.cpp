#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](mlir::Diagnostic &) { return success(); });
  auto project = take(analyze(take(capture({{"carrier", R"(
module carrier;
#[linear] struct Pending { pub first:bool, pub second:bool }
fn pending(value:bool)->Pending { return Pending{first:value,second:value}; }
fn check(claim:Pending)->bool { let values=unpack(claim); return values.0 && values.1; }
protocol Forward roles(V)(claim:Pending@V)->(claim:Pending@V) { return(claim=claim); }
protocol Run roles(V)(value:bool@V)->(accepted:bool@V) {
  let initial@V=pending(value);
  let claim=Forward roles(V)(initial);
  let finalValue@V=check(claim);
  return(accepted=finalValue);
}
)",
                                             "carrier.zkc"}})))
                          .checkedProject());
  auto entry = take(closeSubject(project, "carrier::Run"));
  auto bytes = take(emitOriginal(entry, context));
  auto expectedText = take(inspectComponentDeclarations(entry));
  auto expected = take(json::parse(expectedText));
  Cases cases;
  auto parse = [&] {
    auto module =
        parseSourceString<ModuleOp>(bytes, ParserConfig(&context, false));
    require(bool(module), "emitted original did not parse");
    return module;
  };
  cases.run("producer retains structured inherent declaration data", [&] {
    auto module = parse();
    auto unit = cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
    auto attr = unit->getAttr("source_declarations");
    require(attr && isa<ArrayAttr>(attr),
            "declarations are not structured attributes");
    require(expectedText != "[[],[]]" &&
                equalNaturalJson(take(exportDeclarationData(attr)), expected),
            "declarations differ from independent frontend inspection");
    require(succeeded(admitStage(*module)),
            "structured module failed native verification");
    take(compareOriginal(entry, *module));
  });
  cases.run("parser refuses the retired document carrier", [&] {
    // ODS stores this as an inherent ArrayAttr property. A generic setAttr of
    // the wrong type clears an optional property; exercise the actual import
    // boundary instead of mistaking that API operation for malformed IR.
    auto malformed = parseSourceString<ModuleOp>(R"(
      module { "protocol.module"() ({
      }) {profile=#protocol.profile<protocol>,
          source_declarations="[[],[]]"} : () -> () }
    )",
                                                 ParserConfig(&context, false));
    require(!malformed, "parser admitted the retired document carrier");
  });
  for (StringRef mutation : {"absent", "empty", "field order", "port name"})
    cases.run("independent frontend comparison refuses " + mutation, [&] {
      auto module = parse();
      auto unit =
          cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
      if (mutation == "absent")
        unit->removeAttr("source_declarations");
      else {
        auto changed = take(json::parse(expectedText));
        auto &tables = *changed.getAsArray();
        if (mutation == "empty")
          changed = json::Array{json::Array{}, json::Array{}};
        else if (mutation == "field order") {
          auto &fields =
              *(*(*tables[0].getAsArray())[0].getAsArray())[3].getAsArray();
          require(fields.size() == 2, "fixture lost its two ordered fields");
          std::swap(fields[0], fields[1]);
        } else {
          auto &ports =
              *(*(*tables[1].getAsArray())[0].getAsArray())[1].getAsArray();
          (*ports[0].getAsArray())[0] = "other_claim";
        }
        unit->setAttr("source_declarations",
                      take(importDeclarationData(&context, changed)));
      }
      require(succeeded(admitStage(*module)),
              "declaration mutation did not retain native formation");
      refuses(compareOriginal(entry, *module), "source.correspondence");
    });
  return cases.result();
}
