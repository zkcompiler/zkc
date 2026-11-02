#include "../lib/Compiler/ComponentContracts.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include <map>

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
using J = json::Value;
using A = json::Array;
CheckedProject checked(StringRef module, StringRef text, StringRef format) {
  CaptureOptions options;
  options.format = format.str();
  return take(analyze(take(capture({{module.str(), text.str(), "fixture.zkc"}},
                                   options)))
                  .checkedProject());
}
A &rows(J &carrier, unsigned table) {
  return *(*carrier.getAsArray())[table].getAsArray();
}
A &record(J &carrier, StringRef path) {
  for (auto &value : rows(carrier, 0))
    if ((*(*value.getAsArray())[0].getAsArray())[2] == J(path))
      return *value.getAsArray();
  throw std::runtime_error(("no retained row " + path).str());
}
J &member(J &carrier, StringRef path, StringRef name) {
  for (auto &value : *record(carrier, path)[3].getAsArray())
    if ((*value.getAsArray())[0] == J(name))
      return value;
  throw std::runtime_error(("no retained member " + name).str());
}
A &port(J &carrier, unsigned index = 0) {
  return *(*(*rows(carrier, 1)[0].getAsArray())[1].getAsArray())[index]
              .getAsArray();
}
std::string role(unsigned ordinal) { return nativeRoleName(ordinal); }
void refusesCarrier(const J &carrier, StringRef code) {
  auto error = checkComponentDeclarations(carrier);
  require(bool(error), "malformed carrier accepted: " + code);
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
} // namespace
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
  auto accept = [](Error error) {
    if (error)
      throw std::runtime_error(toString(std::move(error)));
  };
  cases.run("producer retains structured inherent declaration data", [&] {
    auto module = parse();
    auto unit = cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
    auto attr = unit->getAttr("source_declarations");
    require(attr && isa<ArrayAttr>(attr),
            "declarations are not structured attributes");
    require(expectedText != "[[],[],[]]" &&
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
          changed = json::Array{json::Array{}, json::Array{}, json::Array{}};
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
  cases.run("a resource row names its custody slot", [&] {
    auto carrier = expected;
    const auto &row = record(carrier, "carrier::Pending");
    auto slot = row[5].getAsString();
    require(row.size() == 6 && row[4].getAsArray()->empty() && slot &&
                slot->starts_with("zkl_resource_") && slot->size() == 77,
            "linear row lost its custody slot");
    for (const auto &value : *row[3].getAsArray())
      require((*value.getAsArray())[2].kind() == J::Null,
              "an ordinary row member acquired a placement");
    accept(checkComponentDeclarations(carrier));
  });
  auto recursive = [&] {
    auto buffer = MemoryBuffer::getFile(ZKC_RECURSIVE_RECORDS);
    require(bool(buffer), "recursive record fixture is missing");
    return checked("sample", (*buffer)->getBuffer(), "zkc-layout");
  }();
  auto relay = take(closeSubject(recursive, "sample::Relay"));
  auto relayText = take(inspectComponentDeclarations(relay));
  auto relayCarrier = take(json::parse(relayText));
  cases.run("a distributed telescope keeps its nested formulas", [&] {
    auto carrier = relayCarrier;
    auto envelope = record(carrier, "sample::Envelope");
    require(envelope[4] == J(A{"X", "Y", "Z"}) && envelope[5].kind() == J::Null,
            "Envelope lost its telescope or acquired a slot");
    require(record(carrier, "sample::Sources")[4] == J(A{"A", "B", "C"}),
            "Sources lost its telescope");
    // Sources roles(Y,Z,X): left is held by C and right by B in Sources.
    require(
        (*member(carrier, "sample::Envelope", "sources").getAsArray())[2] ==
            J(A{"product", A{"Y", "Z", "X"},
                A{A{"oracle", "X", A{"Y", "Z"}}, A{"oracle", "Z", A{"Y"}}}}),
        "nested formula was not specialized in telescope order");
    require((*member(carrier, "sample::Envelope", "flag").getAsArray())[2] ==
                J(A{"data", A{"Y"}}),
            "data member formula differs");
    // Relay roles(V,Q,P) applies Envelope roles(P,V,Q).
    const auto &placement = port(carrier)[5];
    require((*placement.getAsArray())[1] == J(A{role(2), role(0), role(1)}) &&
                port(carrier)[2] == J(A{role(0), role(1), role(2)}),
            "port arguments were sorted or the summary differs");
    accept(checkComponentDeclarations(carrier));
  });
  cases.run("a permuted 17-role telescope keeps telescope order", [&] {
    std::vector<std::string> telescope, roster, applied;
    for (unsigned i = 0; i < 17; ++i) {
      telescope.push_back("A" + std::to_string(i));
      roster.push_back("R" + std::to_string(i));
      applied.push_back("R" + std::to_string((i * 5 + 3) % 17));
    }
    auto source = "struct Wide roles(" + join(telescope, ", ") +
                  "):\n    pub f0: index @A0\n"
                  "pub protocol Fan roles(" +
                  join(roster, ", ") + ")(w: Wide roles(" +
                  join(applied, ", ") + ")) -> bool @R1:\n    return true\n";
    auto entry =
        take(closeSubject(checked("m", source, "zkc-layout"), "m::Fan"));
    auto carrier = take(json::parse(take(inspectComponentDeclarations(entry))));
    A arguments;
    for (unsigned i = 0; i < 17; ++i)
      arguments.push_back(role((i * 5 + 3) % 17));
    require((*port(carrier)[5].getAsArray())[1] == J(std::move(arguments)),
            "a permuted role substitution was sorted");
    require(record(carrier, "m::Wide")[4].getAsArray()->size() == 17,
            "the telescope was truncated");
    accept(checkComponentDeclarations(carrier));
  });
  cases.run("authorities cover nested, phantom and module paths", [&] {
    auto project = checked("carrier", R"(module carrier;
struct Tag {}
interface Spec { type T:Copy+Drop; }
module Impl:Spec { type T:Copy+Drop=bool; }
#[linear] struct Box<T:Type> { pub value: Impl::T }
protocol Keep roles(V)(b:Box<Tag>@V)->(out:Box<Tag>@V){ return(out=b); }
)",
                           "zkc");
    auto entry = take(closeSubject(project, "carrier::Keep"));
    auto carrier = take(json::parse(take(inspectComponentDeclarations(entry))));
    std::map<std::string, J> authorities;
    std::vector<std::string> order;
    for (const auto &value : rows(carrier, 2)) {
      const auto &row = *value.getAsArray();
      order.push_back(row[0].getAsString()->str());
      authorities.emplace(order.back(), row[1]);
    }
    require(std::is_sorted(order.begin(), order.end()) &&
                authorities.size() == order.size(),
            "authority rows are not sorted and unique");
    for (StringRef path : {"carrier::Box", "carrier::Tag", "carrier::Impl"}) {
      auto found = authorities.find(path.str());
      require(found != authorities.end(), "authority row missing: " + path);
      require(found->second == J(*take(sourceAuthority(project, path))),
              "authority differs from the checked source: " + path);
    }
    accept(checkComponentDeclarations(carrier));
  });
  struct Mutation {
    StringRef name, code;
    std::function<void(J &)> apply;
  };
  std::vector<Mutation> mutations = {
      {"a slot on an ordinary row", "component-declaration-slot",
       [](J &carrier) {
         record(carrier, "sample::Envelope")[5] =
             "zkl_resource_" + std::string(64, 'a');
       }},
      {"a role outside the telescope", "component-declaration-role",
       [](J &carrier) {
         (*member(carrier, "sample::Envelope", "flag").getAsArray())[2] =
             A{"data", A{"W"}};
       }},
      {"non-injective product arguments", "component-declaration-role",
       [](J &carrier) {
         auto &formula =
             *(*member(carrier, "sample::Envelope", "sources").getAsArray())[2]
                  .getAsArray();
         formula[1] = A{"Y", "Y", "X"};
       }},
      {"a missing member placement", "component-declaration-placement",
       [](J &carrier) {
         (*member(carrier, "sample::Envelope", "flag").getAsArray())[2] =
             nullptr;
       }},
      {"a summary that differs from its placement",
       "component-declaration-placement",
       [](J &carrier) { port(carrier)[2] = A{role(0), role(1)}; }},
      {"a missing authority", "component-declaration-authority",
       [](J &carrier) { rows(carrier, 2).pop_back(); }},
      {"an extra authority", "component-declaration-authority",
       [](J &carrier) {
         rows(carrier, 2).push_back(A{"sample::Zeta", nullptr});
       }},
      {"unsorted authorities", "component-declaration-authority",
       [](J &carrier) {
         auto &authorities = rows(carrier, 2);
         std::swap(authorities[0], authorities[1]);
       }},
      {"a duplicate authority", "component-declaration-authority",
       [](J &carrier) {
         auto &authorities = rows(carrier, 2);
         J copy = authorities[0];
         authorities[1] = std::move(copy);
       }},
      {"a non-hex revision", "component-declaration-authority",
       [](J &carrier) {
         (*rows(carrier, 2)[0].getAsArray())[1] = std::string(64, 'G');
       }},
  };
  for (const auto &mutation : mutations)
    cases.run("the carrier reader refuses " + mutation.name, [&] {
      auto carrier = relayCarrier;
      mutation.apply(carrier);
      refusesCarrier(carrier, mutation.code);
    });
  cases.run("the carrier reader refuses a missing slot", [&] {
    auto carrier = expected;
    record(carrier, "carrier::Pending")[5] = nullptr;
    refusesCarrier(carrier, "component-declaration-slot");
  });
  cases.run("frontend comparison refuses sorted product arguments", [&] {
    auto module = parseSourceString<ModuleOp>(
        take(emitOriginal(relay, context)), ParserConfig(&context, false));
    require(bool(module), "emitted relay original did not parse");
    auto unit = cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
    auto carrier = relayCarrier;
    (*(*member(carrier, "sample::Envelope", "sources").getAsArray())[2]
          .getAsArray())[1] = A{"X", "Y", "Z"};
    // Sorting keeps the arguments injective, so only the frontend recomputation
    // of the carrier detects that the substitution changed.
    accept(checkComponentDeclarations(carrier));
    unit->setAttr("source_declarations",
                  take(importDeclarationData(&context, carrier)));
    refuses(compareOriginal(relay, *module), "source.correspondence");
  });
  return cases.result();
}
