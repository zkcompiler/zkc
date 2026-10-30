#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/ApplicationMap.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include <functional>
#include <iterator>
#include <optional>

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
void accept(Error e) {
  if (e)
    throw std::runtime_error(toString(std::move(e)));
}
void refuse(Error e, StringRef code) {
  require(bool(e), "expected refusal: " + code);
  auto message = toString(std::move(e));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
std::string read(StringRef path) {
  auto file = MemoryBuffer::getFile(path);
  require(bool(file), "could not read fixture " + path);
  return (*file)->getBuffer().str();
}
std::string print(ModuleOp module) {
  std::string result;
  raw_string_ostream stream(result);
  module.print(stream, OpPrintingFlags().enableDebugInfo());
  stream << '\n';
  return result;
}
protocol_ir::MathematicalOp function(ModuleOp module, StringRef name) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  return SymbolTable(unit).lookup<protocol_ir::MathematicalOp>(name);
}
std::string digest(StringRef bytes) {
  return "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
struct Fixture {
  MLIRContext &context;
  std::string original, candidate, entry;
  json::Value record = nullptr;
  Fixture(MLIRContext &context, std::string bytes, StringRef selected = "main",
          bool prepare = true)
      : context(context), original(std::move(bytes)), entry(selected.str()) {
    if (prepare) {
      auto module = parseSourceString<ModuleOp>(original, &context);
      require(bool(module), "invalid application fixture");
      auto prepared = mathematical::prepareProtocol(*module, false);
      require(bool(prepared), "unsimplified preparation failed");
      candidate = print(*prepared);
    } else
      candidate = original;
    record = take(json::parse(
        take(produceApplicationMap(original, candidate, entry, context))));
    accept(checkApplicationMap(original, candidate, entry, printJson(record),
                               context));
  }
  json::Array &apps() {
    return *record.getAsObject()->getArray("applications");
  }
  json::Array &rows() {
    return *record.getAsObject()->getArray("instructions");
  }
  Error check(const json::Value &value) {
    return checkApplicationMap(original, candidate, entry, printJson(value),
                               context);
  }
  json::Object &nested(json::Value &value) {
    for (auto &row : *value.getAsObject()->getArray("applications"))
      if (row.getAsObject()->get("parent")->kind() != json::Value::Null)
        return *row.getAsObject();
    throw std::runtime_error("no nested application");
  }
  std::string mutate(llvm::function_ref<void(ModuleOp)> action) {
    auto module = parseSourceString<ModuleOp>(candidate, &context);
    require(bool(module), "candidate parse failed");
    action(*module);
    require(succeeded(mlir::verify(*module)),
            "mutation must remain native signature compatible");
    return print(*module);
  }
  Error changed(StringRef bytes, json::Value value) {
    (*value.getAsObject()->getObject("candidate"))["digest"] = digest(bytes);
    return checkApplicationMap(original, bytes, entry, printJson(value),
                               context);
  }
};
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // Deliberately refused subjects should not drown independent case results.
  ScopedDiagnosticHandler diagnostics(&context,
                                      [](Diagnostic &) { return success(); });
  Cases cases;
  const std::string original =
      read(ZKC_APPLICATION_FIXTURES "/application-map/nested.mlir");
  cases.run("expanded sites retain original string bounds elsewhere", [&] {
    auto longSites = original;
    for (StringRef label : {"check", "first"}) {
      auto from = "site=\"" + label.str() + "\"";
      auto at = longSites.find(from);
      require(at != std::string::npos, "missing site fixture");
      longSites.replace(at, from.size(),
                        "site=\"" + std::string(256, label.front()) + "\"");
    }
    Fixture expanded(context, longSites);
    refuses(exportStructuredSource(expanded.candidate, "main", context),
            "structured-source-limit");
    take(exportStructuredSource(expanded.candidate, "main", context,
                                StructuredSourceProfile::Prepared));
    auto longRole = original;
    auto at = longRole.find("Reader");
    while (at != std::string::npos) {
      longRole.replace(at, 6, std::string(513, 'R'));
      at = longRole.find("Reader", at + 513);
    }
    refuses(exportStructuredSource(longRole, "main", context,
                                   StructuredSourceProfile::Prepared),
            "structured-source-limit");
  });
  std::optional<Fixture> fixture;
  cases.run("prepare actual nested applications and pure helper calls", [&] {
    fixture.emplace(context, original);
    std::vector<std::string> roots;
    unsigned roleFree = 0, loopCalls = 0, emptyCalls = 0;
    for (const auto &value : fixture->apps()) {
      const auto &row = *value.getAsObject();
      require(row.get("written")->kind() == json::Value::Null,
              "MLIR origin or Location manufactured frontend provenance");
      if (row.get("parent")->kind() == json::Value::Null)
        roots.push_back(row.getString("callee")->str());
      else {
        roleFree += row.getArray("roles")->empty();
        loopCalls += row.getArray("source_path")->size() == 3;
        emptyCalls += row.getString("callee") == "zero";
      }
    }
    require(roots == std::vector<std::string>{"empty", "child", "zero", "main",
                                              "unused"},
            "roots lost complete original declaration order");
    require(roleFree == 3 && loopCalls == 1 && emptyCalls == 1,
            "helper, loop or empty application occurrences were omitted");
    bool auxiliary = false, dormant = false;
    for (const auto &value : fixture->rows()) {
      const auto &row = *value.getAsObject();
      auxiliary |= row.getString("purpose") == "auxiliary";
      dormant |= row.getString("target_definition") == "unused";
    }
    require(auxiliary && dormant, "port restrictions or dormant coverage lost");
  });
  if (!fixture)
    return cases.result();
  Fixture &f = *fixture;
  using Mutation = std::pair<const char *, std::function<void(json::Value &)>>;
  const std::vector<Mutation> mutations{
      {"unknown root field",
       [](auto &v) { (*v.getAsObject())["accepted"] = true; }},
      {"wrong format",
       [](auto &v) { (*v.getAsObject())["format"] = "zkc.application-map/1"; }},
      {"unknown identity field",
       [](auto &v) {
         (*v.getAsObject()->getObject("source"))["proof"] = true;
       }},
      {"stale source digest",
       [](auto &v) {
         (*v.getAsObject()->getObject("source"))["digest"] =
             "sha256:" + std::string(64, '0');
       }},
      {"stale candidate digest",
       [](auto &v) {
         (*v.getAsObject()->getObject("candidate"))["digest"] =
             "sha256:" + std::string(64, '0');
       }},
      {"wrong selected entry",
       [](auto &v) {
         (*v.getAsObject()->getObject("source"))["entry"] = "unused";
       }},
      {"noncanonical ordinal", [&](auto &v) { f.nested(v)["id"] = "00"; }},
      {"numeric ordinal", [&](auto &v) { f.nested(v)["id"] = 2; }},
      {"forward parent", [&](auto &v) { f.nested(v)["parent"] = "99999"; }},
      {"self parent",
       [&](auto &v) {
         auto &r = f.nested(v);
         r["parent"] = *r.get("id");
       }},
      {"wrong parent", [&](auto &v) { f.nested(v)["parent"] = "0"; }},
      {"wrong call path",
       [&](auto &v) { f.nested(v)["source_path"] = json::Array{"999"}; }},
      {"wrong callee", [&](auto &v) { f.nested(v)["callee"] = "unused"; }},
      {"wrong source definition",
       [&](auto &v) { f.nested(v)["source_definition"] = "main"; }},
      {"unknown application field",
       [&](auto &v) { f.nested(v)["location"] = "authoritative"; }},
      {"forged written link",
       [&](auto &v) {
         f.nested(v)["written"] =
             json::Object{{"subject", "s"}, {"node", "0"}, {"instance", "i"}};
       }},
      {"same typed arguments",
       [&](auto &v) {
         auto &a = *f.nested(v).getArray("arguments");
         std::swap((*a[0].getAsArray())[1], (*a[1].getAsArray())[1]);
       }},
      {"same typed results",
       [&](auto &v) {
         auto &a = *f.nested(v).getArray("results");
         std::swap((*a[0].getAsArray())[1], (*a[1].getAsArray())[1]);
       }},
      {"role substitution",
       [&](auto &v) {
         auto &a = *f.nested(v).getArray("roles");
         (*a[0].getAsArray())[1] = "0";
       }},
      {"wrong producer",
       [&](auto &v) {
         auto &a = *f.nested(v).getArray("arguments");
         (*(*a[0].getAsArray())[1].getAsObject())["producer"] =
             json::Array{"argument", "999"};
       }},
      {"capture in unrelated region",
       [&](auto &v) {
         auto &a = *f.nested(v).getArray("arguments");
         (*(*a[0].getAsArray())[1].getAsObject())["region"] =
             json::Array{"0", "0"};
       }},
      {"nonempty component path",
       [&](auto &v) {
         auto &a = *f.nested(v).getArray("arguments");
         (*(*a[0].getAsArray())[1].getAsObject())["components"] =
             json::Array{"0"};
       }},
      {"unknown value field",
       [&](auto &v) {
         auto &a = *f.nested(v).getArray("arguments");
         (*(*a[0].getAsArray())[1].getAsObject())["type"] = "i1";
       }},
      {"omit logical argument",
       [&](auto &v) { f.nested(v).getArray("arguments")->pop_back(); }},
      {"omit zero result application",
       [](auto &v) {
         auto &a = *v.getAsObject()->getArray("applications");
         for (auto it = a.begin(); it != a.end(); ++it)
           if (it->getAsObject()->getString("callee") == "zero" &&
               it->getAsObject()->get("parent")->kind() != json::Value::Null) {
             a.erase(it);
             break;
           }
       }},
      {"omit dormant terminator",
       [](auto &v) { v.getAsObject()->getArray("instructions")->pop_back(); }},
      {"duplicate instruction",
       [](auto &v) {
         auto &r = *v.getAsObject()->getArray("instructions");
         r.push_back(r.front());
       }},
      {"wrong target path",
       [](auto &v) {
         (*v.getAsObject()
               ->getArray("instructions")
               ->front()
               .getAsObject())["target_path"] = json::Array{"99999"};
       }},
      {"unknown instruction field",
       [](auto &v) {
         (*v.getAsObject()
               ->getArray("instructions")
               ->front()
               .getAsObject())["certificate"] = true;
       }},
      {"shared versus expanded confusion",
       [](auto &v) {
         auto &r = *v.getAsObject()->getArray("instructions");
         for (auto &i : r)
           if (i.getAsObject()->get("application")->kind() !=
               json::Value::Null) {
             (*i.getAsObject())["application"] = nullptr;
             break;
           }
       }},
      {"forged auxiliary guard",
       [](auto &v) {
         auto &r = *v.getAsObject()->getArray("instructions");
         for (auto &i : r)
           if (i.getAsObject()->getString("source_definition") == "unused") {
             (*i.getAsObject())["purpose"] = "auxiliary";
             (*i.getAsObject())["source_path"] = nullptr;
             break;
           }
       }},
  };
  for (const auto &mutation : mutations) {
    const auto &name = mutation.first;
    const auto &mutate = mutation.second;
    cases.run(name, [&] {
      auto changed = f.record;
      mutate(changed);
      StringRef code = StringRef(name).contains("digest") ||
                               StringRef(name).contains("identity") ||
                               StringRef(name).contains("entry")
                           ? "application-map-identity"
                       : StringRef(name).contains("root") ||
                               StringRef(name) == "wrong format"
                           ? "application-map-schema"
                           : "application-map-correspondence";
      refuse(f.check(changed), code);
    });
  }
  for (StringRef key : {"format", "\\u0066ormat"})
    cases.run("duplicate decoded JSON key: " + key, [&] {
      std::string bytes = printJson(f.record);
      bytes.insert(1, "\"" + key.str() + "\":\"zkc.application-map/0\",");
      refuse(
          checkApplicationMap(f.original, f.candidate, f.entry, bytes, context),
          "application-map-json");
    });
  cases.run("same typed actual return substitution with refreshed digest", [&] {
    auto changed = f.mutate([&](ModuleOp module) {
      auto &term = function(module, "main").getBody().front().back();
      auto a = term.getOperand(0), b = term.getOperand(1);
      term.setOperand(0, b);
      term.setOperand(1, a);
    });
    refuse(f.changed(changed, f.record), "application-map-correspondence");
  });
  cases.run("same typed actual restriction operand and forged locations", [&] {
    auto changed = f.mutate([&](ModuleOp module) {
      auto main = function(module, "main");
      auto restriction = *main.getBody()
                              .front()
                              .getOps<protocol_ir::RestrictRolesOp>()
                              .begin();
      restriction->setOperand(0, main.getBody().front().getArgument(2));
      module.walk([&](Operation *op) {
        op->setLoc(FileLineColLoc::get(&context, "trusted.zkc", 1, 1));
      });
    });
    refuse(f.changed(changed, f.record), "application-map-correspondence");
  });
  cases.run(
      "nested application resolves the actual closed capture producer", [&] {
        auto changed = f.mutate([&](ModuleOp module) {
          auto main = function(module, "main");
          auto repeat =
              *main.getBody().front().getOps<protocol_ir::RepeatOp>().begin();
          auto &body = repeat.getBody().front();
          auto restriction =
              *body.getOps<protocol_ir::RestrictRolesOp>().begin();
          restriction->setOperand(0, body.getArgument(2));
        });
        refuse(f.changed(changed, f.record), "application-map-correspondence");
      });
  cases.run(
      "dormant guard cannot acquire a different same typed producer", [&] {
        auto changed = f.mutate([&](ModuleOp module) {
          auto dormant = function(module, "unused");
          dormant.getBody().front().front().setOperand(
              0, dormant.getBody().front().getArgument(1));
        });
        refuse(f.changed(changed, f.record), "application-map-correspondence");
      });
  cases.run("shared Math helper body has independent actual coverage", [&] {
    auto changed = f.mutate([&](ModuleOp module) {
      auto unit =
          cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
      auto helper = SymbolTable(unit).lookup<func::FuncOp>("flip");
      helper.getBody().front().back().setOperand(0, helper.getArgument(0));
    });
    refuse(f.changed(changed, f.record), "application-map-correspondence");
  });
  cases.run(
      "dormant actual instruction cannot hide behind auxiliary metadata", [&] {
        auto changed = f.mutate([&](ModuleOp module) {
          auto dormant = function(module, "unused");
          OpBuilder builder(&dormant.getBody().front().back());
          protocol_ir::GuardOp::create(builder, dormant.getLoc(),
                                       dormant.getBody().front().getArgument(0),
                                       "extra", "Reader");
        });
        auto map = f.record;
        auto &rows = *map.getAsObject()->getArray("instructions");
        auto terminal = rows.back();
        (*terminal.getAsObject())["target_path"] = json::Array{"2"};
        (*rows.back().getAsObject())["purpose"] = "auxiliary";
        (*rows.back().getAsObject())["source_path"] = nullptr;
        rows.push_back(std::move(terminal));
        refuse(f.changed(changed, std::move(map)),
               "application-map-correspondence");
      });
  cases.run("actual owner substitution remains candidate specific", [&] {
    auto changed = f.mutate([&](ModuleOp module) {
      auto main = function(module, "main");
      auto guard =
          *main.getBody().front().getOps<protocol_ir::GuardOp>().begin();
      guard.setOwnerAttr(StringAttr::get(&context, "V"));
    });
    refuse(f.changed(changed, f.record), "application-map-correspondence");
  });
  cases.run("locations are nonsemantic after exact digest refresh", [&] {
    auto changed = f.mutate([&](ModuleOp module) {
      module.walk([&](Operation *op) {
        op->setLoc(FileLineColLoc::get(&context, "misleading.mlir", 99, 7));
      });
    });
    require(changed != f.candidate, "location mutation was not serialized");
    accept(f.changed(changed, f.record));
  });
  cases.run("exact original bytes bind whitespace", [&] {
    refuse(checkApplicationMap("\n" + f.original, f.candidate, f.entry,
                               printJson(f.record), context),
           "application-map-identity");
  });
  cases.run(
      "zero storage logical values retain ordered argument and result ports",
      [&] {
        Fixture zero(context, read(ZKC_APPLICATION_FIXTURES
                                   "/application-map/zero-ports.mlir"));
        auto copy = zero.record;
        auto &app = zero.nested(copy);
        require(app.getArray("arguments")->size() == 2 &&
                    app.getArray("results")->size() == 2,
                "zero storage values lost logical port identity");
        auto &ports = *app.getArray("arguments");
        std::swap((*ports[0].getAsArray())[1], (*ports[1].getAsArray())[1]);
        refuse(zero.check(copy), "application-map-correspondence");
        copy = zero.record;
        zero.nested(copy).getArray("results")->pop_back();
        refuse(zero.check(copy), "application-map-correspondence");
      });
  cases.run("application service operands retain distinct provider roots", [&] {
    Fixture services(context, read(ZKC_APPLICATION_FIXTURES
                                   "/application-map/services.mlir"));
    auto changed = services.mutate([&](ModuleOp module) {
      auto main = function(module, "main");
      auto query =
          *main.getBody().front().getOps<protocol_ir::QueryOp>().begin();
      require(query.getReference() == main.getBody().front().getArgument(0),
              "service argument acquired a port restriction");
      query->setOperand(0, main.getBody().front().getArgument(1));
    });
    refuse(services.changed(changed, services.record),
           "application-map-correspondence");
  });
  for (StringRef path : {"structured-source/nested-controls.mlir",
                         "structured-source/loops-and-captures.mlir",
                         "structured-source/open-services.mlir",
                         "structured-source/open-components.mlir",
                         "structured-source/open-groups.mlir"})
    cases.run(
        "ordinary preparation retains complete scoped and service carrier: " +
            path,
        [&] {
          Fixture scoped(
              context,
              read((Twine(ZKC_APPLICATION_FIXTURES) + "/" + path).str()),
              path.contains("loops-and-captures") ? "entry" : "main");
          require(!scoped.rows().empty(),
                  "missing retained definition coverage");
        });
  for (StringRef path :
       {"language/application.zkc", "structured-source/repeated-draw.zkc"})
    cases.run("source applications use the public compiler API: " + path, [&] {
      using namespace zkc::language;
      auto captured = take(
          capture({{"sample",
                    read((Twine(ZKC_APPLICATION_FIXTURES) + "/" + path).str()),
                    {}}}));
      auto project = take(analyze(captured).checkedProject());
      auto entry = take(closeProtocolDeployment(project, "sample::Demo"));
      auto original = take(prepareOriginal(entry));
      Fixture source(context, original.bytes().str(),
                     original.interface().selectedProtocol().symbol);
      require(source.apps().size() > 3,
              "source application forest was not exercised");
    });
  cases.run("native CFG comparison survives equal exported logical rows", [&] {
    Fixture scoped(context, read(ZKC_APPLICATION_FIXTURES
                                 "/structured-source/nested-controls.mlir"));
    auto changed = scoped.mutate([&](ModuleOp module) {
      auto unit =
          cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
      auto step = SymbolTable(unit).lookup<func::FuncOp>("step");
      require(bool(step), "missing scoped CFG fixture");
      auto first = std::next(step.getBody().begin());
      auto second = std::next(first);
      second->moveBefore(&*first);
    });
    auto before = take(json::parse(
        take(exportStructuredSource(scoped.candidate, "main", context)).bytes));
    auto after = take(json::parse(
        take(exportStructuredSource(changed, "main", context)).bytes));
    (*after.getAsArray())[2] = (*before.getAsArray())[2];
    require(equalNaturalJson(before, after),
            "CFG control must exercise identical logical rows");
    refuse(scoped.changed(changed, scoped.record),
           "application-map-correspondence");
  });
  cases.run("retained pure helper is a direct shared body association", [&] {
    // No protocol applications remain, but the pure helper remains callable.
    std::string bytes = R"(module { "protocol.module"() ({
      func.func private @id(%a:i1)->i1 { return %a : i1 }
      "protocol.func"() ({ ^entry(%a:i1):
        %r = func.call @id(%a) : (i1)->i1
        "protocol.return"(%r) : (i1)->()
      }) {sym_name="main",origin=["main",[]],function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
    }) {profile=#protocol.profile<protocol>} : ()->() })";
    Fixture shared(context, bytes, "main", false);
    require(shared.apps().size() == 1,
            "shared helper falsely became an expansion");
    require(shared.rows()[0].getAsObject()->get("application")->kind() ==
                json::Value::Null,
            "shared helper body falsely owns one invocation");
  });
  cases.run("folded arithmetic needs an owning correspondence rule", [&] {
    std::string bytes = R"(module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%a:i1):
        %yes = arith.constant true
        %r = arith.andi %a,%yes : i1
        "protocol.return"(%r) : (i1)->()
      }) {sym_name="main",origin=["main",[]],function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
    }) {profile=#protocol.profile<protocol>} : ()->() })";
    auto module = parseSourceString<ModuleOp>(bytes, &context);
    require(bool(module), "invalid folding fixture");
    auto folded = mathematical::prepareProtocol(*module, true);
    require(bool(folded), "folding fixture could not be prepared");
    refuses(produceApplicationMap(bytes, print(*folded), "main", context),
            "application-map-unsupported");
  });
  cases.run("JSON depth bound precedes subject work", [&] {
    auto bytes = std::string(65, '[') + "null" + std::string(65, ']');
    refuse(checkApplicationMap("", "", "", bytes, context),
           "application-map-limit");
  });
  cases.run("byte bound precedes subject work", [&] {
    refuse(checkApplicationMap("", "", "",
                               std::string(32 * 1024 * 1024 + 1, ' '), context),
           "application-map-limit");
  });
  cases.run("metadata work bound precedes JSON allocation", [&] {
    std::string bytes = "[";
    for (unsigned i = 0; i < 1000000; ++i)
      bytes += "null,";
    bytes += "null]";
    refuse(checkApplicationMap("", "", "", bytes, context),
           "application-map-limit");
  });
  for (StringRef table : {"applications", "instructions"})
    cases.run("row bound: " + table, [&] {
      auto copy = f.record;
      json::Array rows;
      for (unsigned i = 0; i <= 100000; ++i)
        rows.push_back(nullptr);
      (*copy.getAsObject())[table] = std::move(rows);
      refuse(f.check(copy), "application-map-limit");
    });
  cases.run("path bound and noncanonical path ordinals", [&] {
    for (bool longPath : {false, true}) {
      auto copy = f.record;
      json::Array path;
      for (unsigned i = 0; i < (longPath ? 65u : 1u); ++i)
        path.push_back(longPath ? "0" : "00");
      f.nested(copy)["source_path"] = std::move(path);
      refuse(f.check(copy), "application-map-correspondence");
    }
  });
  return cases.result();
}
