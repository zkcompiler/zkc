#include "../lib/Compiler/SourceView.h"
#include "mlir/Bytecode/BytecodeWriter.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/ApplicationMap.h"
#include "zkc/Compiler/SourceCorrespondence.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/InspectionData.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include <future>

using namespace llvm;
using namespace mlir;
using namespace zkc::test;
namespace {
std::string bytecode(ModuleOp module) {
  std::string bytes;
  raw_string_ostream out(bytes);
  require(succeeded(writeBytecodeToFile(module, out)),
          "bytecode writer failed");
  return bytes;
}
std::string bytecode(StringRef source, MLIRContext &context) {
  auto module = parseSourceString<ModuleOp>(source, &context);
  require(bool(module), "invalid test source");
  return bytecode(*module);
}
zkc::language::CheckedOriginal original(StringRef expression = "x") {
  using namespace zkc::language;
  auto source = ("module source;protocol P "
                 "roles(A)(x:bool@A)->(ok:bool@A){return(ok=" +
                 expression + ");}")
                    .str();
  auto project =
      take(analyze(take(capture({{"source", std::move(source), ""}})))
               .checkedProject());
  return take(prepareOriginal(take(closeSubject(project, "source::P"))));
}
std::string nativeSource(StringRef declarations, StringRef body) {
  return ("module { \"protocol.module\"() ({\n" + declarations +
          "\n\"protocol.func\"() ({ ^entry(%flag:i1):\n" + body +
          "\n\"protocol.return\"(%flag) : (i1)->()\n}) "
          "{sym_name=\"main\",origin=[\"main\",[]],function_type=(i1)->i1,"
          "roles=[\"P\"],input_roles=[[\"P\"]],output_roles=[[\"P\"]]} : "
          "()->()\n"
          "}) {profile=#protocol.profile<protocol>} : ()->() }")
      .str();
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  for (StringRef fixture : {"finite/total-state.mlir", "finite/unit-state.mlir",
                            "structured-source/nested-controls.mlir",
                            "structured-source/open-components.mlir"})
    cases.run(fixture, [&] {
      auto file = MemoryBuffer::getFile(
          (Twine(ZKC_INPUT_FIXTURES) + "/" + fixture).str());
      require(bool(file), "could not read fixture");
      auto text = (*file)->getBuffer();
      auto binary = bytecode(text, context);
      auto written =
          take(zkc::protocol::exportStructuredSource(text, "main", context));
      auto checkpoint =
          take(zkc::protocol::exportStructuredSource(binary, "main", context));
      auto a = take(json::parse(written.bytes));
      auto b = take(json::parse(checkpoint.bytes));
      require((*a.getAsArray())[2] != (*b.getAsArray())[2],
              "encoding changed without a new identity");
      (*a.getAsArray())[2] = (*b.getAsArray())[2];
      require(zkc::equalNaturalJson(a, b),
              "bytecode changed structured semantics");
      require(written.associations.size() == checkpoint.associations.size(),
              "lost associations");
      for (auto [left, right] :
           zip(written.associations, checkpoint.associations))
        require(left.row == right.row && left.operation == right.operation &&
                    left.derivation == right.derivation && !right.original,
                "bytecode fabricated a written range or changed an operation "
                "association");
      auto module = parseSourceString<ModuleOp>(text, &context);
      auto prepared = zkc::mathematical::prepareProtocol(*module, false);
      require(bool(prepared), "could not prepare test source");
      auto candidate = bytecode(*prepared);
      auto map = take(zkc::protocol::produceApplicationMap(text, candidate,
                                                           "main", context));
      if (auto e = zkc::protocol::checkApplicationMap(text, candidate, "main",
                                                      map, context)
                       .takeError())
        throw std::runtime_error(toString(std::move(e)));
      auto changed =
          zkc::protocol::checkApplicationMap(text, text, "main", map, context)
              .takeError();
      require(bool(changed), "reused a map for different candidate bytes");
      require(namesIdentifier(toString(std::move(changed)),
                              "application-map-identity"),
              "wrong identity refusal");
      refuses(zkc::protocol::exportStructuredSource(
                  StringRef(binary).take_front(8), "main", context),
              "structured-source-original");
    });
  cases.run("native coordinates preserve complete result tuple order", [&] {
    auto file = MemoryBuffer::getFile(
        ZKC_INPUT_FIXTURES "/structured-source/math-operations.mlir");
    require(bool(file), "could not read multiple-result fixture");
    auto source = take(
        zkc::protocol::readSourceView((*file)->getBuffer(), "main", context));
    const auto *main = source.find("main");
    require(main && main->body.instructions.size() == 2,
            "expected two calls with multiple results");
    require(main->body.instructions[0].operands ==
                    std::vector<unsigned>({0, 1, 2}) &&
                main->body.instructions[1].operands ==
                    std::vector<unsigned>({3, 2, 4}) &&
                main->body.returned == std::vector<unsigned>({2, 0, 3, 1}),
            "source coordinates changed operand or result tuple order");
  });
  cases.run(
      "native instruction and reference counts exceed the wire limits", [&] {
        std::string body;
        for (unsigned i = 0; i < 4097; ++i)
          body += "%v" + std::to_string(i) + " = arith.xori %flag,%flag : i1\n";
        auto view = take(zkc::protocol::readSourceView(nativeSource({}, body),
                                                       "main", context));
        const auto &block = view.find("main")->body;
        require(block.instructions.size() == 4097 &&
                    block.returned == std::vector<unsigned>{4097},
                "native indexing inherited the wire instruction limit");
        refuses(zkc::protocol::publishSource(view), "structured-source-limit");
        body.clear();
        for (unsigned i = 0; i < 2050; ++i)
          body += "%v" + std::to_string(i) +
                  ":2 = func.call @pair(%flag) : (i1)->(i1,i1)\n";
        auto pairs = take(zkc::protocol::readSourceView(
            nativeSource("func.func private @pair(%x:i1)->(i1,i1) { return "
                         "%x,%x : i1,i1 }",
                         body),
            "main", context));
        require(pairs.find("main")->body.returned ==
                    std::vector<unsigned>{4100},
                "native multi-result coordinate was truncated");
        refuses(zkc::protocol::publishSource(pairs), "structured-source-limit");
      });
  cases.run("native definitions and signatures exceed the wire limits", [&] {
    std::string declarations;
    for (unsigned i = 0; i < 129; ++i)
      declarations += "func.func private @h" + std::to_string(i) +
                      "(%x:i1)->i1 { return %x : i1 }\n";
    auto view = take(zkc::protocol::readSourceView(
        nativeSource(declarations, {}), "main", context));
    require(view.definitions.size() == 130,
            "native definitions were limited by publication");
    refuses(zkc::protocol::publishSource(view), "structured-source-limit");
    declarations = "func.func private @wide(";
    for (unsigned i = 0; i < 513; ++i)
      declarations += (i ? ",%a" : "%a") + std::to_string(i) + ":i1";
    declarations += ")->i1 { return %a0 : i1 }";
    auto wide = take(zkc::protocol::readSourceView(
        nativeSource(declarations, {}), "main", context));
    require(wide.find("wide")->body.inputs.size() == 513,
            "native signature was limited by publication");
    refuses(zkc::protocol::publishSource(wide), "structured-source-limit");
  });
  cases.run("native byte strings refuse at textual report boundaries", [&] {
    auto bytes = nativeSource(
        R"(func.func private @"\FF"(%x:i1)->i1 { return %x : i1 })", {});
    auto view = take(zkc::protocol::readSourceView(bytes, "main", context));
    require(view.definitions.size() == 2, "native byte name was not retained");
    refuses(zkc::protocol::publishSource(view), "structured-source-string");
    refuses(zkc::protocol::produceApplicationMap(bytes, bytes, "main", context),
            "application-map-string");
  });
  cases.run("retained declarations do not impose publication row limits", [&] {
    std::string definitions, metadata = "[[], [";
    for (unsigned i = 0; i < 129; ++i) {
      auto name = "p" + std::to_string(i);
      definitions += "\"protocol.func\"() ({ \"protocol.return\"() : ()->() }) "
                     "{sym_name=\"" +
                     name + "\",origin=[\"" + name +
                     "\",[]],function_type=()->(),roles=[\"P\"],"
                     "input_roles=[],output_roles=[]} : ()->()\n";
      metadata += (i ? "," : "") + std::string("[\"") + name + "\",[],[]]";
    }
    metadata += "], []]";
    auto bytes =
        "module { \"protocol.module\"() ({" + definitions +
        "}) {profile=#protocol.profile<protocol>, source_declarations=" +
        metadata + "} : ()->() }";
    auto view = take(zkc::protocol::readSourceView(bytes, "p0", context));
    require(view.definitions.size() == 129,
            "retained declarations restricted native admission");
    take(zkc::protocol::produceApplicationMap(bytes, bytes, "p0", context));
    refuses(zkc::protocol::publishSource(view), "structured-source-limit");
    auto at = bytes.find("[\"p128\",[],[]]");
    require(at != std::string::npos, "metadata fixture is incomplete");
    bytes.replace(at, std::string("[\"p128\",[],[]]").size(),
                  "[\"absent\",[],[]]");
    refuses(zkc::protocol::readSourceView(bytes, "p0", context),
            "component-declaration-role");
  });
  cases.run("native declaration keys use semantic string identity", [&] {
    auto bytes = R"(module {
      "protocol.module"() ({
        "protocol.func"() ({ "protocol.return"() : ()->() })
          {sym_name="main", origin=["main",[]], function_type=()->(),
           roles=["P"], input_roles=[], output_roles=[]} : ()->()
      }) {profile=#protocol.profile<protocol>, source_declarations=[[
        [["nominal","record","R",[]],"ordinary",false,[],[],unit],
        [["nominal","record","R" : i8,[]],"ordinary",false,[],[],unit]
      ], [], [["R",unit]]]} : ()->()
    })";
    refuses(zkc::protocol::readSourceView(bytes, "main", context),
            "component-declaration-duplicate");
  });
  cases.run(
      "deferred publication owns its lexical associations and strings", [&] {
        auto view = [] {
          auto checked = original();
          return take(zkc::language::detail::OriginalAccess::read(checked));
        }();
        auto publication = take(zkc::protocol::publishSource(view));
        require(!publication.associations.empty(),
                "deferred publication lost its source ranges");
        require(llvm::any_of(
                    publication.associations,
                    [](const auto &row) { return row.original.has_value(); }),
                "local parser lifetime erased lexical association");
        auto detached = [] {
          auto checked = original();
          auto view =
              take(zkc::language::detail::OriginalAccess::read(checked));
          return take(zkc::protocol::publishSource(view));
        }();
        require(zkc::printJson(publication.snapshot) ==
                    zkc::printJson(detached.snapshot),
                "publication strings borrowed a destroyed context");
      });
  cases.run("source admission rejects unknown effects and bindings", [&] {
    auto file = MemoryBuffer::getFile(ZKC_INPUT_FIXTURES "/finite/order.mlir");
    require(bool(file), "could not read primitive source fixture");
    auto text = (*file)->getBuffer().str();
    take(zkc::protocol::exportStructuredSource(text, "main", context));
    for (const auto &[before, after] :
         std::vector<std::pair<std::string, std::string>>{
             {"\"exec.apply\"", "\"unknown.effect\""},
             {"binding = @add", "binding = @missing"}}) {
      auto changed = text;
      auto position = changed.find(before);
      require(position != std::string::npos,
              "missing primitive mutation target");
      changed.replace(position, before.size(), after);
      refuses(zkc::protocol::exportStructuredSource(changed, "main", context),
              "structured-source-original");
    }
  });
  cases.run("canonical original remains an exact assembly contract", [&] {
    auto value = original();
    auto binary = bytecode(value.bytes(), context);
    refuses(zkc::language::admitOriginal(value.entry(), binary,
                                         value.interfaceJson()),
            "target.admission");
  });
  cases.run(
      "direct frontend and imported original retain identical evidence", [&] {
        auto direct = original("true");
        auto imported = take(zkc::language::admitOriginal(
            direct.entry(), direct.bytes(), direct.interfaceJson()));
        require(imported.identity() == direct.identity() &&
                    imported.locationsIdentity() == direct.locationsIdentity(),
                "direct emission changed original or location identity");
        require(take(zkc::language::exportSourceCorrespondence(imported)) ==
                    take(zkc::language::exportSourceCorrespondence(direct)),
                "direct and parsed originals have different associations");
        auto native = take(zkc::language::detail::OriginalAccess::read(direct));
        auto parsed = take(zkc::protocol::readSourceView(
            direct.bytes(), direct.entry().protocol().symbol, context));
        auto binary = take(zkc::protocol::readSourceView(
            bytecode(direct.bytes(), context), direct.entry().protocol().symbol,
            context));
        require(native.identity == parsed.identity &&
                    native.identity != binary.identity,
                "semantic admission conflated byte identities");
        require(native.definitions.size() == parsed.definitions.size() &&
                    parsed.definitions.size() == binary.definitions.size(),
                "ingress changed the native definition inventory");
        require(binary.written.empty(),
                "bytecode fabricated lexical provenance");
      });
  cases.run("bytecode identity does not authorize a changed actual body", [&] {
    auto source = original("true");
    auto symbol = source.entry().protocol().symbol;
    auto module = parseSourceString<ModuleOp>(source.bytes(), &context);
    require(bool(module), "could not parse checked source");
    auto prepared = zkc::mathematical::prepareProtocol(*module, false);
    require(bool(prepared), "could not prepare checked source");
    auto candidate = bytecode(*prepared);
    auto map = take(json::parse(take(zkc::protocol::produceApplicationMap(
        source.bytes(), candidate, symbol, context))));
    unsigned changed = 0;
    prepared->walk([&](arith::ConstantOp constant) {
      if (constant.getType().isInteger(1)) {
        constant.setValueAttr(IntegerAttr::get(constant.getType(), 0));
        ++changed;
      }
    });
    require(changed == 1, "fixture must contain one Boolean constant");
    candidate = bytecode(*prepared);
    // Supply the true digest of a well-formed, same-typed candidate. The
    // correspondence reader must still inspect its changed native property.
    (*map.getAsObject()->getObject("candidate"))["digest"] =
        "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(candidate)), true);
    auto failure =
        zkc::protocol::checkApplicationMap(source.bytes(), candidate, symbol,
                                           zkc::printJson(map), context)
            .takeError();
    require(bool(failure), "identity authorized a changed bytecode body");
    require(namesIdentifier(toString(std::move(failure)),
                            "application-map-correspondence"),
            "changed bytecode did not reach actual-body comparison");
  });
  cases.run("frontend publication data outlives its checked source", [] {
    using namespace zkc::language;
    std::vector<json::Value> data;
    std::vector<std::string> expected;
    {
      auto source = original();
      const auto &entry = source.entry();
      const auto &project = entry.project();
      data.push_back(take(sourceClaimsData(entry)));
      data.push_back(take(componentDeclarationsData(entry)));
      data.push_back(take(writtenSourceData(project)));
      data.push_back(take(sourceBindingsData(project)));
      data.push_back(take(sourceInstancesData(entry)));
      for (const auto &value : data)
        expected.push_back(zkc::printJson(value));
    }
    for (auto [value, bytes] : zip(data, expected))
      require(zkc::printJson(value) == bytes,
              "publication data borrowed a destroyed checked source");
  });
  cases.run("native views retain context and isolate mutation", [&] {
    auto view = [] {
      auto value = original();
      auto expected = take(zkc::language::exportSourceCorrespondence(value));
      auto clone = take(zkc::language::detail::OriginalAccess::read(value));
      clone.native.get()->setAttr("observation_only",
                                  UnitAttr::get(clone.native->getContext()));
      require(take(zkc::language::exportSourceCorrespondence(value)) ==
                  expected,
              "mutating a clone changed the admitted original");
      return clone;
    }();
    require(view.native.get()->hasAttr("observation_only"),
            "view did not retain its module");
    std::string bytes;
    raw_string_ostream out(bytes);
    view.native->print(out);
    require(!bytes.empty(), "context did not outlive the original handle");
  });
  cases.run("concurrent publications share only an immutable original", [&] {
    auto value = original();
    auto expected = take(zkc::language::exportSourceCorrespondence(value));
    std::vector<std::future<std::string>> readers;
    for (unsigned i = 0; i < 3; ++i)
      readers.push_back(std::async(std::launch::async, [value] {
        return take(zkc::language::exportSourceCorrespondence(value));
      }));
    for (auto &reader : readers)
      require(reader.get() == expected,
              "concurrent publication changed source correspondence");
  });
  return cases.result();
}
