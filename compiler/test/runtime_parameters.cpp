#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Builders.h"
#include "support/Formation.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/LogicalTree.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::runtime;
using namespace zkc::protocol;
int main() {
  DialectRegistry registry;
  registry.insert<RuntimeDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  OpBuilder builder(&context);
  Cases cases;
  auto roundtrip = [&](const json::Value &source) {
    // This writer knows only the shared string/array framing, not origin
    // shapes.
    auto hex = llvm::toHex(take(encodeLogicalTree(source)), true);
    auto decoded = take(decodeNativeOriginTemplate(hex));
    auto native = take(importNativeOrigin(&context, decoded));
    std::string text;
    raw_string_ostream stream(text);
    stream << native;
    auto parsed =
        dyn_cast_or_null<NativeOriginAttr>(parseAttribute(text, &context));
    require(native == parsed, "MLIR origin roundtrip");
    auto exported = take(exportNativeOrigin(parsed));
    require(take(encodeNativeOriginTemplate(exported)) == hex,
            "origin bytes changed");
    return native;
  };
  cases.run(
      "three event forms preserve complete source-relative identities", [&] {
        auto query = roundtrip(json::Array{
            "zkc.native-origin-template/0", "entry",
            json::Array{json::Array{"apply", "parent", "call"},
                        json::Array{"repeat", "child", "round"}},
            json::Array{},
            json::Array{"query", "child", "coin", "input_18446744073709551615",
                        "random.domain/0", "index", "V"}});
        require(cast<QueryOriginAttr>(query.getEvent()).getServiceInput() ==
                        UINT64_MAX &&
                    query.getPath()[1].getKind() == OriginStepKind::Repeat,
                "input index or path step lost native structure");
        roundtrip(json::Array{
            "zkc.native-origin-template/0", "entry", json::Array{},
            json::Array{},
            json::Array{"message", "main", "message", "schema", "P", "V"}});
        roundtrip(json::Array{"zkc.native-origin-template/0", "entry",
                              json::Array{}, json::Array{},
                              json::Array{"start", "caller", "application"}});
      });
  cases.run(
      "event method is preserved and checked by the invoking contract", [&] {
        auto origin = roundtrip(
            json::Array{"zkc.native-origin-template/0", "entry", json::Array{},
                        json::Array{},
                        json::Array{"query", "main", "coin", "input_0",
                                    "service", "index", "V"}});
        auto bytes =
            take(encodeNativeOriginTemplate(take(exportNativeOrigin(origin))));
        require(!checkNativeOrigin(bytes, "query", "index"),
                "matching method refused");
        auto refused = checkNativeOrigin(bytes, "query", "draw");
        require(bool(refused), "distinct method was admitted");
        consumeError(std::move(refused));
      });
  cases.run("native origin and neutral byte formation agree at capacity", [&] {
    NativeOriginTemplate source{"entry", {}, NativeStartOrigin{"main", "call"}};
    for (unsigned count = 0; count <= 65; ++count) {
      source.path.resize(count,
                         {NativeOriginStep::Kind::Repeat, "main", "round"});
      auto native = importNativeOrigin(&context, source);
      auto bytes = encodeNativeOriginTemplate(source);
      require(bool(native) == bool(bytes),
              "direct native size accounting disagrees with bytes");
      if (native)
        require(take(encodeNativeOriginTemplate(
                    take(exportNativeOrigin(*native)))) == *bytes,
                "boundary changed within admitted size");
      else {
        consumeError(native.takeError());
        consumeError(bytes.takeError());
      }
    }
  });
  cases.run("malformed origin metadata is refused at storage formation", [&] {
    auto event = StartOriginAttr::get(&context, "main", "call");
    refusesFormation<StartOriginAttr>(&context, "interactive-native-origin",
                                      StringRef(""), StringRef("call"));
    refusesFormation<QueryOriginAttr>(
        &context, "interactive-native-origin", StringRef("main"),
        StringRef("coin"), uint64_t(0), StringRef("service"), StringRef("draw"),
        StringRef("bad owner"));
    refusesFormation<NativeOriginAttr>(
        &context, "interactive-native-origin", StringRef("entry"),
        ArrayRef<OriginStepAttr>{}, Attribute(builder.getStringAttr("start")));
    refusesFormation<OriginStepAttr>(
        &context, "interactive-native-origin", static_cast<OriginStepKind>(42),
        StringRef("main"), StringRef("site"), StringRef(""));
    refusesFormation<NativeOriginAttr>(
        &context, "interactive-native-origin", StringRef(std::string(129, 'x')),
        ArrayRef<OriginStepAttr>{}, Attribute(event));
  });
  cases.run(
      "origin publication and import retain their own refusal boundaries", [&] {
        refuses(exportNativeOrigin({}), "interactive-native-origin");
        NativeOriginTemplate huge{
            "entry", {}, NativeStartOrigin{std::string(10000, 'x'), "call"}};
        refuses(importNativeOrigin(&context, huge),
                "interactive-native-origin");
        refuses(encodeNativeOriginTemplate(huge), "interactive-native-origin");
      });
  cases.run(
      "direct neutral origin import checks every name without diagnosing", [&] {
        unsigned diagnostics = 0;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &) {
          ++diagnostics;
          return success();
        });
        NativeOriginTemplate source{
            "entry",
            {{NativeOriginStep::Kind::Apply, "outer", "call", ""},
             {NativeOriginStep::Kind::Repeat, "middle", "round", ""},
             {NativeOriginStep::Kind::Branch, "inner", "choose", "else"}},
            NativeStartOrigin{"main", "start"}};
        auto roundtrip = [&] {
          auto native = take(importNativeOrigin(&context, source));
          require(take(encodeNativeOriginTemplate(take(exportNativeOrigin(
                      native)))) == take(encodeNativeOriginTemplate(source)),
                  "direct import changed exact neutral fields");
        };
        auto checkNames = [&](std::initializer_list<std::string *> names) {
          roundtrip();
          for (auto *name : names) {
            auto original = *name;
            for (const auto &bad :
                 {std::string(), std::string("bad name"),
                  std::string("bad\nname"), std::string("bad\0name", 8),
                  std::string(1, '\x7f'), std::string(129, 'x')}) {
              *name = bad;
              refuses(importNativeOrigin(&context, source),
                      "interactive-native-origin");
            }
            *name = original;
          }
          roundtrip();
        };
        auto &start = std::get<NativeStartOrigin>(source.event);
        checkNames({&source.entry, &start.protocol, &start.site,
                    &source.path[0].protocol, &source.path[0].site,
                    &source.path[1].protocol, &source.path[1].site,
                    &source.path[2].protocol, &source.path[2].site,
                    &source.path[2].alternative});
        source.event = NativeQueryOrigin{
            "main", "coin", UINT64_MAX, "random.domain/0", "index", "V"};
        auto &query = std::get<NativeQueryOrigin>(source.event);
        checkNames({&query.protocol, &query.site, &query.service, &query.method,
                    &query.owner});
        source.event = NativeMessageOrigin{"main", "send", "schema", "P", "V"};
        auto &message = std::get<NativeMessageOrigin>(source.event);
        checkNames({&message.protocol, &message.site, &message.schema,
                    &message.sender, &message.receiver});
        require(diagnostics == 0, "Expected-return import diagnosed");
      });
  cases.run("direct neutral origin import checks path kinds and context", [&] {
    unsigned diagnostics = 0;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &) {
      ++diagnostics;
      return success();
    });
    NativeOriginTemplate source{"entry", {}, NativeStartOrigin{"main", "call"}};
    for (auto kind :
         {NativeOriginStep::Kind::Apply, NativeOriginStep::Kind::Repeat}) {
      source.path = {{kind, "main", "site", "then"}};
      refuses(importNativeOrigin(&context, source),
              "interactive-native-origin");
    }
    source.path = {
        {static_cast<NativeOriginStep::Kind>(42), "main", "site", ""}};
    refuses(importNativeOrigin(&context, source), "interactive-native-origin");
    source.path.clear();
    refuses(importNativeOrigin(nullptr, source), "interactive-native-origin");
    MLIRContext unloaded;
    refuses(importNativeOrigin(&unloaded, source), "interactive-native-origin");
    take(importNativeOrigin(&context, source));
    require(diagnostics == 0, "Expected-return import diagnosed");
  });
  cases.run(
      "direct neutral origin import retains exact aggregate size bound", [&] {
        unsigned diagnostics = 0;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &) {
          ++diagnostics;
          return success();
        });
        // Canonical framing is exactly 2048 bytes, although each name
        // and the path independently remain below their own limits.
        NativeOriginTemplate source{
            std::string(120, 'e'), {}, NativeStartOrigin{"main", "call"}};
        source.path.resize(42, {NativeOriginStep::Kind::Apply, "p", "s", ""});
        auto native = take(importNativeOrigin(&context, source));
        auto exported = take(exportNativeOrigin(native));
        require(exported.entry == source.entry &&
                    exported.path.size() == source.path.size(),
                "boundary import changed entry or path");
        for (const auto &step : exported.path)
          require(step.kind == NativeOriginStep::Kind::Apply &&
                      step.protocol == "p" && step.site == "s" &&
                      step.alternative.empty(),
                  "boundary import changed a path step");
        auto event = std::get<NativeStartOrigin>(exported.event);
        require(event.protocol == "main" && event.site == "call" &&
                    take(importNativeOrigin(&context, exported)) == native,
                "boundary import changed native identity");
        source.entry.push_back('e');
        refuses(importNativeOrigin(&context, source),
                "interactive-native-origin");
        require(diagnostics == 0, "Expected-return import diagnosed");
      });
  cases.run("selected origin frames retain exact alternatives", [&] {
    auto native = roundtrip(json::Array{
        "zkc.native-origin-template/0", "entry",
        json::Array{json::Array{"branch", "main", "choose", "then"}},
        json::Array{},
        json::Array{"message", "main", "send", "schema", "P", "V"}});
    require(native.getPath()[0].getKind() == OriginStepKind::Branch &&
                native.getPath()[0].getAlternative() == "then",
            "selected arm lost its native field");
    auto event = native.getEvent();
    refusesFormation<OriginStepAttr>(&context, "interactive-native-origin",
                                     OriginStepKind::Branch, StringRef("main"),
                                     StringRef("choose"), StringRef(""));
    refusesFormation<OriginStepAttr>(&context, "interactive-native-origin",
                                     OriginStepKind::Apply, StringRef("main"),
                                     StringRef("call"), StringRef("then"));
    auto changed = NativeOriginAttr::get(
        &context, "entry",
        {OriginStepAttr::get(&context, OriginStepKind::Branch, "main", "choose",
                             "else")},
        event);
    auto exported = take(exportNativeOrigin(changed));
    require(changed != native && exported.path[0].alternative == "else" &&
                take(importNativeOrigin(&context, exported)) == changed,
            "publication erased a changed native branch alternative");
  });
  cases.run("asset references preserve digest bits and format identity", [&] {
    StringRef digest =
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    auto matrix = take(decodeAssetReference(&context, "zkc.matrix/0", digest));
    auto ring = take(decodeAssetReference(&context, "zkc.ring/0", digest));
    require(matrix != ring && matrix.getDigest() == ring.getDigest() &&
                take(encodeAssetDigest(matrix)) == digest,
            "asset format or digest lost");
    std::string text;
    raw_string_ostream stream(text);
    stream << matrix;
    require(parseAttribute(text, &context) == matrix,
            "asset attribute print/parse");
    refuses(decodeAssetReference(&context, "zkc.matrix/0", digest.upper()),
            "asset-reference");
    refuses(decodeAssetReference(&context, "zkc.matrix/0", digest.drop_back()),
            "asset-reference");
    refuses(decodeAssetReference(&context, "", digest), "asset-reference");
    refusesFormation<AssetReferenceAttr>(&context, "asset-reference",
                                         StringRef("zkc.matrix/0"),
                                         builder.getDenseI8ArrayAttr({0}));
    refuses(encodeAssetDigest({}), "asset-reference");
  });
  return cases.result();
}
