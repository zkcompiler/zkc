#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Builders.h"
#include "support/NativeCases.h"
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
  cases.run("malformed native metadata cannot bypass publication", [&] {
    auto event = StartOriginAttr::get(&context, "main", "call");
    for (Attribute malformed :
         {Attribute(builder.getStringAttr("start")),
          Attribute(StartOriginAttr::get(&context, "", "call")),
          Attribute(QueryOriginAttr::get(&context, "main", "coin", 0, "service",
                                         "draw", "bad owner"))}) {
      auto origin = NativeOriginAttr::get(&context, "entry", {}, malformed);
      refuses(exportNativeOrigin(origin), "interactive-native-origin");
    }
    auto badStep = OriginStepAttr::get(
        &context, static_cast<OriginStepKind>(42), "main", "site");
    refuses(exportNativeOrigin(
                NativeOriginAttr::get(&context, "entry", {badStep}, event)),
            "interactive-native-origin");
    refuses(exportNativeOrigin(NativeOriginAttr::get(
                &context, std::string(129, 'x'), {}, event)),
            "interactive-native-origin");
    refuses(exportNativeOrigin({}), "interactive-native-origin");
    NativeOriginTemplate huge{
        "entry", {}, NativeStartOrigin{std::string(10000, 'x'), "call"}};
    refuses(importNativeOrigin(&context, huge), "interactive-native-origin");
    refuses(encodeNativeOriginTemplate(huge), "interactive-native-origin");
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
    auto malformed = AssetReferenceAttr::get(&context, "zkc.matrix/0",
                                             builder.getDenseI8ArrayAttr({0}));
    refuses(encodeAssetDigest(malformed), "asset-reference");
    refuses(encodeAssetDigest({}), "asset-reference");
  });
  return cases.result();
}
