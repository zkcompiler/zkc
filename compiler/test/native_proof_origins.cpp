#include "../lib/Compiler/NativeProofOrigins.h"
#include "../lib/Transforms/RealizedProtocol.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
using Origins = StringMap<zkc::detail::NativeSourceOrigin>;
OwningOpRef<ModuleOp> fixture(MLIRContext &context) {
  auto file = MemoryBuffer::getFile(ZKC_ORACLE_FIXTURES "/query-blocks.mlir");
  require(bool(file), "missing oracle fixture");
  auto source = parseSourceString<ModuleOp>((*file)->getBuffer(), &context);
  require(bool(source), "invalid oracle fixture");
  return source;
}
Origins authored(ModuleOp source) {
  Origins result;
  source.walk([&](Operation *op) {
    if (isa<protocol_ir::OracleSendOp, protocol_ir::OracleQueryOp>(op)) {
      auto site = op->getAttrOfType<StringAttr>("site").str();
      result[site] = {"leaf",
                      site,
                      {"oracle", "leaf", site},
                      {{"apply", "main", "application"}}};
    }
  });
  return result;
}
mathematical::RealizedProtocol realize(ModuleOp source, bool atomic = true) {
  auto prepared = mathematical::PreparedProtocol::prepare(source);
  require(bool(prepared), "oracle source did not prepare");
  protocol::OracleRealizationPolicy policy;
  policy.roots = protocol::OracleTableRealization{
      "rows.merkle-keccak256.koala-bear.ext4-binomial3/0"};
  policy.authentication = atomic ? protocol::OracleAuthentication::AtomicBlocks
                                 : protocol::OracleAuthentication::PerQuery;
  return take(
      mathematical::RealizedProtocol::realize(std::move(*prepared), policy));
}
std::vector<std::pair<std::string, std::string>>
messages(const Origins &origins) {
  std::vector<std::pair<std::string, std::string>> result;
  for (const auto &item : origins)
    if (item.second.event.front() == "message")
      result.emplace_back(item.first().str(), item.second.protocol);
  llvm::sort(result);
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto source = fixture(context);
  auto logical = authored(*source);
  auto edge = realize(*source);
  cases.run(
      "generated message sites resolve without a duplicated apply prefix", [&] {
        auto origins =
            take(zkc::detail::realizedNativeOrigins(edge, "main", logical));
        unsigned requests = 0, responses = 0, deliveries = 0;
        for (const auto &item : origins) {
          const auto &origin = item.second;
          if (origin.event.front() != "message")
            continue;
          auto encoded = take(protocol::encodeNativeOriginTemplate(
              "main", origin.steps, origin.event));
          auto decoded = take(protocol::decodeNativeOriginTemplate(encoded));
          auto message = std::get<protocol::NativeMessageOrigin>(decoded.event);
          require(message.site == item.first(),
                  "generated site acquired an apply prefix");
          require(StringRef(message.protocol).starts_with("zkc.oracle."),
                  "missing generated namespace");
          require(!decoded.path.empty() &&
                      decoded.path.front().kind ==
                          protocol::NativeOriginStep::Kind::Apply,
                  "generated origins lost the authored application lineage");
          requests += StringRef(message.site).ends_with("opening_request");
          responses += StringRef(message.site).ends_with("opening_response");
          deliveries += StringRef(message.site).ends_with("deliver");
        }
        require(requests == 2 && responses == 2 && deliveries == 2,
                "origin inventory lost the ordered query blocks or root "
                "deliveries");
      });
  cases.run("missing authored query lineage refuses", [&] {
    auto incomplete = logical;
    incomplete.erase("duplicate");
    refuses(zkc::detail::realizedNativeOrigins(edge, "main", incomplete),
            "native-proof-realization-origin");
  });
  cases.run("all queries in a batch bind generated origins", [&] {
    auto changed = logical;
    changed["duplicate"].steps.push_back({"apply", "nested", "different"});
    auto before =
        take(zkc::detail::realizedNativeOrigins(edge, "main", logical));
    auto after =
        take(zkc::detail::realizedNativeOrigins(edge, "main", changed));
    unsigned changedRequests = 0;
    for (const auto &item : before)
      if (item.first().ends_with("opening_request"))
        changedRequests +=
            item.second.protocol != after.lookup(item.first()).protocol;
    require(
        changedRequests == 1,
        "a non-first batch occurrence failed to bind its complete query group");
  });
  cases.run("exact selection changes generated provenance", [&] {
    auto sequential = realize(*source, false);
    auto before =
        take(zkc::detail::realizedNativeOrigins(edge, "main", logical));
    auto after =
        take(zkc::detail::realizedNativeOrigins(sequential, "main", logical));
    require(messages(before) != messages(after),
            "realization choice was not bound");
  });
  cases.run("unexpected authored event cannot disappear", [&] {
    auto extra = logical;
    extra["unaccounted"] = {
        "main",
        "unaccounted",
        {"message", "main", "unaccounted", "unaccounted", "P", "V"},
        {}};
    refuses(zkc::detail::realizedNativeOrigins(edge, "main", extra),
            "native-proof-origin-coverage");
  });
  return cases.result();
}
