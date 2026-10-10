#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Json.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
SourceBuffer source() {
  return {"sample", "module sample;", "/does/not/exist.zkc"};
}
AssetBuffer r1cs() {
  auto relation = take(zkc::relation::R1CS::create("koala-bear", 2, 0, 1, {}));
  return {"circuit", "r1cs-json", zkc::printJson(relation.encode()),
          "/does/not/exist.r1cs"};
}
AssetBuffer air() {
  using namespace zkc::relation;
  auto relation =
      take(AIR::create("koala-bear", 1, 1,
                       {{{AIRScopeKind::First, 0},
                         {AIRNode::read(0, 0), AIRNode::publicInput(0),
                          AIRNode::neg(1), AIRNode::add(0, 2)},
                         std::nullopt,
                         std::nullopt}}));
  return {"trace_constraints", "air-json", zkc::printJson(relation.encode()),
          "/missing.air"};
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("explicit bytes admit without opening diagnostic paths", [] {
    auto captured = take(capture({source()}, {r1cs(), air()}, {}));
    auto project = take(analyze(captured).checkedProject());
    require(project.assets().size() == 2, "captured definitions missing");
    auto &circuit = project.assets()[0];
    auto &trace = project.assets()[1];
    require(circuit.r1cs() && !circuit.air() && trace.air() && !trace.r1cs(),
            "asset families confused");
    require(circuit.r1cs()->columns() == 2 &&
                circuit.r1cs()->publicCount() == 1,
            "R1CS statement layout differs");
    require(trace.air()->constraints()[0].scope.kind ==
                zkc::relation::AIRScopeKind::First,
            "AIR row scope differs");
    auto predicate =
        take(zkc::relation::evaluate(*circuit.r1cs(), {"7"}, {"1", "7"}));
    require(predicate.bound && predicate.satisfied,
            "captured relation meaning differs");
    require(!take(zkc::relation::evaluate(*circuit.r1cs(), {"7"}, {"0", "7"}))
                 .satisfied,
            "ONE binding was lost");
  });
  cases.run("capture sorting and diagnostics preserve identity", [] {
    auto a = r1cs(), b = air();
    auto first = take(capture({source()}, {a, b}, {}));
    a.diagnosticPath = "elsewhere";
    b.diagnosticPath = "different";
    auto second = take(capture({source()}, {b, a}, {}));
    require(first.identity() == second.identity(),
            "order or paths changed capture identity");
  });
  cases.run("raw capture and canonical definition identities are distinct", [] {
    auto a = r1cs();
    auto first = take(capture({source()}, {a}, {}));
    a.bytes = "\n" + a.bytes + "\n";
    auto second = take(capture({source()}, {a}, {}));
    require(first.identity() != second.identity(),
            "raw bytes absent from capture identity");
    auto x = take(analyze(first).checkedProject()),
         y = take(analyze(second).checkedProject());
    require(x.assets()[0].identity() == y.assets()[0].identity(),
            "transport changed definition identity");
    a.name = "another";
    require(second.identity() != take(capture({source()}, {a}, {})).identity(),
            "name not bound");
    a.format = "r1cs-binary";
    auto other = take(capture({source()}, {a}, {}));
    refuses(analyze(other).checkedProject(), "source.asset");
  });
  cases.run("changed relation contents change definition identity", [] {
    auto a = r1cs(), b = r1cs();
    b.bytes = zkc::printJson(
        take(zkc::relation::R1CS::create("koala-bear", 2, 1, 0, {})).encode());
    auto x = take(Asset::read(a)), y = take(Asset::read(b));
    require(x.identity() != y.identity(),
            "public input/output distinction erased");
  });
  cases.run("duplicate names refuse before parsing", [] {
    auto a = r1cs();
    a.bytes = "invalid";
    refuses(capture({source()}, {a, a}, {}), "source.asset");
  });
  cases.run("Unicode source names do not widen captured asset keys", [] {
    auto a = r1cs();
    a.name = "回路";
    refuses(capture({source()}, {a}, {}), "source.asset");
  });
  cases.run("unknown asset format refuses", [] {
    auto a = r1cs();
    a.format = "guess";
    refuses(capture({source()}, {a}, {}), "source.asset");
  });
  cases.run("malformed unused assets refuse analysis", [] {
    for (StringRef format : {"r1cs-json", "r1cs-binary", "air-json"}) {
      auto a = r1cs();
      a.format = format.str();
      a.bytes = "broken";
      refuses(analyze(take(capture({source()}, {a}, {}))).checkedProject(),
              "source.asset");
    }
  });
  cases.run("file count and asset byte budgets are bounded", [] {
    auto a = r1cs();
    CaptureOptions options;
    options.limits.files = 1;
    refuses(capture({source()}, {a}, options), "source.limit");
    options = {};
    options.limits.assetTotalBytes = a.bytes.size() - 1;
    refuses(capture({source()}, {a}, options), "source.limit");
  });
  cases.run("asset bound is checked again at analysis", [] {
    auto captured = take(capture({source()}, {r1cs()}, {}));
    Limits limits;
    limits.assetBytes = 0;
    refuses(analyze(captured, limits).checkedProject(), "source.limit");
    CaptureOptions options;
    options.limits.assetBytes = 0;
    refuses(capture({source()}, {r1cs()}, options), "source.limit");
    options.limits.assetBytes = Limits{}.assetBytes + 1;
    refuses(capture({source()}, {}, options), "source.limit");
  });
  cases.run("AIR duplicate object keys are not overwritten", [] {
    auto a = air();
    auto at = a.bytes.find('{');
    require(at != std::string::npos, "AIR object fixture missing");
    a.bytes.insert(at + 1, "\"format\":\"wrong\",\"format\":\"wrong\",");
    refuses(analyze(take(capture({source()}, {a}, {}))).checkedProject(),
            "source.asset");
  });
  return cases.result();
}
