#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ProtocolObservations.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace pir = protocol_ir;
using Origin = ProtocolValueOrigin;
using Pending = ProtocolPendingTransfer;
constexpr StringLiteral prefix = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!S = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
)mlir";
constexpr StringLiteral suffix = R"mlir(
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr StringLiteral helpers = R"mlir(
 "protocol.func"() ({^entry(%s:!S):
   %q="protocol.query"(%s) {owner="V",method="draw",site="sample"} : (!S)->!F
   "protocol.return"(%q) : (!F)->()
 }) {sym_name="draw",function_type=(!S)->!F,roles=["P","V"],input_roles=[["V"]],output_roles=[["V"]]} : ()->()
 "protocol.func"() ({^entry(%q:!F):
   %sent=protocol.exchange %q {sender="V",receiver="P",site="send"} : !F
   "protocol.return"() : ()->()
 }) {sym_name="deliver",function_type=(!F)->(),roles=["P","V"],input_roles=[["V"]],output_roles=[]} : ()->()
)mlir";
std::string mainFunction(StringRef body, StringRef arguments = "%s:!S",
                         StringRef types = "!S",
                         StringRef roles = "[[\"V\"]]") {
  return (Twine("\"protocol.func\"() ({^entry(") + arguments + "):\n" + body +
          "\n%yes=arith.constant true\n\"protocol.return\"(%yes) : "
          "(i1)->()\n}) {sym_name=\"main\",function_type=(" +
          types + ")->i1,roles=[\"P\",\"V\"],input_roles=" + roles +
          ",output_roles=[[\"V\"]]} : ()->()\n")
      .str();
}
constexpr StringLiteral roundBody = R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="sample_call"} : (!S)->!F
protocol.apply @deliver(%q) {roles=["P","V"],site="delivery_call"} : (!F)->()
)mlir";
pir::MathematicalOp declaration(ModuleOp module, StringRef name = "main") {
  auto root = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  auto result = SymbolTable(root).lookup<pir::MathematicalOp>(name);
  require(bool(result), "missing protocol fixture declaration");
  return result;
}
} // namespace

int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  if (argc == 4) {
    auto module = parseSourceFile<ModuleOp>(argv[1], &context);
    if (!module || failed(admitStage(*module)))
      return 1;
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    auto result = analysis.get(declaration(*module, argv[2]), argv[3], work);
    if (!result) {
      errs() << toString(result.takeError()) << '\n';
      return 1;
    }
    outs() << "query families: " << (*result)->queryFamilies
           << ", work used: " << 1000000 - remaining << '\n';
    return 0;
  }
  if (argc != 1)
    return 2;
  auto parse = [&](StringRef declarations) {
    auto text = (prefix + declarations + suffix).str();
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module) && succeeded(admitStage(*module)),
            "protocol fixture was not admitted");
    return module;
  };
  auto closed = [&](const ProtocolObservationSummary &summary,
                    unsigned queries) {
    require(summary.queryFamilies == queries &&
                summary.pending.input == Pending::Input::Empty &&
                summary.pending.output == Pending::Output::Empty,
            "incorrect closed pending transfer");
  };
  Cases cases;
  cases.run("cross-helper query and delivery compose exact identities", [&] {
    auto module = parse((helpers + mainFunction(roundBody)).str());
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    const auto *summary = take(analysis.get(declaration(*module), "V", work));
    closed(*summary, 1);
    require(summary->services.count() == 1 && summary->services.test(0),
            "selected service formal was lost");
    const auto *draw = summary->actions[0].callee;
    const auto *delivery = summary->actions[1].callee;
    require(draw->pending.input == Pending::Input::Empty &&
                draw->pending.output == Pending::Output::Query &&
                delivery->pending.input == Pending::Input::Formal &&
                delivery->pending.port == 0 &&
                delivery->pending.output == Pending::Output::Empty,
            "callee round boundaries were flattened");
    require(summary->actions[1].inputOrigins[0].kind == Origin::Kind::Query &&
                summary->actions[1].inputOrigins[0].path.size() == 2,
            "returned challenge has no actual call occurrence");
  });
  cases.run("shared callee has distinct invocation origins", [&] {
    auto body = (roundBody + R"mlir(
%q2=protocol.apply @draw(%s) {roles=["P","V"],site="sample_again"} : (!S)->!F
protocol.apply @deliver(%q2) {roles=["P","V"],site="delivery_again"} : (!F)->()
)mlir")
                    .str();
    auto module = parse((helpers + mainFunction(body)).str());
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    const auto *summary = take(analysis.get(declaration(*module), "V", work));
    closed(*summary, 2);
    require(summary->actions[0].callee == summary->actions[2].callee &&
                summary->actions[1].inputOrigins[0] !=
                    summary->actions[3].inputOrigins[0],
            "callee sharing equated two challenges");
  });
  for (StringRef invalid : {StringRef(R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="first"} : (!S)->!F
%r=protocol.apply @draw(%s) {roles=["P","V"],site="second"} : (!S)->!F
)mlir"),
                            StringRef(R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="first"} : (!S)->!F
%changed=algebra.field_subtract %q,%q : (!F,!F)->!F
protocol.apply @deliver(%changed) {roles=["P","V"],site="second"} : (!F)->()
)mlir"),
                            StringRef(R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="first"} : (!S)->!F
protocol.apply @deliver(%q) {roles=["P","V"],site="second"} : (!F)->()
protocol.apply @deliver(%q) {roles=["P","V"],site="third"} : (!F)->()
)mlir")}) {
    cases.run("invalid challenge order or arithmetic identity refuses", [&] {
      auto module = parse((helpers + mainFunction(invalid)).str());
      ProtocolObservationAnalysis analysis(*module);
      uint64_t remaining = 1000000;
      facts::Work work(remaining);
      refuses(analysis.get(declaration(*module), "V", work),
              "protocol-observation-unsupported");
    });
  }
  cases.run(
      "repeat is a symbolic closed round for zero and many iterations", [&] {
        std::string body = R"mlir(
"protocol.repeat"(%n,%s) ({^loop(%i:ui64,%service:!S):
)mlir";
        body += R"mlir(
%q=protocol.apply @draw(%service) {roles=["P","V"],site="sample_call"} : (!S)->!F
protocol.apply @deliver(%q) {roles=["P","V"],site="delivery_call"} : (!F)->()
)mlir";
        body += R"mlir(
"protocol.yield"() : ()->()
}) {site="rounds",carried=0:i64,maximum=1048576:i64,roles=["P","V"],carried_roles=[]} : (ui64,!S)->()
)mlir";
        auto module =
            parse((helpers + mainFunction(body, "%n:ui64,%s:!S", "ui64,!S",
                                          "[[\"P\",\"V\"],[\"V\"]]"))
                      .str());
        ProtocolObservationAnalysis analysis(*module);
        uint64_t remaining = 1000000;
        facts::Work work(remaining);
        const auto *summary =
            take(analysis.get(declaration(*module), "V", work));
        closed(*summary, 1);
        require(summary->actions[0].callee &&
                    summary->actions[0].callee->actions.size() == 3 &&
                    summary->stops.test(0) && summary->results[0].test(0),
                "repeat unrolled or omitted count/stop dependency");
      });
  cases.run("repeat carry reaches a fixed point including the zero trip", [&] {
    auto module = parse(R"mlir(
"protocol.func"() ({^entry(%n:ui64,%a:!F,%b:!F):
%r:2="protocol.repeat"(%n,%a,%b) ({^loop(%i:ui64,%x:!F,%y:!F):
"protocol.yield"(%y,%x) : (!F,!F)->()
}) {site="swap",carried=2:i64,maximum=99:i64,roles=["V"],carried_roles=[["V"],["V"]]} : (ui64,!F,!F)->(!F,!F)
"protocol.return"(%r#0,%r#1) : (!F,!F)->()
}) {sym_name="main",function_type=(ui64,!F,!F)->(!F,!F),roles=["P","V"],input_roles=[["V"],["V"],["V"]],output_roles=[["V"],["V"]]} : ()->()
)mlir");
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    const auto *summary = take(analysis.get(declaration(*module), "V", work));
    for (const auto &deps : summary->results)
      require(deps.test(0) && deps.test(1) && deps.test(2),
              "carry dependencies were not closed");
    for (const auto &origin : summary->resultOrigins)
      require(origin.kind == Origin::Kind::Unknown,
              "swapped carry acquired exact identity");
  });
  cases.run("one-time incoming delivery is not a loop invariant", [&] {
    auto module = parse((helpers + mainFunction(R"mlir(
"protocol.repeat"(%n,%q) ({^loop(%i:ui64,%challenge:!F):
protocol.apply @deliver(%challenge) {roles=["P","V"],site="delivery"} : (!F)->()
"protocol.yield"() : ()->()
}) {site="rounds",carried=0:i64,maximum=10:i64,roles=["P","V"],carried_roles=[]} : (ui64,!F)->()
)mlir",
                                                "%n:ui64,%q:!F", "ui64,!F",
                                                "[[\"P\",\"V\"],[\"V\"]]"))
                            .str());
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    refuses(analysis.get(declaration(*module), "V", work),
            "protocol-observation-unsupported");
  });
  cases.run("ignored verifier guard affects return and stop observations", [&] {
    auto module = parse(
        mainFunction("protocol.guard %accept {owner=\"V\",site=\"guard\"}",
                     "%accept:i1", "i1", "[[\"V\"]]"));
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    const auto *summary = take(analysis.get(declaration(*module), "V", work));
    require(summary->mayStop && summary->stops.test(0) &&
                summary->results[0].test(0),
            "guard stop omitted from return transfer");
  });
  cases.run("zero-atom constant helper returns an available value", [&] {
    auto module = parse(R"mlir(
"protocol.func"() ({
%yes=arith.constant true
"protocol.return"(%yes) : (i1)->()
}) {sym_name="constant",function_type=()->i1,roles=["V"],input_roles=[],output_roles=[["V"]]} : ()->()
"protocol.func"() ({
%ok=protocol.apply @constant() {roles=["V"],site="constant"} : ()->i1
"protocol.return"(%ok) : (i1)->()
}) {sym_name="main",function_type=()->i1,roles=["V"],input_roles=[],output_roles=[["V"]]} : ()->()
)mlir");
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    const auto *summary = take(analysis.get(declaration(*module), "V", work));
    require(!summary->results[0].empty() && summary->results[0].none(),
            "constant became unavailable or acquired a dependency");
  });
  cases.run(
      "roles and exact formal swaps follow actual call associations", [&] {
        auto extra = R"mlir(
"protocol.func"() ({^entry(%first:!F,%second:!F):
"protocol.return"(%second) : (!F)->()
}) {sym_name="second",function_type=(!F,!F)->!F,roles=["Author","Observer"],input_roles=[["Observer"],["Observer"]],output_roles=[["Observer"]]} : ()->()
)mlir";
        auto module = parse(
            (helpers + extra +
             mainFunction(R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="sample"} : (!S)->!F
%x=protocol.apply @second(%unused,%q) {roles=["P","V"],site="select"} : (!F,!F)->!F
%restricted=protocol.restrict_roles %x {roles=["V"]} : !F
protocol.apply @deliver(%restricted) {roles=["P","V"],site="deliver"} : (!F)->()
)mlir",
                          "%s:!S,%unused:!F", "!S,!F", "[[\"V\"],[\"V\"]]"))
                .str());
        ProtocolObservationAnalysis analysis(*module);
        uint64_t remaining = 1000000;
        facts::Work work(remaining);
        auto *summary = take(analysis.get(declaration(*module), "V", work));
        closed(*summary, 1);
        require(summary->actions[1].callee->observer == "Observer" &&
                    !summary->actions[1].results[0].test(1),
                "role mapping or formal substitution was positional guesswork");
      });
  cases.run("role assembly preserves only the observer component", [&] {
    auto module = parse((helpers + mainFunction(R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="sample"} : (!S)->!F
%both="protocol.assemble_roles"(%private,%q) {roles=["P","V"]} : (!F,!F)->!F
%sent=protocol.exchange %both {sender="V",receiver="P",site="deliver"} : !F
)mlir",
                                                "%s:!S,%private:!F", "!S,!F",
                                                "[[\"V\"],[\"P\"]]"))
                            .str());
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    closed(*take(analysis.get(declaration(*module), "V", work)), 1);
  });
  cases.run("receive is a new observed atom, not the prover expression", [&] {
    auto module = parse(R"mlir(
"protocol.func"() ({^entry(%private:i1):
%received=protocol.exchange %private {sender="P",receiver="V",site="message"} : i1
"protocol.return"(%received) : (i1)->()
}) {sym_name="main",function_type=(i1)->i1,roles=["P","V"],input_roles=[["P"]],output_roles=[["V"]]} : ()->()
)mlir");
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    const auto *summary = take(analysis.get(declaration(*module), "V", work));
    require(summary->results[0].count() == 1 && summary->results[0].test(1),
            "receive followed the private expression");
  });
  cases.run("pending challenge cannot cross a verifier receive", [&] {
    auto module = parse((helpers + mainFunction(R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="sample"} : (!S)->!F
%received=protocol.exchange %private {sender="P",receiver="V",site="message"} : !F
protocol.apply @deliver(%q) {roles=["P","V"],site="deliver"} : (!F)->()
)mlir",
                                                "%s:!S,%private:!F", "!S,!F",
                                                "[[\"V\"],[\"P\"]]"))
                            .str());
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    refuses(analysis.get(declaration(*module), "V", work),
            "protocol-observation-unsupported");
  });
  cases.run("ignored verifier local call retains logical stop dependencies",
            [&] {
              auto module = parse((Twine(R"mlir(
"runtime.binding"() {sym_name="inverse",contract="field.inverse",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope,!F)->!exec.outcome<(!F)>} : ()->()
func.func @ignored(%scope:!runtime.scope,%x:!F)->!exec.outcome<> attributes {no_inline,runtime.origin=["ignored",[]]} {
%attempt="exec.apply"(%scope,%x) {binding=@inverse,parameters=[],site="inverse"} : (!runtime.scope,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%attempt)[^ok,^failed] : (!exec.outcome<(!F)>)->()
^ok(%unused:!F):
%done="exec.returned"() : ()->!exec.outcome<>
func.return %done : !exec.outcome<>
^failed(%reason:!exec.stop):
%failure="exec.failed"(%reason) : (!exec.stop)->!exec.outcome<>
func.return %failure : !exec.outcome<>
}
)mlir") + mainFunction(R"mlir(
"protocol.local_call"(%x) {callee=@ignored,role="V",site="ignored"} : (!F)->()
)mlir",
                       "%x:!F", "!F", "[[\"V\"]]"))
                                      .str());
              ProtocolObservationAnalysis analysis(*module);
              uint64_t remaining = 1000000;
              facts::Work work(remaining);
              const auto *summary =
                  take(analysis.get(declaration(*module), "V", work));
              require(summary->mayStop && summary->stops.test(0) &&
                          summary->results[0].test(0) &&
                          summary->actions[0].numerical &&
                          summary->actions[0].numerical->primitives.size() == 1,
                      "unused partial local computation lost its actual stop "
                      "or interpretation");
            });
  cases.run(
      "service aliases preserve the actual formal for independent selection",
      [&] {
        auto module = parse((helpers + mainFunction(R"mlir(
%q=protocol.apply @draw(%other) {roles=["P","V"],site="sample"} : (!S)->!F
protocol.apply @deliver(%q) {roles=["P","V"],site="deliver"} : (!F)->()
)mlir",
                                                    "%s:!S,%other:!S", "!S,!S",
                                                    "[[\"V\"],[\"V\"]]"))
                                .str());
        ProtocolObservationAnalysis analysis(*module);
        uint64_t remaining = 1000000;
        facts::Work work(remaining);
        auto *summary = take(analysis.get(declaration(*module), "V", work));
        require(summary->services.count() == 1 && summary->services.test(1),
                "different service roots were equated by contract type");
      });
  cases.run("all insufficient work allowances refuse without a partial summary",
            [&] {
              auto module = parse((helpers + mainFunction(roundBody)).str());
              uint64_t remaining = 1000000;
              facts::Work complete(remaining);
              ProtocolObservationAnalysis baseline(*module);
              take(baseline.get(declaration(*module), "V", complete));
              uint64_t needed = 1000000 - remaining;
              for (uint64_t allowance = 0; allowance < needed; ++allowance) {
                ProtocolObservationAnalysis analysis(*module);
                uint64_t budget = allowance;
                facts::Work bounded(budget);
                refuses(analysis.get(declaration(*module), "V", bounded),
                        "protocol-observation-capacity");
                require(bounded.exhausted(),
                        "capacity refusal did not exhaust caller work");
              }
            });
  cases.run(
      "scalar and product requests keep distinct methods and operands", [&] {
        auto module = parse(R"mlir(
"protocol.func"() ({^entry(%s:!protocol.service_ref<"random.koala-bear.ext4-binomial3/0">):
%n="data.index"() {value=8:ui64} : ()->ui64
%count="data.index"() {value=4:ui64} : ()->ui64
%i="protocol.query"(%s,%n) {owner="V",method="index",site="scalar"} : (!protocol.service_ref<"random.koala-bear.ext4-binomial3/0">,ui64)->ui64
%sent_i=protocol.exchange %i {sender="V",receiver="P",site="scalar_delivery"} : ui64
%block="protocol.query"(%s,%n,%count) {owner="V",method="indices",site="product"} : (!protocol.service_ref<"random.koala-bear.ext4-binomial3/0">,ui64,ui64)->!data.indices
%sent_block=protocol.exchange %block {sender="V",receiver="P",site="product_delivery"} : !data.indices
%yes=arith.constant true
"protocol.return"(%yes) : (i1)->()
}) {sym_name="main",function_type=(!protocol.service_ref<"random.koala-bear.ext4-binomial3/0">)->i1,roles=["P","V"],input_roles=[["V"]],output_roles=[["V"]]} : ()->()
)mlir");
        ProtocolObservationAnalysis analysis(*module);
        uint64_t remaining = 1000000;
        facts::Work work(remaining);
        auto *summary = take(analysis.get(declaration(*module), "V", work));
        closed(*summary, 2);
        auto scalar = cast<pir::QueryOp>(summary->actions[2].operation);
        auto product = cast<pir::QueryOp>(summary->actions[4].operation);
        require(scalar.getMethod() == "index" &&
                    product.getMethod() == "indices" &&
                    summary->actions[2].inputs.size() == 2 &&
                    summary->actions[4].inputs.size() == 3 &&
                    scalar.getInputs()[0] == product.getInputs()[0],
                "request laws or exact shape operands were conflated");
      });
  cases.run(
      "nested repeats retain one event family with its two coordinates", [&] {
        auto module = parse((helpers + mainFunction(R"mlir(
"protocol.repeat"(%n,%n,%s) ({^outer(%i:ui64,%inner_count:ui64,%service:!S):
"protocol.repeat"(%inner_count,%service) ({^inner(%j:ui64,%inner_service:!S):
%q=protocol.apply @draw(%inner_service) {roles=["P","V"],site="sample"} : (!S)->!F
protocol.apply @deliver(%q) {roles=["P","V"],site="deliver"} : (!F)->()
"protocol.yield"() : ()->()
}) {site="inner",carried=0:i64,maximum=1048576:i64,roles=["P","V"],carried_roles=[]} : (ui64,!S)->()
"protocol.yield"() : ()->()
}) {site="outer",carried=0:i64,maximum=1048576:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64,!S)->()
)mlir",
                                                    "%n:ui64,%s:!S", "ui64,!S",
                                                    "[[\"P\",\"V\"],[\"V\"]]"))
                                .str());
        ProtocolObservationAnalysis analysis(*module);
        uint64_t remaining = 1000000;
        facts::Work work(remaining);
        const auto *summary =
            take(analysis.get(declaration(*module), "V", work));
        closed(*summary, 1);
        const auto *outer = summary->actions[0].callee;
        const auto *inner = outer->actions[0].callee;
        require(outer->block != inner->block && outer->actions.size() == 2 &&
                    inner->actions.size() == 3 && summary->depth == 4 &&
                    summary->stops.test(0),
                "nested repetition lost coordinates, sharing or count stops");
      });
  cases.run("selected data transport cannot consume a pending challenge", [&] {
    auto module = parse((helpers + mainFunction(R"mlir(
%q=protocol.apply @draw(%s) {roles=["P","V"],site="sample"} : (!S)->!F
%sent=protocol.exchange %q {sender="V",receiver="P",site="data"} : !F
)mlir"))
                            .str());
    auto entry = declaration(*module);
    auto exchange = *entry.getBody().front().getOps<pir::ExchangeOp>().begin();
    ProtocolObservationAnalysis analysis(*module, {exchange});
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    refuses(analysis.get(entry, "V", work), "protocol-observation-unsupported");
  });
  cases.run("data selection is exact and clear removes it", [&] {
    auto text = mainFunction(R"mlir(
%sent=protocol.exchange %data {sender="V",receiver="P",site="data"} : !F
)mlir",
                             "%data:!F", "!F", "[[\"V\"]]");
    auto module = parse(text), foreign = parse(text);
    auto entry = declaration(*module);
    auto exchange = *entry.getBody().front().getOps<pir::ExchangeOp>().begin();
    auto other = *declaration(*foreign)
                      .getBody()
                      .front()
                      .getOps<pir::ExchangeOp>()
                      .begin();
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    ProtocolObservationAnalysis wrong(*module, {other});
    refuses(wrong.get(entry, "V", work), "protocol-observation-owner");
    ProtocolObservationAnalysis repeated(*module, {exchange, exchange});
    refuses(repeated.get(entry, "V", work), "protocol-observation-owner");
    ProtocolObservationAnalysis selected(*module, {exchange});
    auto *summary = take(selected.get(entry, "V", work));
    require(summary->actions[0].dataExchange && summary->queryFamilies == 0 &&
                summary->pending.input == Pending::Input::Empty,
            "selected data exchange became a challenge");
    selected.clear();
    summary = take(selected.get(entry, "V", work));
    require(!summary->actions[0].dataExchange &&
                summary->pending.input == Pending::Input::Formal,
            "clear retained data-exchange permission");
  });
  cases.run("wrong owner and exhausted work are sticky until clear", [&] {
    auto module = parse((helpers + mainFunction(roundBody)).str());
    auto foreign = parse((helpers + mainFunction(roundBody)).str());
    ProtocolObservationAnalysis analysis(*module);
    uint64_t remaining = 1000000;
    facts::Work work(remaining);
    refuses(analysis.get(declaration(*foreign), "V", work),
            "protocol-observation-owner");
    refuses(analysis.get(declaration(*module), "V", work),
            "protocol-observation-owner");
    analysis.clear();
    closed(*take(analysis.get(declaration(*module), "V", work)), 1);
    remaining = 0;
    refuses(analysis.get(declaration(*module), "V", work),
            "protocol-observation-capacity");
    analysis.clear();
    remaining = 1000000;
    facts::Work fresh(remaining);
    closed(*take(analysis.get(declaration(*module), "V", fresh)), 1);
  });
  return cases.result();
}
