#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Language/Project.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {

std::string mutate(StringRef text, StringRef from, StringRef to) {
  auto result = text.str();
  auto at = result.find(from.str());
  require(at != std::string::npos, "mutation missing");
  result.replace(at, from.size(), to.str());
  return result;
}
struct Fixture {
  OwningOpRef<ModuleOp> original;
  NativeProofPolicy policy;
  NativeProofConstruction constructed;
};
Expected<Fixture> fixture(StringRef text, MLIRContext &context,
                          ArrayRef<unsigned> publicInputs = {0},
                          unsigned service = 2) {
  auto captured = language::capture({{"m", text.str(), "binding.zkc"}});
  if (!captured)
    return captured.takeError();
  auto checked = language::analyze(*captured).checkedProject();
  if (!checked)
    return checked.takeError();
  auto closed = language::closeEntry(*checked, "m::Demo");
  if (!closed)
    return closed.takeError();
  auto emitted = language::emitOriginal(*closed, context);
  if (!emitted)
    return emitted.takeError();
  auto original = parseSourceString<ModuleOp>(*emitted, &context);
  if (!original)
    return zkc::error("test-original");
  auto unit = cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  NativeProofPolicy policy;
  for (auto entry :
       unit.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
    policy.entry = entry.getSymName().str();
    policy.producer = cast<StringAttr>(entry.getRoles()[0]).str();
    policy.validator = cast<StringAttr>(entry.getRoles()[1]).str();
  }
  policy.publicInputs.assign(publicInputs.begin(), publicInputs.end());
  policy.services = {service};
  for (auto record :
       unit.getBody().front().getOps<protocol_ir::ConstructionOp>())
    policy.construction = record.getSymName().str();
  if (policy.construction.empty())
    policy.suite = "merlin3.bls12-381.fr64be/0";
  auto selected = selectNativeProofDraws(*original, policy);
  if (!selected)
    return selected.takeError();
  auto constructed = constructNativeProof(*original, *selected);
  if (!constructed)
    return constructed.takeError();
  return Fixture{std::move(original), std::move(*selected),
                 std::move(*constructed)};
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::ifstream input(ZKC_FIXTURES "/language/construction-binding.zkc");
  std::string program((std::istreambuf_iterator<char>(input)), {});
  require(!program.empty(), "binding fixture missing");
  Cases cases;
  auto analyze = [&](StringRef text, NativeProofBindingProfile profile) {
    auto f = fixture(text, context);
    if (!f)
      return Expected<json::Value>(f.takeError());
    return analyzeNativeProofBinding(*f->original, *f->constructed.module,
                                     f->policy, profile);
  };
  cases.run("actual canonical hash history", [&] {
    auto report =
        take(analyze(program, NativeProofBindingProfile::CanonicalHashHistory));
    auto &coverage = *report.getAsObject()->getObject("coverage");
    require(coverage.getString("hash") == "hash.sha256",
            "hash primitive missing");
    require(coverage.getArray("transitions")->size() == 5,
            "root/start/commit/query/terminal coverage");
    require(coverage.getArray("terminal_outside_query")->size() == 1,
            "terminal absorption is not a subsequent query");
  });
  auto explicitSource = mutate(program, "construction Derived<History>;",
                               "construction Derived<Explicit>;");
  cases.run("actual stateless explicit-input request", [&] {
    auto report =
        take(analyze(explicitSource, NativeProofBindingProfile::ExplicitInput));
    auto &coverage = *report.getAsObject()->getObject("coverage");
    require(coverage.getArray("transitions")->size() == 1,
            "explicit request count");
    require(coverage.getArray("terminal_outside_query")->size() == 1,
            "terminal distinction missing");
  });
  cases.run("explicit input is not a history claim", [&] {
    refuses(analyze(explicitSource,
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-coverage");
  });
  for (auto replacement :
       {std::pair<StringRef, StringRef>{"tag(2),concat(unpack(t),encode(v))",
                                        "tag(2),unpack(t)"},
        {"tag(3),concat(unpack(t),encode(v))", "tag(3),unpack(t)"},
        {"tag(3),concat(unpack(t),encode(v))",
         "tag(3),concat(encode(v),unpack(t))"},
        {"return (State(next),sample(next));", "return (t,sample(next));"},
        {"tag(4),unpack(t)", "tag(3),unpack(t)"}})
    cases.run(
        "history refuses omitted/reset/reordered data: " + replacement.first,
        [&] {
          refuses(
              analyze(mutate(program, replacement.first, replacement.second),
                      NativeProofBindingProfile::CanonicalHashHistory),
              "construction-binding-coverage");
        });
  cases.run("arithmetic dependence is not canonical coverage", [&] {
    refuses(analyze(mutate(program, "tag(2),concat(unpack(t),encode(v))",
                           "tag(2),concat(unpack(t),encode(v-v))"),
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-encoding");
  });
  cases.run("stateless query cannot omit its public input", [&] {
    refuses(analyze(mutate(explicitSource, "return State(encode(v));",
                           "return State(empty());"),
                    NativeProofBindingProfile::ExplicitInput),
            "construction-binding-coverage");
  });
  cases.run("native installed history", [&] {
    auto native = mutate(
        program, "construction Derived<History>;",
        "construction fiat_shamir(\"merlin3.bls12-381.fr64be/0\",challenges);");
    auto report =
        take(analyze(native, NativeProofBindingProfile::NativeHistory));
    require(report.getAsObject()->getString("profile") == "native-history",
            "native profile");
    auto &coverage = *report.getAsObject()->getObject("coverage");
    require(coverage.getArray("terminal_outside_query")->size() == 1,
            "native terminal absorption is not a subsequent query");
  });
  cases.run("local handlers do not inherit installed history", [&] {
    refuses(analyze(program, NativeProofBindingProfile::NativeHistory),
            "construction-binding-profile");
  });
  cases.run("complete report recomputation refuses changed evidence", [&] {
    auto f = take(fixture(program, context));
    auto report = take(analyzeNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory));
    auto parsed = take(parseNaturalJson(printJson(report), 8 * 1024 * 1024, 64,
                                        "test-json", "test-capacity"));
    require(equalNaturalJson(report, parsed),
            "report JSON round trip changes meaning");
    auto repeated = take(analyzeNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory));
    require(equalNaturalJson(report, repeated),
            "binding recomputation is nondeterministic");
    auto checked = checkNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory, printJson(report));
    if (checked)
      throw std::runtime_error(toString(std::move(checked)));
    (*report.getAsObject())["candidate_sha256"] = "changed";
    auto error = checkNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory, printJson(report));
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "construction-binding-report"),
            "changed report identity accepted");
  });
  auto byteProgram = mutate(program, "public:F@(P,V)", "public:Bytes@(P,V)");
  for (unsigned i = 0; i < 3; ++i)
    byteProgram = mutate(byteProgram, "fn start(t:State,v:F)",
                         "fn start(t:State,v:Bytes)");
  byteProgram = mutate(byteProgram, "tag(2),concat(unpack(t),encode(v))",
                       "tag(2),concat(unpack(t),frame(v))");
  byteProgram = mutate(byteProgram, "return State(encode(v));",
                       "return State(frame(v));");
  byteProgram = mutate(byteProgram, "interface Chain", R"(
fn length(x:Bytes)->index=primitive("bytes.length");
fn length_code(x:index)->Bytes=primitive("encoding.index_uleb128");
fn frame(x:Bytes)->Bytes{return concat(length_code(length(x)),x);}
interface Chain)");
  cases.run("canonical actual-length framing", [&] {
    take(analyze(byteProgram, NativeProofBindingProfile::CanonicalHashHistory));
  });
  cases.run("unframed variable bytes refuse", [&] {
    refuses(
        analyze(mutate(byteProgram, "return concat(length_code(length(x)),x);",
                       "return x;"),
                NativeProofBindingProfile::CanonicalHashHistory),
        "construction-binding-encoding");
  });
  cases.run("constant length does not frame a variable input", [&] {
    refuses(analyze(mutate(byteProgram, "length_code(length(x))",
                           "length_code(32)"),
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-encoding");
  });
  std::ifstream schnorrInput(ZKC_FIXTURES
                             "/language/construction-binding-schnorr.zkc");
  std::string schnorr((std::istreambuf_iterator<char>(schnorrInput)), {});
  require(!schnorr.empty(), "Schnorr binding fixture missing");
  for (bool history : {true, false})
    cases.run(
        history ? "Schnorr canonical history" : "Schnorr explicit inputs", [&] {
          auto text = history ? schnorr
                              : mutate(schnorr, "Derived<History>",
                                       "Derived<Explicit>");
          auto f = take(fixture(text, context, {0, 1}, 4));
          auto profile = history
                             ? NativeProofBindingProfile::CanonicalHashHistory
                             : NativeProofBindingProfile::ExplicitInput;
          auto report = take(analyzeNativeProofBinding(
              *f.original, *f.constructed.module, f.policy, profile));
          if (auto error =
                  checkNativeProofBinding(*f.original, *f.constructed.module,
                                          f.policy, profile, printJson(report)))
            throw std::runtime_error(toString(std::move(error)));
        });
  cases.run("changed actual terminal acceptance is not binding evidence", [&] {
    auto f = take(fixture(program, context));
    bool changed = false;
    f.constructed.module->walk([&](algebra::FieldEqualOp op) {
      op->setOperand(1, op->getOperand(0));
      changed = true;
    });
    require(changed, "actual acceptance predicate missing");
    refuses(analyzeNativeProofBinding(
                *f.original, *f.constructed.module, f.policy,
                NativeProofBindingProfile::CanonicalHashHistory),
            "native-proof-correspondence");
  });
  cases.run("history cannot drop terminal observation", [&] {
    auto text =
        mutate(program,
               "on message {commitment,response}(t,value){return "
               "H::observe(t,value);}",
               "on message commitment(t,value){return H::observe(t,value);}"
               "on message response(t,value){return t;}");
    refuses(analyze(text, NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-coverage");
  });
  cases.run("mixed-direction message grouping refuses before binding", [&] {
    auto f = take(fixture(program, context));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(f.original->getBody()->front());
    auto record =
        *unit.getBody().front().getOps<protocol_ir::ConstructionOp>().begin();
    Builder builder(&context);
    StringRef delivery = f.policy.draws.front().second;
    std::string response = "label_" + llvm::toHex("response", true) + "_0";
    unsigned changed = 0;
    SmallVector<Attribute> rules;
    for (auto attr : record.getRules()) {
      auto rule = cast<DictionaryAttr>(attr);
      auto sites = rule.getAs<ArrayAttr>("sites");
      if (sites.size() == 1 &&
          cast<StringAttr>(sites[0]).getValue() == response) {
        ++changed;
        continue;
      }
      if (sites.size() == 1 &&
          cast<StringAttr>(sites[0]).getValue() == delivery) {
        ++changed;
        auto handler = SymbolTable(unit).lookup<func::FuncOp>(
            rule.getAs<FlatSymbolRefAttr>("handler").getValue());
        auto type = handler.getFunctionType();
        SmallVector<Type> inputs(type.getInputs());
        inputs.push_back(inputs.back());
        handler.setType(builder.getFunctionType(inputs, type.getResults()));
        handler.getBody().front().addArgument(inputs.back(), handler.getLoc());
        NamedAttrList grouped(rule);
        grouped.set("sites", builder.getStrArrayAttr({delivery, response}));
        auto payload = rule.getAs<ArrayAttr>("payload");
        grouped.set("payload", builder.getArrayAttr({payload[0], payload[0]}));
        rule = grouped.getDictionary(&context);
      }
      rules.push_back(rule);
    }
    require(changed == 2,
            "grouping must replace both actual message selectors");
    record.setRulesAttr(builder.getArrayAttr(rules));
    refuses(constructNativeProof(*f.original, f.policy),
            "native-proof-construction-message-group");
  });
  auto tupleSource =
      mutate(program, "send P->V(secret);", "send P->V((secret,secret));");
  tupleSource = mutate(tupleSource, "return last==first+c;",
                       "let (left,right)=first; return last==left+c;");
  tupleSource = mutate(
      tupleSource,
      "on message {commitment,response}(t,value){return H::observe(t,value);}",
      "on message commitment(t,value){let (a,b)=value; return "
      "H::observe(H::observe(t,a),b);}"
      "on message response(t,value){return H::observe(t,value);}");
  cases.run("whole grouped payload is covered by actual nested hashes", [&] {
    take(analyze(tupleSource, NativeProofBindingProfile::CanonicalHashHistory));
  });
  cases.run("a grouped handler cannot omit its second payload", [&] {
    refuses(analyze(mutate(tupleSource, "H::observe(H::observe(t,a),b)",
                           "H::observe(t,a)"),
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-coverage");
  });
  return cases.result();
}
