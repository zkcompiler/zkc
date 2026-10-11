#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Language/Project.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
constexpr StringLiteral source = R"zkc(module m;
domain F=field("bls12-381.fr");
interface TestTranscript<T:Field>{
  type State:Copy+Drop;
  fn initialize()->State effects(stop, opaque);
  fn observe(t:State,value:T)->State effects(stop, opaque);
  fn draw(t:State)->(State,T) effects(stop, opaque);
}
module Provider:TestTranscript<F>{
  type State:Copy+Drop=index;
  fn initialize()->State{return State(0);}
  fn observe(t:State,value:F)->State{return t;}
  fn draw(t:State)->(State,F){return (t,1);}
}
protocol Leaf<T:Field+Share+Wire> roles(A,B)
  (public:T@(A,B),secret:T@A,random:Random<T>@B)->(ok:bool@B){
  #[site(msg)] let message=send A->B(secret);
  #[site(query)] let challenge=random.draw();
  #[site(delivery)] let actual=send B->A(challenge);
  return message==public+challenge;
}
protocol Outer<T:Field+Share+Wire> roles(P,V)
  (x:T@(P,V),w:T@P,random:Random<T>@V)->(ok:bool@V){
  #[site(step)] let ok=Leaf<T> roles(P,V)(x,w,random);
  return ok;
}
construction Child<T:Field+Share+Wire,H:TestTranscript<T>> for Leaf<T>{
  transcript H;
  replace random;
  on start(t,public){return H::observe(t,public);}
  on message {msg,delivery}(t,value){return H::observe(t,value);}
  on query query(t){return H::draw(t);}
}
construction Parent<T:Field+Share+Wire,H:TestTranscript<T>> for Outer<T>{
  transcript H;
  replace random;
  on start(t){return t;}
  apply Child<T,H> at step;
}
proof Demo=Outer<F>{prover P;verifier V;public{x};accept ok;
  construction Parent<F,Provider>;}
)zkc";
Expected<CheckedProject> checked(StringRef text) {
  auto captured = capture({{"m", text.str(), "applications.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
std::string changedSource(StringRef text, StringRef from, StringRef to) {
  auto result = text.str();
  auto position = result.find(from.str());
  require(position != std::string::npos, "fixture replacement exists");
  result.replace(position, from.size(), to.str());
  return result;
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("delegation remains a closed association in source and PIR", [&] {
    auto project = take(checked(source));
    auto closed = take(closeEntry(project, "m::Demo"));
    const auto &root =
        closed.declarations()
            [closed.entry().proof()->selectedConstruction->index];
    require(root.construction->applications.size() == 1,
            "child selection retained");
    const auto &application = root.construction->applications.front();
    const auto &child = closed.declarations()[application.construction.index];
    require(child.parameters.empty() && child.construction->rules.size() == 4,
            "child handlers are independently closed");
    require(root.construction->rules.size() == 1,
            "parent does not flatten child rules");
    auto original = take(emitOriginal(closed, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(original, &context);
    require(bool(parsed), "delegated PIR parses");
    take(compareOriginal(closed, *parsed));
    unsigned count = 0;
    parsed->walk([&](zkc::protocol_ir::ConstructionOp) { ++count; });
    require(count == 2,
            "PIR retains precisely the selected construction closure");
    mlir::SymbolTableCollection symbols;
    auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    auto record =
        symbols.lookupNearestSymbolFrom<zkc::protocol_ir::ConstructionOp>(
            unit, mlir::StringAttr::get(&context, root.symbol));
    auto resolved =
        take(zkc::protocol::resolveConstructionPlan(record, symbols));
    require(
        resolved.definitions.size() == 2 && resolved.invocations.size() == 1 &&
            resolved.invocations.front().inputs == SmallVector<unsigned>{0},
        "resolver retains one child start with its callee input coordinate");
    require(resolved.plan.rules.size() == 4,
            "execution plan contains root start and the three child event "
            "handlers");
  });
  cases.run("inherited delegation can be replaced as a whole", [&] {
    auto text = changedSource(source, "construction Parent<F,Provider>;",
                              "construction Changed<F,Provider>;");
    text += R"zkc(
      construction Other<T:Field+Share+Wire,H:TestTranscript<T>> for Leaf<T>{
        base Child<T,H>;
        on message msg(t,value){return t;}
      }
      construction Changed<T:Field+Share+Wire,H:TestTranscript<T>> for Outer<T>{
        base Parent<T,H>;
        apply Other<T,H> at step;
      })zkc";
    auto project = take(checked(text));
    auto closed = take(closeEntry(project, "m::Demo"));
    auto original = take(emitOriginal(closed, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(original, &context);
    require(bool(parsed), "replacement PIR parses");
    take(compareOriginal(closed, *parsed));
  });
  cases.run("child starts lower through checked participant construction", [&] {
    auto project = take(checked(source));
    auto closed = take(closeEntry(project, "m::Demo"));
    auto original = take(prepareOriginal(closed));
    for (bool simplify : {false, true}) {
      EntryOptions options;
      options.simplify = simplify;
      options.releaseStorage = simplify;
      auto compiled = take(compileEntry(original, options));
      require(
          std::holds_alternative<zkc::CompiledNativeProof>(compiled.artifact()),
          "delegation lowers to the common proof deployment");
    }
  });
  cases.run("nested delegation follows the actual expanded call path", [&] {
    auto text = source.str() + R"zkc(
      protocol Top<T:Field+Share+Wire> roles(P,V)
        (x:T@(P,V),w:T@P,random:Random<T>@V)->(ok:bool@V){
        #[site(outer)] let ok=Outer<T> roles(P,V)(x,w,random);
        return ok;
      }
      construction Grand<T:Field+Share+Wire,H:TestTranscript<T>> for Top<T>{
        transcript H; replace random;
        on start(t){return t;}
        apply Parent<T,H> at outer;
      }
      proof Nested=Top<F>{prover P;verifier V;public{x};accept ok;
        construction Grand<F,Provider>;}
    )zkc";
    auto project = take(checked(text));
    auto closed = take(closeEntry(project, "m::Nested"));
    auto original = take(emitOriginal(closed, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(original, &context);
    require(bool(parsed), "nested PIR parses");
    take(compareOriginal(closed, *parsed));
    auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    mlir::SymbolTableCollection symbols;
    const auto &root =
        closed.declarations()
            [closed.entry().proof()->selectedConstruction->index];
    auto record =
        symbols.lookupNearestSymbolFrom<zkc::protocol_ir::ConstructionOp>(
            unit, mlir::StringAttr::get(&context, root.symbol));
    auto resolved =
        take(zkc::protocol::resolveConstructionPlan(record, symbols));
    require(resolved.definitions.size() == 3 &&
                resolved.invocations.size() == 2,
            "nested starts and definition closure retained");
    SmallVector<zkc::mathematical::ApplicationStart> starts;
    for (const auto &invocation : resolved.invocations)
      starts.push_back(
          {closed.protocol().symbol, invocation.site, invocation.inputs});
    mlir::PassManager passes(&context);
    passes.addPass(
        zkc::protocol::createPrepareProtocolPass(false, false, starts));
    require(mlir::succeeded(passes.run(*parsed)),
            "independent source expansion agrees with resolved child paths");
    unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    mlir::SymbolTableCollection preparedSymbols;
    auto target =
        preparedSymbols
            .lookupNearestSymbolFrom<zkc::protocol_ir::MathematicalOp>(
                unit,
                mlir::StringAttr::get(&context, closed.protocol().symbol));
    std::set<std::string> events;
    target.walk([&](mlir::Operation *op) {
      if (mlir::isa<zkc::protocol_ir::QueryOp, zkc::protocol_ir::ExchangeOp>(
              op))
        events.insert(op->getAttrOfType<mlir::StringAttr>("site").str());
    });
    for (const auto &rule : resolved.plan.rules)
      for (const auto &site : rule.sites)
        require(events.erase(site),
                "resolved handler selects the actual nested operation");
    require(events.empty(), "nested execution plan covers every event");
  });
  cases.run("source parameter order does not change start input coordinates",
            [&] {
              auto text = changedSource(
                  source, "public:T@(A,B),secret:T@A,random:Random<T>@B",
                  "random:Random<T>@B,public:T@(A,B),secret:T@A");
              text = changedSource(text, "roles(P,V)(x,w,random)",
                                   "roles(P,V)(random,x,w)");
              auto project = take(checked(text));
              auto closed = take(closeEntry(project, "m::Demo"));
              auto original = take(emitOriginal(closed, context));
              auto parsed =
                  mlir::parseSourceString<mlir::ModuleOp>(original, &context);
              require(bool(parsed), "reordered source produces formed PIR");
              take(compareOriginal(closed, *parsed));
            });
  cases.run("unlabelled call cannot inherit a sibling's delegation", [&] {
    auto text = changedSource(
        source, "#[site(step)] let ok=Leaf<T> roles(P,V)(x,w,random);",
        "let ignored=Shadow<T> roles(P,V)(x,w,random); #[site(step)] "
        "let ok=Leaf<T> roles(P,V)(x,w,random);");
    text += R"zkc(
      protocol Shadow<T:Field+Share+Wire> roles(P,V)
        (x:T@(P,V),w:T@P,random:Random<T>@V)->(ok:bool@V){
        #[site(step)] let ok=Leaf<T> roles(P,V)(x,w,random);
        return ok;
      })zkc";
    refuses(checked(text), "source.construction");
  });
  cases.run("a child cannot hide an alias of the replaced authority", [&] {
    auto text = changedSource(
        source, "public:T@(A,B),secret:T@A,random:Random<T>@B",
        "public:T@(A,B),secret:T@A,random:Random<T>@B,alias:Random<T>@B");
    text = changedSource(text, "roles(P,V)(x,w,random)",
                         "roles(P,V)(x,w,random,random)");
    refuses(checked(text), "source.construction");
  });
  for (const auto &item :
       {std::pair{"missing call", "apply Child<T,H> at absent;"},
        {"wrong target", "apply Parent<T,H> at step;"},
        {"non construction", "apply Leaf<T> at step;"},
        {"duplicate", "apply Child<T,H> at step; apply Child<T,H> at step;"},
        {"overlapping parent rule",
         "apply Child<T,H> at step; on message step.msg(t,value){return t;}"}})
    cases.run(item.first, [&] {
      refuses(checked(changedSource(source, "apply Child<T,H> at step;",
                                    item.second)),
              "source.construction");
    });
  cases.run("explicit child format belongs to root only", [&] {
    refuses(checked(changedSource(source, "on start(t,public)",
                                  "format Native; on start(t,public)")),
            "source.construction");
  });
  cases.run("parent cannot override an inherited child's leaf", [&] {
    auto text = source.str() + R"zkc(
      construction Changed<T:Field+Share+Wire,H:TestTranscript<T>> for Outer<T>{
        base Parent<T,H>;
        on message step.msg(t,value){return t;}
      })zkc";
    refuses(checked(text), "source.construction");
  });
  for (StringRef mutation : {"omitted-child", "child-provider", "child-root",
                             "missing-rule", "wrong-call", "duplicate-call"})
    cases.run("PIR resolution refuses " + mutation, [&] {
      auto project = take(checked(source));
      auto closed = take(closeEntry(project, "m::Demo"));
      auto original = take(emitOriginal(closed, context));
      auto parsed = mlir::parseSourceString<mlir::ModuleOp>(original, &context);
      require(bool(parsed), "PIR fixture parses");
      auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
          parsed->getBody()->front());
      mlir::SymbolTableCollection symbols;
      const auto &definition =
          closed.declarations()
              [closed.entry().proof()->selectedConstruction->index];
      auto root =
          symbols.lookupNearestSymbolFrom<zkc::protocol_ir::ConstructionOp>(
              unit, mlir::StringAttr::get(&context, definition.symbol));
      auto selected =
          mlir::cast<mlir::DictionaryAttr>(root.getApplications()[0]);
      auto child =
          symbols.lookupNearestSymbolFrom<zkc::protocol_ir::ConstructionOp>(
              root, selected.getAs<mlir::FlatSymbolRefAttr>("construction"));
      mlir::OpBuilder builder(&context);
      if (mutation == "omitted-child")
        root.setApplicationsAttr(builder.getArrayAttr({}));
      else if (mutation == "child-provider")
        child.setProvider("another-provider");
      else if (mutation == "child-root")
        child.setRootOnly(true);
      else if (mutation == "missing-rule")
        child.setRulesAttr(
            builder.getArrayAttr(child.getRules().getValue().drop_back()));
      else if (mutation == "duplicate-call")
        root.setApplicationsAttr(builder.getArrayAttr({selected, selected}));
      else {
        mlir::NamedAttrList changed(selected);
        changed.set("site", builder.getStringAttr("absent"));
        root.setApplicationsAttr(
            builder.getArrayAttr({changed.getDictionary(&context)}));
      }
      refuses(zkc::protocol::resolveConstructionPlan(root, symbols),
              "protocol-construction");
    });
  return cases.result();
}
