#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguageInspection.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Dialect/Printing.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SHA256.h"
#include <set>
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
ClosedEntry close(StringRef text, std::vector<AssetBuffer> assets = {}) {
  return take(closeEntry(take(analyze(take(capture({{"sample", text.str(), {}}},
                                                   std::move(assets), {})))
                                  .checkedProject()),
                         "sample::Demo"));
}
constexpr StringLiteral source = R"(module sample;
math fn same(x:bool,y:bool)->bool{return x==y;}
relation Equal(statement x:bool,witness y:bool){return same(x,y);}
protocol Run roles(P,V)(x:bool@P,y:bool@V)->(ok:bool@V)
 spec {target proof=Equal(in.x,in.y) accept out.ok;}
 {let ok@V=true;return(ok=ok);}entry Demo=Run;)";
zkc::relation::DeclareOp relation(mlir::ModuleOp module) {
  zkc::relation::DeclareOp result;
  module.walk([&](zkc::relation::DeclareOp op) { result = op; });
  require(bool(result), "missing native relation");
  return result;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto entry = close(source);
  auto bytes = take(emitOriginal(entry, context));
  auto parse = [&](StringRef bytes) {
    auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(module), "invalid relation original");
    return module;
  };
  auto module = parse(bytes);
  cases.run("noncallable declaration and total formula compare independently",
            [&] {
              auto report = take(compareOriginal(entry, *module));
              require(report.declarations == 4,
                      "relation/helper definition inventory differs");
              auto declaration = relation(*module);
              require(declaration.getKind() == "zkc.language.formula" &&
                          declaration.getRevision().size() == 64,
                      "formula representation identity missing");
              std::string formula;
              for (const auto &decl : entry.declarations())
                if (decl.relation && decl.origin)
                  formula = formulaSymbol(decl);
              require(succeeded(zkc::mathematical::verifyHelperObservations(
                          *module, {formula})),
                      "valid predicate observation rejected");
            });
  cases.run("unrelated captured helpers do not change predicate identity", [&] {
    auto other =
        close((source + " math fn unrelated(x:bool)->bool{return x;}").str());
    auto changed = parse(take(emitOriginal(other, context)));
    require(relation(*changed).getRevision() == relation(*module).getRevision(),
            "predicate identity included unrelated source capture");
  });
  cases.run("transitive helper body changes predicate identity", [&] {
    auto text = source.str();
    text.replace(text.find("return x==y;"), 12, "return x;");
    auto changed = parse(take(emitOriginal(close(text), context)));
    require(relation(*changed).getRevision() != relation(*module).getRevision(),
            "predicate identity omitted a helper definition");
  });
  for (StringRef attribute : {"key", "revision"})
    cases.run("relation identity mutation refuses", [&] {
      auto candidate = parse(bytes);
      relation(*candidate)
          ->setAttr(attribute, mlir::StringAttr::get(&context, "altered"));
      require(succeeded(mlir::verify(*candidate)),
              "mutation is not admitted IR");
      refuses(compareOriginal(entry, *candidate), "source.correspondence");
    });
  cases.run("native purpose mutation refuses", [&] {
    auto candidate = parse(bytes);
    relation(*candidate)
        ->setAttr(
            "purposes",
            mlir::ArrayAttr::get(
                &context, {mlir::StringAttr::get(&context, "witness"),
                           mlir::StringAttr::get(&context, "statement")}));
    require(succeeded(mlir::verify(*candidate)), "purpose mutation invalid");
    refuses(compareOriginal(entry, *candidate), "source.correspondence");
  });
  cases.run("omitting declaration and predicate together refuses", [&] {
    auto candidate = parse(bytes);
    relation(*candidate).erase();
    for (const auto &decl : entry.declarations())
      if (decl.relation && decl.origin) {
        auto wanted = formulaSymbol(decl);
        mlir::Operation *found = nullptr;
        candidate->walk([&](mlir::Operation *op) {
          if (auto name = op->getAttrOfType<mlir::StringAttr>("sym_name");
              name && name.getValue() == wanted)
            found = op;
        });
        require(found, "predicate missing");
        found->erase();
      }
    require(succeeded(mlir::verify(*candidate)), "omission invalid native IR");
    refuses(compareOriginal(entry, *candidate), "source.correspondence");
  });
  cases.run(
      "source clauses round trip through independent native bindings", [&] {
        auto original = take(prepareOriginal(entry));
        auto decoded =
            take(readInterface(original.bytes(), original.interfaceJson()));
        const auto &protocol = decoded.selectedProtocol();
        require(protocol.clauses.size() == 1 && decoded.relations.size() == 1 &&
                    protocol.clauses[0].subject.operands[0].native ==
                        std::vector<unsigned>{0} &&
                    protocol.clauses[0].subject.operands[1].role == 1 &&
                    protocol.clauses[0].decision->role == 1,
                "formula bindings were omitted or moved between participants");
        if (auto error = compareInterface(entry, decoded))
          throw std::runtime_error(toString(std::move(error)));
        take(compileEntry(original));
      });
  cases.run(
      "source completeness refuses an omitted clause or changed valid binding",
      [&] {
        auto original = take(prepareOriginal(entry));
        for (bool remove : {false, true}) {
          auto encoded = take(json::parse(original.interfaceJson()));
          auto &clauses = *encoded.getAsObject()
                               ->getArray("protocols")
                               ->front()
                               .getAsObject()
                               ->getArray("clauses");
          if (remove)
            clauses.clear();
          else {
            auto &operands =
                *clauses.front().getAsObject()->getObject("subject")->getArray(
                    "operands");
            std::swap(operands[0], operands[1]);
          }
          auto decoded =
              take(readInterface(original.bytes(), zkc::printJson(encoded)));
          auto error = compareInterface(entry, decoded);
          require(bool(error), "changed source clause was accepted");
          require(StringRef(toString(std::move(error)))
                      .contains("source.correspondence"),
                  "unexpected source comparison refusal");
        }
      });
  cases.run(
      "predicate definitions cannot be referenced by executable helpers", [&] {
        auto original = take(prepareOriginal(entry));
        auto candidate = parse(original.bytes());
        auto encoded = take(json::parse(original.interfaceJson()));
        auto symbol = *encoded.getAsObject()
                           ->getArray("relations")
                           ->front()
                           .getAsObject()
                           ->getObject("definition")
                           ->getString("function");
        mlir::func::FuncOp predicate;
        candidate->walk([&](mlir::func::FuncOp op) {
          if (op.getSymName() == symbol)
            predicate = op;
        });
        require(bool(predicate), "predicate helper missing");
        auto observer = mlir::cast<mlir::func::FuncOp>(predicate->clone());
        observer.setSymName("observer");
        observer.walk([&](mlir::func::CallOp op) { op.setCallee(symbol); });
        predicate->getBlock()->push_back(observer);
        require(succeeded(mlir::verify(*candidate)),
                "executable reference invalid");
        std::string bytes;
        raw_string_ostream stream(bytes);
        candidate->print(stream, mlir::OpPrintingFlags().printGenericOpForm());
        (*encoded.getAsObject())["original"] =
            toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
        refuses(readInterface(bytes, zkc::printJson(encoded)),
                "target.admission");
      });
  cases.run(
      "reused generic component clauses bind actual values and roles", [&] {
        auto original = take(prepareOriginal(close(R"(module sample;
      domain Fr=field("bls12-381.fr");domain K=field("bn254.fr");
      relation Equal<F:Field>(statement x:F,witness y:F){return x==y;}
      protocol Step<F:Field> roles(A,B)(x:F@A,y:F@B)->(a:F@A,b:F@B,ok:bool@B)
      spec{continuation reduce=Equal<F>(in.x,in.y)
         residual Equal<F>(out.a,out.b) accept out.ok;}
      {let ok@B=true;return(a=x,b=y,ok=ok);}
      protocol Run roles(P,V)(x:Fr@P,y:Fr@V,z:K@P,w:K@V,n:index@(P,V))
      ->(a:Fr@P,b:Fr@V) {
        let (a,b,ok)=apply Step<Fr> roles(P,V)(x,y);
        let (c,d,ok2)=apply Step<Fr> roles(V,P)(y,x);
        let (e,f,ok3)=apply Step<K> roles(P,V)(z,w);
        let (u,v)=repeat roles(P,V)(i<n,max 2) carry(u=x,v=y) capture(n) {
          let (r,s)=repeat roles(P,V)(j<n,max 2) carry(r=u,s=v) capture() {
            let (a,b,ok)=apply Step<Fr> roles(P,V)(r,s);
            yield(r=a,s=b);
          };
          yield(u=r,v=s);
        };
        return(a=u,b=v);
      }entry Demo=Run;)")));
        unsigned calls = 0, nested = 0;
        std::set<std::string> callees;
        std::set<std::vector<unsigned>> paths;
        auto error = inspectApplications(
            original, [&](const ApplicationOccurrence &occurrence) -> Error {
              ++calls;
              callees.insert(occurrence.callee.symbol);
              require(paths
                          .insert(std::vector<unsigned>(occurrence.path.begin(),
                                                        occurrence.path.end()))
                          .second,
                      "distinct applications share a path");
              require(occurrence.clauses.size() == 1,
                      "component contract missing");
              const auto &clause = occurrence.clauses[0];
              require(clause.subject[0].values[0] ==
                              occurrence.operation->getOperand(0) &&
                          clause.subject[1].values[0] ==
                              occurrence.operation->getOperand(1) &&
                          (*clause.residual)[0].values[0] ==
                              occurrence.operation->getResult(0) &&
                          (*clause.residual)[1].values[0] ==
                              occurrence.operation->getResult(1) &&
                          clause.decision->values[0] ==
                              occurrence.operation->getResult(2),
                      "component selector did not bind actual SSA");
              require(clause.subject[0].role == occurrence.roles[0] &&
                          clause.subject[1].role == occurrence.roles[1] &&
                          clause.decision->role == occurrence.roles[1],
                      "role substitution differs");
              if (calls == 2)
                require(occurrence.roles == ArrayRef<unsigned>({1, 0}),
                        "swapped participants lost");
              if (occurrence.path.size() == 3) {
                ++nested;
                require(
                    mlir::isa<mlir::BlockArgument>(clause.subject[0].values[0]),
                    "repeat operand was rebound to outer entry input");
              }
              return Error::success();
            });
        if (error)
          throw std::runtime_error(toString(std::move(error)));
        require(calls == 4 && nested == 1 && callees.size() == 2,
                "application or generic-instance inventory differs");
        unsigned untrustedCalls = 0;
        if (auto error = inspectApplications(
                original.bytes(), original.interfaceJson(),
                [&](const ApplicationOccurrence &) -> Error {
                  ++untrustedCalls;
                  return Error::success();
                }))
          throw std::runtime_error(toString(std::move(error)));
        require(untrustedCalls == calls, "trusted and byte inspection differ");
        Limits tight;
        tight.interfaceBytes = original.interfaceJson().size() - 1;
        unsigned tightCalls = 0;
        auto tooSmall = inspectApplications(
            original,
            [&](const ApplicationOccurrence &) -> Error {
              ++tightCalls;
              return Error::success();
            },
            tight);
        require(bool(tooSmall) && tightCalls == 0,
                "retained inspection bypasses tighter admission limits");
        consumeError(std::move(tooSmall));
        auto visitorError = inspectApplications(
            original, [&](const ApplicationOccurrence &) -> Error {
              return createStringError(inconvertibleErrorCode(),
                                       "retained visitor stop");
            });
        require(bool(visitorError) && toString(std::move(visitorError)) ==
                                          "retained visitor stop",
                "retained inspection swallowed the visitor error");

        take(compileEntry(original));
        for (unsigned mutation = 0; mutation < 4; ++mutation) {
          auto candidate = parse(original.bytes());
          zkc::protocol_ir::ApplyOp call;
          candidate->walk([&](zkc::protocol_ir::ApplyOp op) {
            if (!call)
              call = op;
          });
          require(bool(call), "no application to mutate");
          auto role = call.getRoles()[0];
          if (mutation == 0)
            call.setRolesAttr(mlir::ArrayAttr::get(&context, {role}));
          else if (mutation == 1)
            call.setRolesAttr(mlir::ArrayAttr::get(&context, {role, role}));
          else if (mutation == 2)
            call->eraseOperand(0);
          else {
            auto nested = mlir::ModuleOp::create(call.getLoc());
            call->getBlock()->getOperations().insert(call->getIterator(),
                                                     nested);
          }
          std::string bytes;
          raw_string_ostream stream(bytes);
          candidate->print(stream, zkc::canonicalPrintingFlags());
          unsigned visited = 0;
          auto rejected =
              inspectApplications(bytes, original.interfaceJson(),
                                  [&](const ApplicationOccurrence &) -> Error {
                                    ++visited;
                                    return Error::success();
                                  });
          require(bool(rejected) && visited == 0,
                  "malformed application reached inspection callback");
          require(StringRef(toString(std::move(rejected)))
                      .contains("target.admission"),
                  "malformed application did not fail native admission");
        }
        unsigned callbacks = 0;
        auto stopped =
            inspectApplications(original.bytes(), original.interfaceJson(),
                                [&](const ApplicationOccurrence &) -> Error {
                                  ++callbacks;
                                  return createStringError(
                                      inconvertibleErrorCode(), "visitor stop");
                                });
        require(bool(stopped) && callbacks == 1,
                "visitor refusal did not stop inspection");
        consumeError(std::move(stopped));
        callbacks = 0;
        auto encoded = take(json::parse(original.interfaceJson()));
        encoded.getAsObject()->getArray("protocols")->clear();
        auto malformed =
            inspectApplications(original.bytes(), zkc::printJson(encoded),
                                [&](const ApplicationOccurrence &) -> Error {
                                  ++callbacks;
                                  return Error::success();
                                });
        require(bool(malformed) && callbacks == 0,
                "inspection ran before complete admission");
        consumeError(std::move(malformed));
      });
  cases.run("malformed specification metadata refuses structurally", [&] {
    auto original = take(prepareOriginal(entry));
    auto mutate = [&](function_ref<void(json::Object &, json::Object &)>
                          change) {
      auto encoded = take(json::parse(original.interfaceJson()));
      auto &clause = *encoded.getAsObject()
                          ->getArray("protocols")
                          ->front()
                          .getAsObject()
                          ->getArray("clauses")
                          ->front()
                          .getAsObject();
      auto &relation =
          *encoded.getAsObject()->getArray("relations")->front().getAsObject();
      change(clause, relation);
      refuses(readInterface(original.bytes(), zkc::printJson(encoded)),
              "source.interface");
    };
    mutate([](auto &c, auto &) { c["decision"] = nullptr; });
    mutate([](auto &c, auto &) { c["kind"] = "continuation"; });
    mutate([](auto &c, auto &) { c["extra"] = true; });
    mutate([](auto &c, auto &) { (*c.getObject("decision"))["role"] = "P"; });
    mutate([](auto &c, auto &) {
      (*c.getObject("decision"))["direction"] = "input";
    });
    mutate([](auto &c, auto &) {
      (*c.getObject("decision"))["path"] = json::Array{0};
    });
    mutate([](auto &c, auto &) {
      (*c.getObject("subject"))["relation"] = "unknown";
    });
    mutate([](auto &c, auto &) {
      (*c.getObject("subject"))["operands"] = json::Array{};
    });
    mutate([](auto &, auto &r) {
      (*r.getObject("definition"))["kind"] = "opaque";
      r.getObject("definition")->erase("function");
    });
    mutate([](auto &, auto &r) {
      (*r.getObject("definition"))["function"] = "unknown";
    });
    mutate([](auto &, auto &r) {
      (*r.getArray("inputs"))[0].getAsObject()->operator[]("purpose") =
          "witness";
    });
  });
  cases.run(
      "inline formulas and every clause kind retain authored inventories", [&] {
        auto original = take(prepareOriginal(close(R"(module sample;
      relation R(statement x:bool,witness y:bool){return x==y;}
      protocol Run roles(P)(x:bool@P)->(y:bool@P,ok:bool@P)
      spec{
        input before=R(in.x,in.x);
        output after=R(in.x,out.y);
        continuation reduction=R(in.x,in.x) residual R(in.x,out.y) accept out.ok;
        target target=relation(statement expected=in.x,witness actual=out.y){return expected==actual;} accept out.ok;
      }{return(y=x,ok=true);}entry Demo=Run;)")));
        require(original.interface().selectedProtocol().clauses.size() == 4 &&
                    original.interface().relations.size() == 2,
                "authored clause inventory was not retained");
        take(compileEntry(original));
      });
  cases.run(
      "captured relations require their exact explicitly supplied assets", [&] {
        for (bool air : {false, true}) {
          using namespace zkc::relation;
          auto r1cs = take(R1CS::create(
              "bls12-381.fr", 3, 0, 1,
              {Constraint{LinearForm{{2, "1"}}, LinearForm{{2, "1"}},
                          LinearForm{{1, "1"}}}}));
          using N = AIRNode;
          auto trace = take(AIR::create(
              "bls12-381.fr", 2, 1,
              {{{AIRScopeKind::Every, 0}, {N::read(0, 1)}, {}, {}},
               {{AIRScopeKind::First, 0},
                {N::read(0, 0), N::publicInput(0), N::neg(1), N::add(0, 2)},
                {},
                {}},
               {{AIRScopeKind::Transition, 1},
                {N::read(1, 0), N::read(0, 0), N::mul(1, 1), N::neg(2),
                 N::add(0, 3)},
                {},
                {}},
               {{AIRScopeKind::Last, 0},
                {N::read(0, 0), N::constant("16"), N::neg(1), N::add(0, 2)},
                {},
                {}}}));
          AssetBuffer asset{
              "definition",
              air ? "air-json" : "r1cs-json",
              zkc::printJson(air ? trace.encode() : r1cs.encode()),
              {}};
          std::string witness =
              air ? "builtin(\"matrix\",F)" : "builtin(\"field_array\",F,3)";
          std::string text =
              "module sample;domain F=field(\"bls12-381.fr\");"
              "relation Captured(statement "
              "s:builtin(\"field_array\",F,1),witness w:" +
              witness + ")=" + (air ? "air" : "r1cs") +
              "(asset definition);"
              "protocol Run roles(P,V)(s:builtin(\"field_array\",F,1)@V,w:" +
              witness +
              "@P)->(ok:bool@V)"
              "spec{target proof=Captured(in.s,in.w) accept out.ok;}{let "
              "ok@V=true;return(ok=ok);}entry Demo=Run;";
          auto original = take(prepareOriginal(close(text, {asset})));
          refuses(readInterface(original.bytes(), original.interfaceJson()),
                  "source.interface");
          auto decoded =
              take(readInterface(original.bytes(), original.interfaceJson(), {},
                                 original.entry().project().assets()));
          require(decoded.relations[0].asset &&
                      decoded.relations[0].key ==
                          original.entry().project().assets()[0].identity(),
                  "captured asset binding lost");
          const auto &retained = *decoded.relations[0].asset;
          if (air) {
            require(retained.air()->constraints().size() == 4 &&
                        retained.air()->constraints()[2].scope.lookahead == 1,
                    "AIR scopes or transition window changed");
            AIRTrace values{{"bls12-381.fr", 3, 2},
                            {"2", "0", "4", "0", "16", "0"}};
            require(take(retained.air()->evaluate(values, {"2"})).satisfied,
                    "captured AIR interpretation changed");
            values.cells[2] = "5";
            require(!take(retained.air()->evaluate(values, {"2"})).satisfied,
                    "captured AIR omitted a transition constraint");
          } else {
            require(take(evaluate(*retained.r1cs(), {"9"}, {"1", "9", "3"}))
                        .satisfied,
                    "captured R1CS interpretation changed");
            require(
                !take(evaluate(*retained.r1cs(), {"8"}, {"1", "9", "3"})).bound,
                "captured R1CS lost the public prefix binding");
          }
          auto changed = RelationAsset::read(
              {"different",
               asset.format,
               zkc::printJson(
                   air ? take(AIR::create("bls12-381.fr", 2, 1, {})).encode()
                       : take(R1CS::create("bls12-381.fr", 3, 0, 1, {}))
                             .encode()),
               {}});
          auto other = take(std::move(changed));
          refuses(readInterface(original.bytes(), original.interfaceJson(), {},
                                {other}),
                  "source.interface");
          take(compileEntry(original));
        }
      });
  cases.run("unused invalid predicate observations fail before export", [&] {
    auto selected = close(R"(module sample;domain F=field("bls12-381.fr");
      relation Bad(statement x:F){
        let p=intrinsic<F,2>("poly.from_coefficients",intrinsic<F,2>("array.pack",[x,x]));
        let unused=intrinsic<F,1>("poly.coefficients",p);
        return x==x;
      }
      protocol Run roles(P)(x:F@P)->(ok:bool@P)
      spec{target claim=Bad(in.x) accept out.ok;}{return(ok=true);}entry Demo=Run;)");
    auto invalid = prepareOriginal(selected);
    require(!invalid, "invalid predicate observation accepted");
    auto message = toString(invalid.takeError());
    require(StringRef(message).contains("target.admission") &&
                StringRef(message).contains("sample::Bad"),
            message);
  });
  cases.run("formula revisions bind full record schemas across captures", [&] {
    auto make = [&](StringRef first, StringRef second) {
      return take(prepareOriginal(close(
          "module sample;struct Pair{pub " + first.str() + ":bool,pub " +
          second.str() + ":bool}relation Equal(statement x:Pair){return x." +
          first.str() + "==x." + second.str() +
          ";}protocol Run roles(P)(x:Pair@P)->(ok:bool@P)"
          "spec{target t=Equal(in.x) accept out.ok;}{return(ok=true);}entry "
          "Demo=Run;")));
    };
    auto a = make("a", "b"), b = make("c", "d");
    require(a.interface().relations[0].key == b.interface().relations[0].key &&
                a.interface().relations[0].inputs[0].schema->identity ==
                    b.interface().relations[0].inputs[0].schema->identity &&
                a.interface().relations[0].revision !=
                    b.interface().relations[0].revision,
            "renaming record fields did not change the predicate revision");
  });
  cases.run(
      "standalone admission binds exact retained bytes and checked source",
      [&] {
        auto original = take(prepareOriginal(entry));
        auto admitted = take(
            admitOriginal(entry, original.bytes(), original.interfaceJson()));
        require(admitted.identity() == original.identity() &&
                    admitted.interfaceJson() == original.interfaceJson(),
                "admission changed bytes");
        auto reformatted = "  " + original.interfaceJson().str() + "\n";
        if (auto error = checkInterface(original, reformatted))
          throw std::runtime_error(toString(std::move(error)));
        refuses(admitOriginal(entry, original.bytes(), reformatted),
                "source.interface");
        auto rejectEncoding = [&](StringRef bytes) {
          auto encoded = take(json::parse(original.interfaceJson()));
          (*encoded.getAsObject())["original"] =
              toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
          // Semantic correspondence alone deliberately ignores spelling.
          auto candidate = parse(bytes);
          take(compareOriginal(entry, *candidate));
          refuses(admitOriginal(entry, bytes, zkc::printJson(encoded)),
                  "source.correspondence");
        };
        rejectEncoding(original.bytes().str() + "\n// alternate encoding\n");
        for (bool location : {false, true}) {
          auto candidate = parse(original.bytes());
          auto declaration = relation(*candidate);
          if (location)
            declaration->setLoc(mlir::FileLineColLoc::get(
                &context, "zkc-language-original.mlir", 1, 1));
          else
            declaration->moveBefore(&declaration->getBlock()->front());
          std::string bytes;
          raw_string_ostream stream(bytes);
          candidate->print(
              stream, zkc::canonicalPrintingFlags().enableDebugInfo(location));
          rejectEncoding(bytes);
        }
        refuses(admitOriginal(entry, original.bytes().str() + "\n",
                              original.interfaceJson()),
                "source.interface");
        auto changedSource = source.str();
        changedSource.replace(changedSource.find("return same(x,y);"),
                              StringRef("return same(x,y);").size(),
                              "return true;");
        auto other = close(changedSource);
        refuses(
            admitOriginal(other, original.bytes(), original.interfaceJson()),
            "source.correspondence");
        Limits limit;
        limit.irBytes = 1;
        refuses(admitOriginal(entry, original.bytes(), original.interfaceJson(),
                              limit),
                "source.limit");
      });
  cases.run("predicate-only helper cycles fail native formation", [&] {
    auto original = take(prepareOriginal(entry));
    auto candidate = parse(original.bytes());
    mlir::func::FuncOp helper;
    candidate->walk([&](mlir::func::FuncOp op) {
      if (!op.getSymName().starts_with("zkf_"))
        helper = op;
    });
    require(bool(helper), "missing predicate dependency");
    auto returned = mlir::cast<mlir::func::ReturnOp>(helper.front().back());
    mlir::OpBuilder builder(returned);
    auto recursive = mlir::func::CallOp::create(builder, helper.getLoc(),
                                                helper, helper.getArguments());
    returned.setOperand(0, recursive.getResult(0));
    std::string bytes;
    raw_string_ostream stream(bytes);
    candidate->print(stream, zkc::canonicalPrintingFlags());
    refuses(readInterface(bytes, original.interfaceJson()), "target.admission");
  });
  cases.run("native predicate checks honor the caller work budget", [&] {
    uint64_t work = 1;
    auto failure = zkc::mathematical::checkFormulaDefinitions(*module, work);
    require(bool(failure), "low native predicate budget accepted");
    require(StringRef(toString(std::move(failure))).contains("source.limit"),
            "limit was misclassified");
  });
  for (StringRef observed : {"fixed", "sum", "interpolated", "recovered"})
    for (bool fits : {false, true})
      cases.run("executed and predicate-only polynomial recipes: " + observed +
                    (fits ? " fitting" : " under-width"),
                [&] {
                  unsigned width = observed == "recovered" ? 3 : 2;
                  if (!fits)
                    --width;
                  std::string helper =
                      R"(module sample;domain F=field("bls12-381.fr");
          math fn probe(x:F)->bool {
            let table=intrinsic<F,4>("array.pack",[x,x,x,x]);
            let p=intrinsic<F,2>("poly.mle",table);
            let fixed=intrinsic<F,1,1>("poly.fix",p,[x]);
            let sum=intrinsic<F,1,1>("poly.sum_suffix",p);
            let reduced=intrinsic<F,1,1>("poly.fix_table",table,[x]);
            let interpolated=intrinsic<F,1>("poly.mle",reduced);
            let samples=intrinsic<F>("poly.evaluate_domain",fixed;"0","1","2");
            let recovered=intrinsic<F>("poly.interpolate",samples;"0","1","2");
            let unused=intrinsic<F,)" +
                      std::to_string(width) + ">(" + "\"poly.coefficients\"," +
                      observed.str() + R"();
            return x==x;
          })";
                  auto run = take(prepareOriginal(close(helper + R"(
          protocol Run roles(P)(x:F@P)->(ok:bool@P){return(ok=probe(x));}
          entry Demo=Run;)")));
                  auto executed = compileEntry(run);
                  require(bool(executed) == fits,
                          "execution observation verdict differs");
                  if (!executed) {
                    auto message = toString(executed.takeError());
                    require(StringRef(message).contains("fitting degree bound"),
                            message);
                  }
                  auto specified = prepareOriginal(close(helper + R"(
          relation R(statement x:F){return probe(x);}
          protocol Run roles(P)(x:F@P)->(ok:bool@P)
          spec{target t=R(in.x) accept out.ok;}{return(ok=true);}entry Demo=Run;)"));
                  require(bool(specified) == fits,
                          "predicate-only observation verdict differs");
                  if (!specified) {
                    auto message = toString(specified.takeError());
                    require(
                        StringRef(message).contains("target.admission") &&
                            StringRef(message).contains("sample::probe") &&
                            StringRef(message).contains("fitting degree bound"),
                        message);
                  }
                });
  cases.run("helper DAG expansion exhausts one shared observation budget", [&] {
    std::string text = "module sample;math fn f0(x:bool)->bool{return x;}";
    for (unsigned i = 1; i < 9; ++i)
      text += "math fn f" + std::to_string(i) + "(x:bool)->bool{return f" +
              std::to_string(i - 1) + "(x)==f" + std::to_string(i - 1) +
              "(x);}";
    text += "relation R(statement x:bool){return f8(x);}"
            "protocol Run roles(P)(x:bool@P)->(ok:bool@P)"
            "spec{target t=R(in.x) accept out.ok;}{return(ok=true);}entry "
            "Demo=Run;";
    auto original = take(prepareOriginal(close(text)));
    auto parsed = parse(original.bytes());
    uint64_t remaining = 600;
    mlir::ScopedDiagnosticHandler quiet(
        &context, [](mlir::Diagnostic &) { return mlir::success(); });
    auto failure =
        zkc::mathematical::checkFormulaDefinitions(*parsed, remaining);
    require(bool(failure), "exponential helper expansion escaped budget");
    auto message = toString(std::move(failure));
    require(StringRef(message).contains("source.limit") &&
                StringRef(message).contains("observation"),
            message);
  });
  cases.run("many predicates share one charged helper definition digest", [&] {
    std::string text = "module sample;math fn shared(x:bool)->bool{";
    for (unsigned i = 0; i < 400; ++i)
      text += "let a" + std::to_string(i) + "=" +
              (i ? "a" + std::to_string(i - 1) : "x") + "==x;";
    text += "return a399;}";
    for (unsigned i = 0; i < 30; ++i)
      text += "relation R" + std::to_string(i) +
              "(statement x:bool){return shared(x);}";
    text += "protocol Run roles(P)(x:bool@P)->() spec{";
    for (unsigned i = 0; i < 30; ++i)
      text +=
          "input c" + std::to_string(i) + "=R" + std::to_string(i) + "(in.x);";
    text += "}{return ();}entry Demo=Run;";
    auto original = take(prepareOriginal(close(text)));
    require(original.interface().relations.size() == 30,
            "shared predicate closure omitted roots");
    take(readInterface(original.bytes(), original.interfaceJson()));
  });
  cases.run(
      "global MLIR printer flags cannot erase formula bodies or identities",
      [&] {
        auto baseline = take(prepareOriginal(entry));
        mlir::registerAsmPrinterCLOptions();
        const char *arguments[] = {
            "specification-test",
            "--mlir-print-skip-regions",
            "--mlir-print-value-users",
            "--mlir-print-unique-ssa-ids",
            "--mlir-use-nameloc-as-prefix",
            "--mlir-print-elementsattrs-with-hex-if-larger=0",
            "--mlir-elide-elementsattrs-if-larger=0",
            "--mlir-elide-resource-strings-if-larger=0"};
        require(cl::ParseCommandLineOptions(std::size(arguments), arguments),
                "printer flag setup failed");
        auto hostile = take(prepareOriginal(entry));
        require(hostile.bytes() == baseline.bytes() &&
                    hostile.interface().relations[0].revision ==
                        baseline.interface().relations[0].revision,
                "host printer flags changed formula identity");
        auto changedSource = source.str();
        changedSource.replace(changedSource.find("return same(x,y);"),
                              StringRef("return same(x,y);").size(),
                              "return true;");
        auto other = close(changedSource);
        auto changed = take(prepareOriginal(other));
        require(changed.interface().relations[0].revision !=
                    baseline.interface().relations[0].revision,
                "global flags erased predicate body identity");
      });
  return cases.result();
}
