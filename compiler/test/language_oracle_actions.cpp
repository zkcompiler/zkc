#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Transforms/Mathematical.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
const char *prefix = R"(
module m;
domain F=field("bls12-381.fr");
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Oracle<K:OracleKind>=builtin("oracle",K);
type Vec=builtin("vector",F);
type O=Oracle<Fixed<F,16>>;
type Dynamic=Oracle<Table<F>>;
)";
Expected<CheckedProject> check(StringRef code) {
  auto captureResult =
      capture({{"m", std::string(prefix) + code.str(), "oracle.zkc"}});
  if (!captureResult)
    return captureResult.takeError();
  return analyze(*captureResult).checkedProject();
}
CheckedOriginal original(StringRef code) {
  auto project = take(check(code));
  auto source =
      take(prepareOriginal(take(zkc::test::closeNativeRun(project, "m::Run"))));
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
  require(bool(module), "source failed to parse");
  auto prepared = mathematical::prepareProtocol(*module);
  require(bool(prepared), "checked oracle preparation failed");
  auto snapshot = take(protocol::exportStructuredSource(
      source.bytes(), source.entry().protocol().symbol, context));
  require(!snapshot.bytes.empty(), "oracle structured export is empty");
  return source;
}
const char *repeated = R"(
protocol Run roles(P,V)(xs:Vec@P)->(out:F@V) {
 #[site(word)] let h=send P->V(xs) as oracle<Fixed<F,16>>;
 #[site(first)] let unused@V=query h at 0;
 #[site(second)] let answer@V=query h at 0;
 return(out=answer);
}
)";
unsigned occurrenceCount(StringRef text, StringRef name) {
  unsigned n = 0;
  while (text.contains(name)) {
    text = text.split(name).second;
    ++n;
  }
  return n;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("sized delivery retains repeated and unused query events", [] {
    auto source = original(repeated);
    require(occurrenceCount(source.bytes(), "protocol.oracle_send") == 1 &&
                occurrenceCount(source.bytes(), "protocol.oracle_query") == 2,
            "an oracle event disappeared");
  });
  cases.run("holder data and row views preserve a port anchor", [] {
    auto source = original(R"(
    protocol Run roles(P,V)(h:O@P->V)->(xs:Vec@P,n:index@(P,V),h2:Dynamic@P->V max 16){
      let xs=oracle.data(h);let n=oracle.rows(h);let h2=oracle.forget_rows(h);
      return(xs=xs,n=n,h2=h2);
    }
   )");
    require(source.bytes().contains("protocol.oracle_contents") &&
                source.bytes().contains("protocol.oracle_shape") &&
                source.bytes().contains("protocol.oracle_forget_shape"),
            "oracle views were erased");
  });
  cases.run("unsized delivery retains shared shape and full unsigned maximum",
            [] {
              auto source = original(R"(
    protocol Run roles(P,V)(xs:Vec@P,n:index@(P,V))->(out:F@V){
      let h=send P->V(xs) as oracle<Table<F>>(rows=n) max 18446744073709551615;
      let out@V=query h at 0;return(out=out);
    }
   )");
              require(source.bytes().contains("18446744073709551615"),
                      "maximum narrowed");
            });
  cases.run("generic kind queries use forward associated types", [] {
    original(R"(
    protocol Read<K:OracleKind> roles(A,B)(h:Oracle<K>@A->B,p:K::Query@B)->(out:K::Answer@B){
      let out@B=query h at p;return(out=out);
    }
    protocol Run roles(P,V)(h:O@P->V)->(out:F@V){
      let out=Read<Fixed<F,16>> roles(P,V)(h,0);return(out=out);
    }
   )");
  });
  cases.run("generic sized delivery closes its inferred shape", [] {
    original(R"(
    protocol Deliver<N:nat> roles(A,B)(xs:Vec@A)->(h:Oracle<Fixed<F,N>>@A->B){
      let h=send A->B(xs) as oracle<Fixed<F,N>>;return(h=h);
    }
    protocol Run roles(P,V)(xs:Vec@P)->(out:F@V){
      let h=Deliver<16> roles(P,V)(xs);let out@V=query h at 0;return(out=out);
    }
   )");
  });
  cases.run("generic unsized delivery closes its maximum", [] {
    original(R"(
      protocol Deliver<M:nat> roles(A,B)(xs:Vec@A,n:index@(A,B))->(h:Dynamic@A->B max M){
        let h=send A->B(xs) as oracle<Table<F>>(rows=n) max M;return(h=h);
      }
      protocol Run roles(P,V)(xs:Vec@P,n:index@(P,V))->(out:F@V){
        let h=Deliver<16> roles(P,V)(xs,n);let out@V=query h at 0;return(out=out);
      }
    )");
  });
  cases.run("loop successors retain a holder while changing the anchor", [] {
    original(R"(
      protocol Run roles(P,V)(h:O@P->V,xs:Vec@P,n:index@(P,V))->(out:F@V){
        let mut current=h;
        for i in 0..n roles(P,V) max 4 {
          current=send P->V(xs) as oracle<Fixed<F,16>>;
        }
        let out@V=query current at 0;return(out=out);
      }
    )");
  });
  cases.run("packed answer rows preserve product fields", [] {
    original(R"(
    type Packed=Oracle<Fixed<(bool,index),8>>;
    protocol Run roles(P,V)(h:Packed@P->V)->(out:(bool,index)@V){
      let out@V=query h at 0;return(out=out);
    }
   )");
  });
  cases.run("query role selection handles multiple receivers", [] {
    original(R"(
    protocol Run roles(C,A,B)(xs:Vec@A)->(out:F@C){
      let h=send A->(B,C)(xs) as oracle<Fixed<F,16>>;
      let out@C=query h at 0;return(out=out);
    }
   )");
  });
  cases.run("loop captures keep the oracle family and repeated event", [] {
    auto source = original(R"(
    protocol Run roles(P,V)(h:O@P->V,n:index@(P,V))->(ok:bool@V){
      for i in 0..n roles(P,V) max 4 {let out@V=query h at i;}
      let ok@V=true;return(ok=ok);
    }
   )");
    require(source.bytes().contains("protocol.repeat") &&
                source.bytes().contains("protocol.oracle_query"),
            "loop event disappeared");
  });
  for (auto [name, body, code] :
       {std::tuple{"receiver data extraction", "let xs@V=oracle.data(h);",
                   "source.roles"},
        {"holder query", "let x@P=query h at 0;", "source.roles"},
        {"data passed as handle", "let x=oracle.rows(n);",
         "source.oracle-action"},
        {"partial handle alias", "let x@V=h;", "source.oracle-role"},
        {"invalid oracle action", "let x=oracle.missing(h);",
         "source.oracle-action"}})
    cases.run(Twine("refuse ") + name, [body = body, code = code] {
      refuses(
          check(
              "protocol Run roles(P,V)(h:O@P->V,n:index@(P,V))->(ok:bool@V){" +
              std::string(body) + "let ok@V=true;return(ok=ok);}"),
          code);
    });
  cases.run("refuse unsized send without shape", [] {
    refuses(check(R"(protocol Run roles(P,V)(xs:Vec@P)->(ok:bool@V){
     let h=send P->V(xs) as oracle<Table<F>>;let ok@V=true;return(ok=ok);})"),
            "source.oracle-shape");
  });
  cases.run("refuse sized send with explicit shape", [] {
    refuses(
        check(R"(protocol Run roles(P,V)(xs:Vec@P,n:index@(P,V))->(ok:bool@V){
     let h=send P->V(xs) as oracle<Fixed<F,16>>(rows=n);let ok@V=true;return(ok=ok);})"),
        "source.oracle-shape");
  });
  cases.run("refuse holder-only dynamic shape", [] {
    refuses(check(R"(protocol Run roles(P,V)(xs:Vec@P,n:index@P)->(ok:bool@V){
     let h=send P->V(xs) as oracle<Table<F>>(rows=n) max 16;let ok@V=true;return(ok=ok);})"),
            "source.roles");
  });
  cases.run("refuse wrong mapped holder at a protocol call", [] {
    refuses(check(R"(
    protocol Forward roles(A,B)(h:O@A->B)->(out:O@A->B){return(out=h);}
    protocol Run roles(P,V)(h:O@P->V)->(ok:bool@V){
      let x=Forward roles(V,P)(h);let ok@V=true;return(ok=ok);
    })"),
            "source.oracle-role");
  });
  cases.run("refuse a return that reverses the holder", [] {
    refuses(
        check(
            R"(protocol Run roles(P,V)(h:O@P->V)->(out:O@V->P){return(out=h);})"),
        "source.oracle-role");
  });
  cases.run("refuse an ambiguous query receiver", [] {
    refuses(check(R"(protocol Run roles(P,V,W)(h:O@P->(V,W))->(ok:bool@V){
      let x=query h at 0;let ok@V=true;return(ok=ok);})"),
            "source.owner");
  });
  cases.run("refuse forgetting an already unsized kind", [] {
    refuses(
        check(R"(protocol Run roles(P,V)(h:Dynamic@P->V max 16)->(ok:bool@V){
      let x=oracle.forget_rows(h);let ok@V=true;return(ok=ok);})"),
        "source.oracle-shape");
  });
  cases.run("refuse unsized send without a maximum", [] {
    refuses(
        check(R"(protocol Run roles(P,V)(xs:Vec@P,n:index@(P,V))->(ok:bool@V){
      let h=send P->V(xs) as oracle<Table<F>>(rows=n);let ok@V=true;return(ok=ok);})"),
        "source.oracle-shape");
  });
  cases.run("refuse non-natural send maximum", [] {
    refuses(
        check(R"(protocol Run roles(P,V)(xs:Vec@P,n:index@(P,V))->(ok:bool@V){
      let h=send P->V(xs) as oracle<Table<F>>(rows=n) max bool;let ok@V=true;return(ok=ok);})"),
        "source.oracle-shape");
  });
  cases.run("written syntax retains distinct sends and queries", [] {
    auto ast = take(inspectWrittenSource(take(check(repeated))));
    require(ast.find("expr.oracle_send") != std::string::npos &&
                ast.find("expr.oracle_query") != std::string::npos,
            "written actions became ordinary calls");
  });
  cases.run("independent comparison rejects a well-formed position change", [] {
    auto source = original(repeated);
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
    require(bool(module), "original failed to parse");
    bool changed = false;
    module->walk([&](protocol_ir::OracleQueryOp query) {
      auto *position = query.getPosition().getDefiningOp();
      if (!changed && position &&
          position->getName().getStringRef() == "data.index") {
        position->setAttr("value", mlir::StringAttr::get(&context, "1"));
        changed = true;
      }
    });
    require(changed && mlir::succeeded(mlir::verify(*module)),
            "position mutation must remain well formed");
    refuses(compareOriginal(source.entry(), *module), "source.correspondence");
  });
  return cases.result();
}
