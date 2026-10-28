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
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Oracle<K:OracleKind>=builtin("oracle",K);
type O=Oracle<Fixed<F,16>>;
)";
Expected<CheckedProject> check(StringRef code) {
  auto project =
      capture({{"m", std::string(prefix) + code.str(), "sequence.zkc"}});
  if (!project)
    return project.takeError();
  return analyze(*project).checkedProject();
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
const char *selectionSubject = R"(
 protocol Run roles(P,V)(a:O@P->V,b:O@P->V,i:index@(P,V))->(out:F@V){
   let empty=oracle.empty<Fixed<F,16>,2> roles(P,V)();
   let first=oracle.append(empty,a);let both=oracle.append(first,b);
   let chosen=oracle.at(both,i);let out@V=query chosen at 0;return(out=out);
 }
)";
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("runtime selection retains the selected actual anchor", [] {
    auto source = original(selectionSubject);
    require(source.bytes().contains("protocol.oracle_sequence_at") &&
                source.bytes().contains("protocol.oracle_query"),
            "selection became a statically chosen anchor");
  });
  cases.run("empty sequence retains a family within a larger roster", [] {
    original(R"(
    protocol Run roles(P,V,W)()->(n:index@(P,V)){
      let empty=oracle.empty<Fixed<F,16>,0> roles(P,V)();
      let n=oracle.length(empty);return(n=n);
    })");
  });
  cases.run("loop appends retain bounded sequence state", [] {
    original(R"(
    protocol Run roles(P,V)(h:O@P->V,n:index@(P,V))->(out:F@V){
      let mut layers=oracle.empty<Fixed<F,16>,4> roles(P,V)();
      for i in 0..n roles(P,V) max 4 {layers=oracle.append(layers,h);}
      let chosen=oracle.at(layers,0);let out@V=query chosen at 0;return(out=out);
    })");
  });
  cases.run("generic capacity specializes through a returned handle", [] {
    original(R"(
    protocol Select<M:nat> roles(A,B)(h:O@A->B)->(out:O@A->B){
      let empty=oracle.empty<Fixed<F,16>,M> roles(A,B)();
      let layers=oracle.append(empty,h);let out=oracle.at(layers,0);return(out=out);
    }
    protocol Run roles(P,V)(h:O@P->V)->(out:F@V){
      let chosen=Select<1> roles(P,V)(h);let out@V=query chosen at 0;return(out=out);
    })");
  });
  cases.run("forgotten row refinements share one bounded layer sequence", [] {
    original(R"(
    type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
    type Small=Oracle<Fixed<F,8>>;
    protocol Run roles(P,V)(a:O@P->V,b:Small@P->V,i:index@(P,V))->(out:F@V){
      let empty=oracle.empty<Table<F>,2> roles(P,V)();
      let first=oracle.append(empty,oracle.forget_rows(a));
      let both=oracle.append(first,oracle.forget_rows(b));
      let chosen=oracle.at(both,i);let out@V=query chosen at 0;return(out=out);
    })");
  });
  cases.run("refuse a different holder in the same participant set", [] {
    refuses(check(R"(protocol Run roles(P,V)(h:O@P->V)->(ok:bool@V){
      let empty=oracle.empty<Fixed<F,16>,2> roles(V,P)();
      let invalid=oracle.append(empty,h);let ok@V=true;return(ok=ok);})"),
            "source.oracle-role");
  });
  cases.run("refuse appending a wider receiver family", [] {
    refuses(check(R"(protocol Run roles(P,V,W)(h:O@P->(V,W))->(ok:bool@V){
      let empty=oracle.empty<Fixed<F,16>,2> roles(P,V)();
      let invalid=oracle.append(empty,h);let ok@V=true;return(ok=ok);})"),
            "source.oracle-role");
  });
  cases.run("refuse a receiver-private sequence selector", [] {
    refuses(check(R"(protocol Run roles(P,V)(h:O@P->V,i:index@V)->(ok:bool@V){
      let empty=oracle.empty<Fixed<F,16>,2> roles(P,V)();
      let layers=oracle.append(empty,h);let invalid=oracle.at(layers,i);
      let ok@V=true;return(ok=ok);})"),
            "source.roles");
  });
  cases.run("refuse an empty family without receivers", [] {
    refuses(check(R"(protocol Run roles(P,V)()->(ok:bool@V){
      let empty=oracle.empty<Fixed<F,16>,2> roles(P)();let ok@V=true;return(ok=ok);})"),
            "source.oracle-role");
  });
  cases.run("refuse a nonnatural sequence capacity", [] {
    refuses(check(R"(protocol Run roles(P,V)()->(ok:bool@V){
      let empty=oracle.empty<Fixed<F,16>,bool> roles(P,V)();
      let ok@V=true;return(ok=ok);})"),
            "source.oracle-kind");
  });
  cases.run("zero-capacity selection retains its stopping operation", [] {
    auto source = original(R"(protocol Run roles(P,V)()->(out:F@V){
      let empty=oracle.empty<Fixed<F,16>,0> roles(P,V)();
      let chosen=oracle.at(empty,0);let out@V=query chosen at 0;return(out=out);})");
    require(source.bytes().contains("protocol.oracle_sequence_at"),
            "empty sequence selection lost its bounds check");
  });
  cases.run("refuse sequence operations on ordinary values", [] {
    refuses(check(R"(protocol Run roles(P,V)(x:index@P)->(ok:bool@V){
      let invalid=oracle.length(x);let ok@V=true;return(ok=ok);})"),
            "source.oracle-action");
  });
  cases.run("refuse oracle sequence creation inside local code", [] {
    refuses(
        check(
            R"(fn invalid()->index{let empty=oracle.empty<Fixed<F,16>,2> roles(P,V)();return 0;})"),
        "source.mode");
  });
  cases.run(
      "written source retains sequence operations and explicit family", [] {
        auto ast = take(inspectWrittenSource(take(check(selectionSubject))));
        for (const char *kind :
             {"expr.oracle_sequence_empty", "expr.oracle_sequence_append",
              "expr.oracle_sequence_at"})
          require(ast.find(kind) != std::string::npos,
                  "sequence syntax was erased");
      });
  cases.run(
      "independent comparison rejects replacing a valid selection input", [] {
        auto source = original(selectionSubject);
        mlir::DialectRegistry registry;
        registerDialects(registry);
        mlir::MLIRContext context(registry);
        context.loadAllAvailableDialects();
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
        require(bool(module), "original failed to parse");
        protocol_ir::OracleSequenceAppendOp first;
        bool changed = false;
        module->walk([&](mlir::Operation *op) {
          if (auto append =
                  mlir::dyn_cast<protocol_ir::OracleSequenceAppendOp>(op);
              append && !first)
            first = append;
          if (auto at = mlir::dyn_cast<protocol_ir::OracleSequenceAtOp>(op);
              at && first) {
            at.getSequenceMutable().assign(first.getOutput());
            changed = true;
          }
        });
        require(changed && mlir::succeeded(mlir::verify(*module)),
                "mutation must remain well formed");
        refuses(compareOriginal(source.entry(), *module),
                "source.correspondence");
      });
  return cases.result();
}
