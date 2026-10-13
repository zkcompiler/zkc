#include "../lib/Language/FiniteContracts.h"
#include "../lib/Language/HelperResults.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace source_detail = zkc::language::detail;
namespace {
const std::string prelude = R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
type Array<F:Field,N:nat>=builtin("field_array",F,N);
domain fn indices<F:Field>(xs:Vector<F>)->domain<index>=domain("indices");
math fn total<I:Type+Copy+Drop>(rows:domain<I>,initial:Fr,step:math fn(Fr,item:I)->Fr where item_from(item,rows))->Fr=finite("math.fold");
math fn vector_id(xs:Vector<Fr>)->Vector<Fr>{return xs;}
math fn index_id(i:index)->index{return i;}
math fn nested(xs:Vector<Fr>)->Vector<Fr>{return vector_id(vector_id(xs));}
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return intrinsic<Vector<Fr>>("container.at",xs,i);}
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture({{"m", prelude + source.str(), "forwarding.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
void emit(const CheckedProject &project, mlir::MLIRContext &context) {
  auto closed = take(closeEntry(project, "m::Run"));
  if (auto error = checkScopedSpecialization(closed))
    throw std::runtime_error(toString(std::move(error)));
  auto bytes = take(emitOriginal(closed, context));
  auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(module) && succeeded(mlir::verify(*module)),
          "forwarding original did not verify");
  take(compareOriginal(closed, *module));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  for (StringRef forwarded : {"vector_id(xs)", "nested(xs)"})
    cases.run("exact identity " + forwarded, [&] {
      auto project = take(check(
          "math fn subject(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs)"
          "{return at(" +
          forwarded.str() +
          ",index_id(i));}\n"
          "math fn run(xs:Vector<Fr>)->Fr{return total(indices(xs),0,"
          "fn(s,i)=>s+subject(xs,i));}\n"
          "protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return run(xs);}"
          "run Run=Demo;"));
      emit(project, context);
    });
  cases.run("forwarded literal index emits", [&] {
    emit(take(check(R"(
math fn subject(xs:Array<Fr,4>)->Fr{return intrinsic<Array<Fr,4>>("container.at",xs,index_id(index_id(3)));}
fn fixed_read(xs:Vector<Fr>)->Fr{let packed=kernel<Fr,4>("field_array.from_vector",xs);return subject(packed);}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return fixed_read(xs);}run Run=Demo;
)")),
         context);
  });
  cases.run("full nested record projection emits", [&] {
    emit(take(check(R"(
struct Inner{pub values:Vector<Fr>,pub other:Vector<Fr>}
struct Outer{pub inner:Inner}
math fn inner(x:Outer)->Inner{return x.inner;}
math fn values(x:Inner)->Vector<Fr>{return x.values;}
math fn subject(x:Outer)->Fr{return total(indices(values(inner(x))),0,fn(s,i)=>s+at(x.inner.values,i));}
protocol Demo roles(P)(x:Outer@P)->(r:Fr@P){return subject(x);}run Run=Demo;
)")),
         context);
  });
  cases.run("forwarded domain container and callback captures emit", [&] {
    emit(take(check(R"(
math fn subject(xs:Vector<Fr>)->Fr{let ys=nested(xs);return total(indices(ys),0,fn(s,i)=>s+at(xs,index_id(i)));}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return subject(xs);}run Run=Demo;
)")),
         context);
  });
  for (
      StringRef source :
      {R"(math fn subject(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let a=vector_id(xs);let b=vector_id(ys);return at(b,i);})",
       R"(struct Pair{pub xs:Vector<Fr>,pub ys:Vector<Fr>} math fn second(p:Pair)->Vector<Fr>{return p.ys;} math fn subject(p:Pair,i:index)->Fr where in_bounds(i,p.xs){return at(second(p),i);})",
       R"(math fn conditional(xs:Vector<Fr>,i:index)->Vector<Fr> where in_bounds(i,xs){return xs;} math fn subject(xs:Vector<Fr>,i:index)->Fr{return at(conditional(xs,i),i);})",
       R"(math fn subject(xs:Array<Fr,4>)->Fr{return intrinsic<Array<Fr,4>>("container.at",xs,index_id(4));})"})
    cases.run("forwarding cannot invent premise " + source.take_front(65),
              [&] { refuses(check(source), "source.data-bound"); });
  cases.run("projected item cannot become the whole originating item", [&] {
    refuses(check(R"(
math fn first(x:(index,index))->index{return index_id(x.0);}
math fn apply_pair(rows:domain<(index,index)>,body:math fn(item:(index,index))->Fr where item_from(item,rows))->Fr{return total(rows,0,fn(s,item)=>s+body((first(item),item.1)));}
)"),
            "source.scoped-domain");
  });
  cases.run("record return preserves whole-item callback provenance", [&] {
    emit(take(check(R"(
math fn pair(x:index)->(index,index){return (x,x);}
math fn apply(rows:domain<index>,body:math fn(item:index)->Fr where item_from(item,rows))->Fr{return total(rows,0,fn(s,item)=>{let paired=pair(item);s+body(paired.0)});}
math fn subject(xs:Vector<Fr>)->Fr{return apply(indices(xs),fn(i)=>at(xs,i));}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return subject(xs);}run Run=Demo;
)")),
         context);
  });
  cases.run("record return cannot substitute an unrelated callback item", [&] {
    refuses(check(R"(
math fn pair(x:index,y:index)->(index,index){return (x,y);}
math fn apply(rows:domain<index>,other:index,body:math fn(item:index)->Fr where item_from(item,rows))->Fr{return total(rows,0,fn(s,item)=>{let paired=pair(item,other);s+body(paired.1)});}
)"),
            "source.scoped-domain");
  });
  cases.run("whole item survives exact helper forwarding", [&] {
    emit(take(check(R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
domain fn product(a:domain<index>,b:domain<index>)->domain<(index,index)>=domain("product");
math fn pair_id(x:(index,index))->(index,index){return x;}
math fn apply_pair(rows:domain<(index,index)>,body:math fn(item:(index,index))->Fr where item_from(item,rows))->Fr{return total(rows,0,fn(s,item)=>s+body(pair_id(item)));}
math fn subject()->Fr{return apply_pair(product(range(0,2),range(1,3)),fn(pair)=>1);}
protocol Demo roles(P)()->(r:Fr@P){return subject();}run Run=Demo;
)")),
         context);
  });
  cases.run("generic identity uses actual value and complete selector", [&] {
    emit(take(check(R"(
math fn generic<F:Field>(xs:Vector<F>)->Vector<F>{return xs;}
math fn second(xs:Vector<Fr>,ys:Vector<Fr>)->Vector<Fr>{return generic<Fr>(ys);}
math fn subject(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return total(indices(ys),0,fn(s,i)=>s+at(second(xs,ys),i));}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P)->(r:Fr@P){return subject(xs,ys);}run Run=Demo;
)")),
         context);
  });
  cases.run("memoized extraction retains an exact work boundary", [&] {
    auto project = take(check(R"(
math fn subject(xs:Vector<Fr>,ys:Vector<Fr>)->Vector<Fr>{let a=nested(xs);return nested(ys);}
)"));
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    auto subject = llvm::find_if(declarations, [](const auto &declaration) {
      return declaration.name == "subject";
    });
    require(subject != declarations.end(), "missing forwarding subject");
    unsigned subjectIndex = subject->id.index;
    auto measure = [&](const Limits &limits) -> std::pair<bool, uint64_t> {
      source_detail::Work work{limits};
      source_detail::Semantics types(declarations, project.assets(), work);
      const auto &declaration = declarations[subjectIndex];
      source_detail::HelperResults results(types, declarations);
      bool accepted = source_detail::checkFiniteContracts(
          types, declarations, declaration, *declaration.body, results);
      if (!accepted)
        require(types.diagnostic && types.diagnostic->code == "source.limit",
                "unexpected bounded forwarding diagnostic");
      return {accepted, work.used};
    };
    Limits limits;
    auto [accepted, cost] = measure(limits);
    require(accepted && cost, "unbounded forwarding failed");
    limits.work = cost;
    require(measure(limits).first, "last available work unit was refused");
    limits.work = cost - 1;
    require(!measure(limits).first, "insufficient work was admitted");
    limits = Limits{};
    limits.expressionDepth = 2;
    require(measure(limits).first, "lexical depth reduced helper allowance");
    limits.expressionDepth = 1;
    require(measure(limits).first, "SSA forwarding consumed lexical depth");
    limits.callDepth = 0;
    require(!measure(limits).first, "nested forwarding ignored call depth");
    // An additional declaration requires its own extraction. Reusing one
    // summary must cost less than reading an identical fresh declaration.
    auto body = std::make_shared<Body>(*declarations[subjectIndex].body);
    HelperCall *last = nullptr;
    for (auto &op : body->operations)
      if (auto *call = std::get_if<HelperCall>(&op.action))
        last = call;
    require(last, "missing repeated forwarding call");
    Declaration clone = declarations[last->callee.index];
    clone.id.index = declarations.size();
    last->callee = clone.id;
    declarations.push_back(std::move(clone));
    declarations[subjectIndex].body = std::move(body);
    auto [uncachedAccepted, uncachedCost] = measure(Limits{});
    require(uncachedAccepted && uncachedCost > cost,
            "repeated calls paid for extracting the same declaration");
  });
  cases.run("unsuccessful nested query retains cached depth", [&] {
    for (StringRef prefix : {"", "let warm=via<M>(0);"}) {
      auto project = take(check(
          "interface Relay{math fn pass(x:Fr)->Fr;}"
          "math fn via<M:Relay>(x:Fr)->Fr{return M::pass(x);}"
          "math fn subject<M:Relay>(xs:Vector<Fr>)->Fr{" +
          prefix.str() + "return total(indices(xs),0,fn(s,i)=>via<M>(s));}"));
      std::vector<Declaration> declarations(project.declarations().begin(),
                                            project.declarations().end());
      auto subject = llvm::find_if(declarations, [](const auto &declaration) {
        return declaration.name == "subject";
      });
      require(subject != declarations.end(),
              "missing abstract forwarding subject");
      for (unsigned depth : {0u, 1u}) {
        Limits limits;
        limits.callDepth = depth;
        source_detail::Work work{limits};
        source_detail::Semantics types(declarations, project.assets(), work);
        source_detail::HelperResults results(types, declarations);
        bool accepted = source_detail::checkFiniteContracts(
            types, declarations, *subject, *subject->body, results);
        require(accepted == (depth == 1),
                "warming the forwarding memo changed depth admission");
        if (!accepted)
          require(types.diagnostic && types.diagnostic->code == "source.limit",
                  "unexpected abstract forwarding diagnostic");
      }
    }
  });
  cases.run("shared forwarding dependencies do not expand logical work", [&] {
    std::string source = "math fn h0(x:Fr)->Fr{return x;}\n";
    for (unsigned i = 1; i <= 24; ++i) {
      auto prior = "h" + std::to_string(i - 1);
      source += "math fn h" + std::to_string(i) + "(x:Fr)->Fr{return " + prior +
                "(" + prior + "(x));}\n";
    }
    take(check(source));
  });
  cases.run("generic module dispatch supplies no concrete forwarding fact",
            [&] {
              refuses(check(R"(
interface Relay{math fn pass(xs:Vector<Fr>)->Vector<Fr>;}
module Identity:Relay{math fn pass(xs:Vector<Fr>)->Vector<Fr>{return xs;}}
math fn subject<M:Relay>(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(M::pass(xs),i);}
)"),
                      "source.data-bound");
            });
  return cases.result();
}
