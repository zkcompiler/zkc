#include "../lib/Language/FiniteContracts.h"
#include "../lib/Language/FiniteFormation.h"
#include "../lib/Language/HelperResults.h"
#include "../lib/Language/MathematicalFacts.h"
#include "../lib/Language/ValueOrigins.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Project.h"
#include <limits>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace source = zkc::language::detail;
namespace facts = zkc::facts;
namespace {
const std::string prelude = R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
type Matrix<F:Field>=builtin("matrix",F);
type Array<F:Field,N:nat>=builtin("field_array",F,N);
domain fn indices<F:Field>(xs:Vector<F>)->domain<index>=domain("indices");
domain fn coords<F:Field>(xs:Matrix<F>)->domain<(index,index)>=domain("matrix.coordinates.row_major");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return intrinsic<Vector<Fr>>("container.at",xs,i);}
)";
Expected<CheckedProject> check(StringRef text, const Limits &limits = {}) {
  auto captured = capture({{"m", prelude + text.str(), "facts.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == ("m::" + name).str())
      return decl;
  throw std::runtime_error("missing declaration");
}
struct Environment {
  Limits limits;
  source::Work work{limits};
  std::vector<Declaration> declarations;
  source::Semantics semantics{declarations, {}, work};
};
Type arrayType(Natural size) {
  Type result(Type::Kind::Builtin);
  result.domain = "field_array";
  Type dimension(Type::Kind::Natural);
  dimension.dimension = std::move(size);
  result.arguments = {Type(Type::Kind::Field), std::move(dimension)};
  return result;
}
void proven(facts::Status status) {
  require(status == facts::Status::Proven, "missing expected source fact");
}
} // namespace
int main() {
  Cases cases;
  cases.run("read-only mutable captures preserve mathematical facts", [] {
    auto project = take(check(R"(
fn preserve(xs:Vector<Fr>,c:bool,n:index)->Vector<Fr> {
 let mut values=xs;
 if c {let observed=values;} else {}
 for _ in 0..n {let observed=values;}
 return values;
})"));
    const auto &body = *named(project, "preserve").body;
    Environment env;
    source::ValueOrigins origins(env.semantics, body);
    auto origin = origins.get(body.results.front());
    require(origin && *origin == source::ValueOrigin{0, {}},
            "read-only control changed the returned value's origin");
  });
  cases.run(
      "helper input contracts transfer through symmetric transitive extents",
      [] {
        take(check(R"(
math fn forward(a:Vector<Fr>,b:Vector<Fr>,c:Vector<Fr>,i:index)->Fr
 where in_bounds(i,a),equal_extent(b,a),equal_extent(b,c){return at(c,i);}
)"));
      });
  cases.run("unrelated dynamic container cannot borrow a helper bound", [] {
    refuses(check(R"(
math fn forward(a:Vector<Fr>,b:Vector<Fr>,i:index)->Fr
 where in_bounds(i,a){return at(b,i);}
)"),
            "source.data-bound");
  });
  cases.run("normalized generic Natural dimensions transfer a bound", [] {
    take(check(R"(
math fn forward<N:nat,M:nat>(a:Array<Fr,N+M>,b:Array<Fr,M+N>,i:index)->Fr
 where in_bounds(i,a){return intrinsic<Array<Fr,M+N>>("container.at",b,i);}
)"));
  });
  cases.run("distinct generic Natural dimensions do not equate extents", [] {
    refuses(check(R"(
math fn forward<N:nat,M:nat>(a:Array<Fr,N>,b:Array<Fr,M>,i:index)->Fr
 where in_bounds(i,a){return intrinsic<Array<Fr,M>>("container.at",b,i);}
)"),
            "source.data-bound");
  });
  cases.run("generic helper dimensions retain their actual binding", [] {
    take(check(R"(
math fn pick<N:nat>(a:Array<Fr,N>,i:index)->Fr where in_bounds(i,a){
 return intrinsic<Array<Fr,N>>("container.at",a,i);
}
math fn caller<N:nat>(a:Array<Fr,N+1>,i:index)->Fr where in_bounds(i,a){
 return pick<N+1>(a,i);
}
)"));
    refuses(check(R"(
math fn pick<N:nat>(a:Array<Fr,N>,i:index)->Fr where in_bounds(i,a){
 return intrinsic<Array<Fr,N>>("container.at",a,i);
}
math fn caller<N:nat>(a:Array<Fr,N>,b:Array<Fr,N+1>,i:index)->Fr
 where in_bounds(i,a){return pick<N+1>(b,i);}
)"),
            "source.data-bound");
  });
  cases.run("equal fixed shapes preserve the exact bounded index", [] {
    take(check(R"(
math fn forward(a:Array<Fr,4>,b:Array<Fr,4>,i:index)->Fr
 where in_bounds(i,a){return intrinsic<Array<Fr,4>>("container.at",b,i);}
)"));
    refuses(check(R"(
math fn forward(a:Array<Fr,4>,b:Array<Fr,4>,i:index,j:index)->Fr
 where in_bounds(i,a){return intrinsic<Array<Fr,4>>("container.at",b,j);}
)"),
            "source.data-bound");
  });
  for (bool valid : {true, false})
    cases.run(valid ? "complete nested selector aliases preserve bounds"
                    : "a sibling nested selector has no borrowed bound",
              [&] {
                auto text = R"(
struct Leaf{pub xs:Vector<Fr>,pub ys:Vector<Fr>}
struct Data{pub left:Leaf,pub right:Leaf}
math fn read(data:Data,i:index)->Fr where in_bounds(i,data.left.xs){
 let alias=data.left;
 return at()" + std::string(valid ? "alias.xs" : "data.right.xs") +
                            ",i);}";
                if (valid)
                  take(check(text));
                else
                  refuses(check(text), "source.data-bound");
              });
  for (bool capture : {true, false})
    cases.run(capture ? "nested callback preserves its captured actual index"
                      : "nested callback formal index has a fresh origin",
              [&] {
                auto text = R"(
math fn apply(i:index,body:math fn(index)->Fr)->Fr{return body(i);}
math fn work(xs:Vector<Fr>)->Fr{
 return total(indices(xs),0,fn(state,i)=>state+apply(i,fn(j)=>at(xs,)" +
                            std::string(capture ? "i" : "j") + ")));}";
                if (capture)
                  take(check(text));
                else
                  refuses(check(text), "source.data-bound");
              });
  cases.run("distinct callback occurrences cannot share local index facts", [] {
    refuses(check(R"(
math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{
 let first=total(indices(xs),0,fn(state,i)=>state+at(xs,i));
 return total(indices(ys),first,fn(state,i)=>state+at(xs,i));
}
)"),
            "source.data-bound");
  });
  for (bool swapped : {false, true})
    cases.run(swapped ? "matrix coordinate axes cannot be exchanged"
                      : "matrix coordinate axes establish separate bounds",
              [&] {
                auto text = R"(
math fn work(xs:Matrix<Fr>)->Fr{
 return total(coords(xs),0,fn(state,(i,j))=>state+intrinsic<Matrix<Fr>>("matrix.at",xs,)" +
                            std::string(swapped ? "j,i" : "i,j") + "));}";
                if (swapped)
                  refuses(check(text), "source.data-bound");
                else
                  take(check(text));
              });
  for (unsigned index : {3, 4})
    cases.run("strict constant bound at " + std::to_string(index), [&] {
      auto text = "math fn work(xs:Array<Fr,4>)->Fr{return "
                  "intrinsic<Array<Fr,4>>(\"container.at\",xs," +
                  std::to_string(index) + ");}";
      if (index < 4)
        take(check(text));
      else
        refuses(check(text), "source.data-bound");
    });
  cases.run("total index literal overflow retains its diagnostic", [] {
    refuses(check("math fn bad()->index{return 18446744073709551616;}"),
            "source.literal");
  });
  cases.run("source finite callback conditions survive specialization", [] {
    auto project = take(check(R"(
math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr where equal_extent(xs,ys){
 return total(indices(xs),0,fn(state,i)=>state+at(ys,i));
}
math fn same(xs:Vector<Fr>)->Fr{return work(xs,xs);}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return same(xs);}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
    auto closed = take(zkc::test::closeProtocolDeployment(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  const std::string collections = R"(
domain fn elements(xs:Vector<Fr>)->domain<Fr>=domain("elements");
domain fn array_elements<N:nat>(xs:Array<Fr,N>)->domain<Fr>=domain("elements");
math fn mapped<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item,rows))->Vector<Fr>=finite("math.collect.vector");
math fn filtered<I:Type+Copy+Drop>(rows:domain<I>,keep:math fn(item:I)->bool where item_from(item,rows),body:math fn(item:I)->Fr where item_from(item,rows))->Vector<Fr>=finite("math.collect.vector_where");
math fn copy(xs:Vector<Fr>)->Vector<Fr>{return mapped(elements(xs),fn(x)=>x);}
)";
  for (StringRef mutation :
       {"body-domain", "call-input", "call-domain", "factory-data",
        "factory-child", "factory-parameter"})
    cases.run("helper result rejects malformed coverage: " + mutation, [&] {
      auto project = take(check(collections + R"(
domain fn selected(xs:Vector<Fr>)->domain<Fr>{return elements(xs);}
math fn selected_copy(xs:Vector<Fr>)->Vector<Fr>{return mapped(selected(xs),fn(x)=>x);}
math fn chain(xs:Vector<Fr>)->Vector<Fr>{return copy(xs);}
math fn from_domain(rows:domain<Fr>)->Vector<Fr>{return mapped(rows,fn(x)=>x);}
math fn applied(xs:Vector<Fr>)->Vector<Fr>{return from_domain(elements(xs));}
)"));
      Environment env;
      env.declarations = project.declarations().vec();
      auto target =
          named(project, mutation == "call-input"    ? "chain"
                         : mutation == "call-domain" ? "applied"
                         : mutation == "body-domain" ? "copy"
                                                     : "selected_copy")
              .id.index;
      if (mutation.starts_with("factory")) {
        auto factory = named(project, "selected").id.index;
        auto recipe = std::make_shared<DomainDefinition>(
            *env.declarations[factory].domainDefinition);
        require(!recipe->bindings.empty(), "missing domain recipe");
        if (mutation == "factory-data")
          recipe->bindings.front().operands = {{999999}};
        else if (mutation == "factory-parameter")
          recipe->bindings.front().parameter = 0;
        else
          recipe->bindings.front().children = {0};
        env.declarations[factory].domainDefinition = std::move(recipe);
      } else {
        auto body = std::make_shared<Body>(*env.declarations[target].body);
        if (mutation == "body-domain")
          body->domainBindings.clear();
        else {
          bool changed = false;
          for (auto &op : body->operations)
            if (auto *call = std::get_if<HelperCall>(&op.action)) {
              if (mutation == "call-domain")
                call->domainArguments.clear();
              else
                call->operands.clear();
              changed = true;
            }
          require(changed, "missing helper call");
        }
        env.declarations[target].body = std::move(body);
      }
      source::HelperResults results(env.semantics, env.declarations);
      require(!results.get(target, 0, {}, {}) && env.semantics.diagnostic &&
                  env.semantics.diagnostic->code == "source.scoped-domain",
              "malformed helper dependency did not refuse");
    });
  cases.run("unfiltered result extents cross nested helper calls", [&] {
    take(check(collections + R"(
math fn twice(xs:Vector<Fr>)->Vector<Fr>{return copy(copy(xs));}
math fn read(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(twice(xs),i);}
)"));
  });
  cases.run("result extents retain actual argument permutation", [&] {
    take(check(collections + R"(
math fn second(a:Vector<Fr>,b:Vector<Fr>)->Vector<Fr>{return copy(b);}
math fn read(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(second(ys,xs),i);}
)"));
    refuses(check(collections + R"(
math fn second(a:Vector<Fr>,b:Vector<Fr>)->Vector<Fr>{return copy(b);}
math fn read(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(second(xs,ys),i);}
)"),
            "source.data-bound");
  });
  cases.run("returned record projections preserve each extent separately", [&] {
    auto record = collections + R"(
struct Pair{pub left:Vector<Fr>,pub right:Vector<Fr>}
math fn copies(a:Vector<Fr>,b:Vector<Fr>)->Pair{return Pair{left:copy(a),right:copy(b)};}
)";
    take(check(record + R"(
math fn read(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let pair=copies(xs,ys);return at(pair.left,i);}
)"));
    refuses(check(record + R"(
math fn read(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let pair=copies(xs,ys);return at(pair.right,i);}
)"),
            "source.data-bound");
  });
  cases.run("separate calls do not share result extent evidence", [&] {
    refuses(check(collections + R"(
math fn read(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){
 let first=copy(xs);let second=copy(ys);return at(second,i);}
)"),
            "source.data-bound");
  });
  cases.run("fixed array input supplies helper result cardinality", [&] {
    take(check(collections + R"(
math fn from_array(xs:Array<Fr,2>)->Vector<Fr>{return mapped(array_elements(xs),fn(x)=>x);}
math fn read(xs:Array<Fr,2>)->Fr{return at(from_array(xs),1);}
)"));
    refuses(check(collections + R"(
math fn from_array(xs:Array<Fr,2>)->Vector<Fr>{return mapped(array_elements(xs),fn(x)=>x);}
math fn read(xs:Array<Fr,2>)->Fr{return at(from_array(xs),2);}
)"),
            "source.data-bound");
  });
  cases.run("filtered helper results never acquire the source exact extent",
            [&] {
              refuses(check(collections + R"(
math fn select(xs:Vector<Fr>)->Vector<Fr>{return filtered(elements(xs),fn(x)=>false,fn(x)=>x);}
math fn read(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(select(xs),i);}
)"),
                      "source.data-bound");
            });
  cases.run("helper result evidence survives closed specialization", [&] {
    auto project = take(check(collections + R"(
math fn read(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(copy(xs),i);}
math fn work(xs:Vector<Fr>)->Fr{return total(indices(xs),0,fn(s,i)=>s+read(xs,i));}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return work(xs);}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
    auto closed = take(zkc::test::closeProtocolDeployment(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("captured result facts remain available after callback scope", [&] {
    auto project = take(check(collections + R"(
struct Pair{pub left:Vector<Fr>,pub right:Vector<Fr>}
math fn copies(a:Vector<Fr>,b:Vector<Fr>)->Pair{return Pair{left:copy(a),right:copy(b)};}
math fn read(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){
 let pair=copies(xs,ys);let l=pair.left;
 let subtotal=total(indices(xs),0,fn(st,j)=>st+at(l,j));
 return subtotal+at(l,i);
}
math fn work(xs:Vector<Fr>)->Fr{return total(indices(xs),0,fn(st,i)=>st+read(xs,xs,i));}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return work(xs);}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
    auto closed = take(zkc::test::closeProtocolDeployment(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("record fields retain origins across callback captures", [&] {
    auto project = take(check(collections + R"(
struct Pair{pub left:Vector<Fr>,pub right:Vector<Fr>}
math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{
 let p=Pair{left:copy(xs),right:copy(ys)};
 return total(indices(xs),0,fn(st,j)=>st+at(p.left,j));
}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P)->(r:Fr@P){return work(xs,ys);}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
    auto closed = take(zkc::test::closeProtocolDeployment(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("sequential helper result chains use work rather than call depth",
            [&] {
              std::string chain =
                  collections + "math fn chain(xs:Vector<Fr>)->Vector<Fr>{";
              std::string previous = "xs";
              for (unsigned i = 0; i < 256; ++i) {
                auto current = "v" + std::to_string(i);
                chain += "let " + current + "=copy(" + previous + ");";
                previous = current;
              }
              chain += "return " + previous + ";}";
              take(check(chain + R"(
math fn read(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(chain(xs),i);}
)"));
            });
  cases.run(
      "result dependency traversal handles thousands of admitted SSA links",
      [&] {
        auto project = take(check(collections + R"(
math fn chain(xs:Vector<Fr>)->Vector<Fr>{return copy(xs);}
)"));
        Environment env;
        env.declarations = project.declarations().vec();
        auto index = named(project, "chain").id.index;
        auto storage = std::make_shared<Body>(*env.declarations[index].body);
        auto &body = *storage;
        env.declarations[index].body = storage;
        auto prototype = body.operations.front();
        for (const auto &op : body.operations)
          if (std::holds_alternative<HelperCall>(op.action))
            prototype = op;
        auto resultType = body.values[prototype.results.front().index];
        body.operations.clear();
        body.values.resize(1);
        ValueId previous{0};
        for (unsigned i = 0; i < 4096; ++i) {
          auto op = prototype;
          std::get<HelperCall>(op.action).operands = {previous};
          previous = {static_cast<unsigned>(body.values.size())};
          op.results = {previous};
          body.values.push_back(resultType);
          body.operations.push_back(std::move(op));
        }
        body.results = {previous};
        source::HelperResults results(env.semantics, env.declarations);
        const auto *result = results.get(index, 0, {}, {});
        require(result && result->shape.input == source::ValueOrigin{0, {}},
                "iterative result analysis lost the original extent");
        require(env.work.used < 1000000,
                "linear chain repeated result analysis");
      });
  cases.run("domain result facts survive direct and nested wrappers", [&] {
    take(check(collections + R"(
math fn wrap<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item,rows))->Vector<Fr>{return mapped(rows,body);}
math fn outer(xs:Vector<Fr>)->Vector<Fr>{return wrap(indices(xs),fn(i)=>0);}
math fn direct(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(wrap(indices(xs),fn(j)=>0),i);}
math fn nested(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(outer(xs),i);}
)"));
    refuses(check(collections + R"(
math fn wrap<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item,rows))->Vector<Fr>{return filtered(rows,fn(i)=>false,body);}
math fn read(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return at(wrap(indices(xs),fn(j)=>0),i);}
)"),
            "source.data-bound");
  });
  cases.run("local and returned records respect declared field order", [&] {
    std::string records = collections + R"(
struct Pair{pub left:Vector<Fr>,pub right:Vector<Fr>}
math fn copies(a:Vector<Fr>,b:Vector<Fr>)->Pair{return Pair{right:copy(b),left:copy(a)};}
math fn returned(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let p=copies(xs,ys);return at(p.left,i);}
math fn local(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let p=Pair{right:copy(ys),left:copy(xs)};return at(p.left,i);}
)";
    take(check(records));
    refuses(check(records + R"(
math fn wrong(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let p=Pair{right:copy(ys),left:copy(xs)};return at(p.right,i);}
)"),
            "source.data-bound");
  });
  cases.run("source fact scopes preserve full paths and isolate branches", [] {
    Environment environment;
    source::MathematicalFacts adapter(environment.semantics);
    source::ValueOrigin index{1, {0, 1}}, container{2, {1, 0}};
    source::SourceDataFact bound{DataPrecondition::Kind::IndexBound, index,
                                 container};
    auto parent = adapter.scope();
    proven(adapter.enter({}));
    proven(adapter.assume(bound, {}));
    proven(adapter.prove(bound, {}));
    auto sibling = bound;
    sibling.left.second = {1, 0};
    require(adapter.prove(sibling, {}) == facts::Status::Unknown,
            "projection path collapsed");
    adapter.restore(parent);
    proven(adapter.enter({}));
    require(adapter.prove(bound, {}) == facts::Status::Unknown,
            "one branch's bound escaped its scope");
  });
  cases.run("equal source shapes never identify scalar values", [] {
    Environment environment;
    source::MathematicalFacts adapter(environment.semantics);
    source::ValueOrigin a{1, {}}, b{2, {}}, i{3, {}}, j{4, {}};
    auto type = arrayType(Natural::constant(5));
    proven(adapter.record(a, type, {}));
    proven(adapter.record(b, type, {}));
    proven(adapter.constant(i, 4, {}));
    proven(adapter.prove({DataPrecondition::Kind::EqualExtent, a, b}, {}));
    proven(adapter.prove({DataPrecondition::Kind::IndexBound, i, b}, {}));
    require(adapter.prove({DataPrecondition::Kind::IndexBound, j, b}, {}) ==
                facts::Status::Unknown,
            "shape evidence identified indices");
  });
  cases.run(
      "symbolic source naturals do not become runtime ui64 constants", [] {
        Environment environment;
        source::MathematicalFacts adapter(environment.semantics);
        source::ValueOrigin a{1, {}}, b{2, {}}, i{3, {}};
        auto type = arrayType(take(Natural::atom("N")));
        proven(adapter.record(a, type, {}));
        proven(adapter.record(b, type, {}));
        proven(adapter.prove({DataPrecondition::Kind::EqualExtent, a, b}, {}));
        proven(adapter.constant(i, std::numeric_limits<uint64_t>::max(), {}));
        require(adapter.prove({DataPrecondition::Kind::IndexBound, i, b}, {}) ==
                    facts::Status::Unknown,
                "symbolic dimension acquired a numeric bound");
      });
  cases.run(
      "nested queries consume the source work allowance with sticky capacity",
      [] {
        Environment environment;
        source::MathematicalFacts adapter(environment.semantics);
        source::SourceDataFact equal{
            DataPrecondition::Kind::EqualExtent, {1, {}}, {2, {}}};
        proven(adapter.assume(equal, {}));
        auto used = environment.work.used;
        proven(adapter.enter({}));
        proven(adapter.prove(equal, {}));
        require(environment.work.used > used,
                "nested query did not debit source work");
        environment.work.used = environment.limits.work;
        require(adapter.prove(equal, {}) == facts::Status::Capacity,
                "exhaustion used known evidence");
        require(environment.semantics.diagnostic &&
                    environment.semantics.diagnostic->code == "source.limit",
                "capacity lost the source diagnostic");
        require(adapter.prove(equal, {}) == facts::Status::Capacity,
                "nested query renewed its allowance");
      });
  cases.run("absence may infer a precondition but exhaustion cannot", [] {
    auto project = take(check(""));
    auto helper = named(project, "at");
    helper.dataPreconditions.clear();
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    Limits limits;
    source::Work work{limits};
    source::Semantics semantics(declarations, {}, work);
    auto requirements = source::deriveDataPreconditions(
        semantics, declarations, helper, *helper.body, true);
    require(requirements && requirements->size() == 1,
            "missing evidence did not infer the permitted input condition");
    auto requiredWork = work.used;
    source::Work limited{limits};
    limited.used = limits.work - requiredWork + 1;
    source::Semantics exhausted(declarations, {}, limited);
    require(!source::deriveDataPreconditions(exhausted, declarations, helper,
                                             *helper.body, true),
            "exhaustion returned a mathematical precondition");
    require(exhausted.diagnostic &&
                exhausted.diagnostic->code == "source.limit",
            "exhaustion became an absent-evidence diagnostic");
  });
  for (bool zero : {false, true})
    cases.run(
        zero ? "zero cardinality survives an overflowing sibling product"
             : "overflowing product cannot establish a wrapped collection size",
        [&] {
          Environment environment;
          auto shape = std::make_shared<DomainShape>();
          DomainBinding range{};
          range.kind = DomainBinding::Kind::Range;
          range.operands = {{0}, {1}};
          shape->nodes.push_back(range);
          range.operands = {{0}, {2}};
          shape->nodes.push_back(range);
          DomainBinding product{};
          product.kind = DomainBinding::Kind::Product;
          product.children = {0, 1};
          shape->nodes.push_back(product);
          if (zero) {
            range.operands = {{0}, {0}};
            shape->nodes.push_back(range);
            product.children = {2, 3};
            shape->nodes.push_back(product);
          }
          shape->result = shape->nodes.size() - 1;
          FiniteComputation finite{};
          finite.kind = FiniteApplication::Kind::Collect;
          finite.domain = shape;
          auto constant = [](ValueId id) -> std::optional<uint64_t> {
            return id.index == 0   ? 0
                   : id.index == 1 ? std::numeric_limits<uint64_t>::max()
                                   : 2;
          };
          auto extent = [](ValueId, unsigned) -> std::optional<uint64_t> {
            return {};
          };
          auto same = [](ValueId a, ValueId b) { return a.index == b.index; };
          auto equal = [](ValueId, unsigned, ValueId, unsigned) {
            return false;
          };
          auto bound = [](ValueId, ValueId, unsigned) { return false; };
          auto result = arrayType(Natural::constant(
              zero ? 0 : std::numeric_limits<uint64_t>::max() - 1));
          auto accepted = source::checkFiniteFormation(
              environment.semantics, finite, result, true, {},
              {constant, extent, same, equal, bound});
          require(accepted == zero,
                  "source formation used wrapping cardinality arithmetic");
          if (!zero)
            require(environment.semantics.diagnostic &&
                        environment.semantics.diagnostic->code ==
                            "source.data-bound",
                    "overflow refusal lost source.data-bound");
        });
  return cases.result();
}
