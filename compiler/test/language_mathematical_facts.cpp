#include "../lib/Language/FiniteContracts.h"
#include "../lib/Language/FiniteFormation.h"
#include "../lib/Language/MathematicalFacts.h"
#include "support/NativeCases.h"
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
Expected<CheckedProject> check(StringRef text) {
  auto captured = capture({{"m", prelude + text.str(), "facts.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
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
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return same(xs);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
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
