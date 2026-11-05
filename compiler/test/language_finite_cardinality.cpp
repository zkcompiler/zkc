#include "../lib/Language/FiniteFormation.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Project.h"
#include <map>
using namespace zkc::language;
using namespace zkc::test;
namespace source = zkc::language::detail;
namespace {
Type arrayType(uint64_t size, bool native = true) {
  Type result(native ? Type::Kind::Builtin : Type::Kind::Array);
  Type field(Type::Kind::Field);
  if (native) {
    result.domain = "field_array";
    Type dimension(Type::Kind::Natural);
    dimension.dimension = Natural::constant(size);
    result.arguments = {field, dimension};
  } else {
    result.arguments = {field};
    result.dimension = Natural::constant(size);
  }
  return result;
}
struct Formation {
  Limits limits;
  source::Work work{limits};
  std::vector<Declaration> declarations;
  source::Semantics semantics{declarations, {}, work};
  std::shared_ptr<DomainShape> shape = std::make_shared<DomainShape>();
  std::map<unsigned, uint64_t> constants;
  std::map<std::pair<unsigned, unsigned>, uint64_t> extents;
  unsigned equalQueries = 0, boundQueries = 0;
  bool inferEqual = false, allowBound = true, filtered = false;
  enum class Exhaust {
    None,
    Extent,
    Integer,
    Identity,
    Equality
  } exhaust = Exhaust::None;
  unsigned add(DomainBinding::Kind kind, std::vector<ValueId> operands = {},
               std::vector<unsigned> children = {}) {
    DomainBinding node{};
    node.kind = kind;
    node.operands = std::move(operands);
    node.children = std::move(children);
    shape->nodes.push_back(std::move(node));
    shape->result = shape->nodes.size() - 1;
    return shape->result;
  }
  bool check(bool total, std::optional<uint64_t> fixed = {}) {
    FiniteComputation finite{};
    finite.kind = fixed ? FiniteApplication::Kind::Collect
                        : FiniteApplication::Kind::Fold;
    finite.domain = shape;
    if (filtered)
      finite.predicate = FiniteCallback{};
    auto constant = [&](ValueId id) -> std::optional<uint64_t> {
      if (exhaust == Exhaust::Integer) {
        semantics.charge(limits.work + 1, {});
        return {};
      }
      auto it = constants.find(id.index);
      return it == constants.end() ? std::nullopt
                                   : std::optional<uint64_t>(it->second);
    };
    auto extent = [&](ValueId id, unsigned axis) -> std::optional<uint64_t> {
      if (exhaust == Exhaust::Extent) {
        semantics.charge(limits.work + 1, {});
        return {};
      }
      auto it = extents.find({id.index, axis});
      return it == extents.end() ? std::nullopt
                                 : std::optional<uint64_t>(it->second);
    };
    auto same = [&](ValueId a, ValueId b) {
      if (exhaust == Exhaust::Identity)
        return semantics.charge(limits.work + 1, {});
      return a.index == b.index;
    };
    auto equal = [&](ValueId a, unsigned aa, ValueId b, unsigned ba) {
      ++equalQueries;
      if (exhaust == Exhaust::Equality)
        return semantics.charge(limits.work + 1, {});
      return inferEqual || (a.index == b.index && aa == ba);
    };
    auto bound = [&](ValueId, ValueId, unsigned) {
      ++boundQueries;
      return allowBound ||
             semantics.fail("source.data-bound", "missing selector bound", {});
    };
    return source::checkFiniteFormation(
        semantics, finite, fixed ? arrayType(*fixed) : Type{}, total, {},
        {constant, extent, same, equal, bound});
  }
  void refused(const char *code) {
    require(semantics.diagnostic && semantics.diagnostic->code == code,
            "incorrect formation diagnostic");
  }
};
llvm::Expected<ClosedEntry> close(llvm::StringRef body) {
  auto captured = capture({{"sample", body.str(), "cardinality.zkc"}});
  if (!captured)
    return captured.takeError();
  auto checked = analyze(*captured).checkedProject();
  if (!checked)
    return checked.takeError();
  return zkc::test::closeProtocolDeployment(*checked, "sample::Demo");
}
const std::string prelude = R"(module sample;
domain Fr=field("koala-bear");
type Array<F:Field,N:nat>=builtin("field_array",F,N);
fn collect<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:fn(item:I)->Fr effects(stop) where item_from(item,rows))->Array<Fr,N> effects(stop)=finite("local.collect.field_array");
)";
} // namespace
int main() {
  Cases cases;
  for (bool total : {true, false})
    cases.run(total ? "Math fixed range uses exact actual constants"
                    : "Local fixed range cannot use erased actual constants",
              [&] {
                Formation test;
                test.add(DomainBinding::Kind::Range, {{0}, {1}});
                test.constants = {{0, 0}, {1, 2}};
                require(test.check(total, 2) == total,
                        "range formal/actual policy differs");
                if (!total)
                  test.refused("source.data-bound");
              });
  for (bool native : {true, false})
    cases.run(native ? "Local fixed native extent survives declaration lowering"
                     : "Local source array extent is erased to Sequence",
              [&] {
                Formation test;
                test.shape->inputs = {arrayType(2, native)};
                test.add(native ? DomainBinding::Kind::Elements
                                : DomainBinding::Kind::SourceArray,
                         {{0}});
                test.extents = {{{0, 0}, 2}};
                require(test.check(false, 2) == native,
                        "Local extent was not invariant");
                if (!native)
                  test.refused("source.data-bound");
              });
  cases.run("Local dynamic input cannot borrow a known actual extent", [] {
    Formation test;
    Type vector(Type::Kind::Builtin);
    vector.domain = "vector";
    test.shape->inputs = {vector};
    test.add(DomainBinding::Kind::Elements, {{0}});
    test.extents = {{{0, 0}, 2}};
    require(!test.check(false, 2), "Local declaration used actual extent");
    test.refused("source.data-bound");
  });
  cases.run("matrix coordinate count is the product of exact axes", [] {
    Formation test;
    test.add(DomainBinding::Kind::MatrixCoordinates, {{0}});
    test.extents = {{{0, 0}, 3}, {{0, 1}, 5}};
    require(test.check(true, 15), "matrix cardinality remained unknown");
  });
  cases.run("matrix structural equality invokes both formation callbacks", [] {
    Formation test;
    auto a = test.add(DomainBinding::Kind::MatrixCoordinates, {{0}});
    auto b = test.add(DomainBinding::Kind::MatrixCoordinates, {{1}});
    test.add(DomainBinding::Kind::Zip, {}, {a, b});
    test.inferEqual = true;
    require(test.check(true) && test.equalQueries == 2,
            "matrix equality lost an inferred formation obligation");
  });
  cases.run("matching products infer each required extent equality", [] {
    Formation test;
    auto a = test.add(DomainBinding::Kind::Elements, {{0}});
    auto b = test.add(DomainBinding::Kind::Elements, {{1}});
    auto c = test.add(DomainBinding::Kind::Elements, {{2}});
    auto d = test.add(DomainBinding::Kind::Elements, {{3}});
    auto x = test.add(DomainBinding::Kind::Product, {}, {a, c});
    auto y = test.add(DomainBinding::Kind::Product, {}, {b, d});
    test.add(DomainBinding::Kind::Zip, {}, {x, y});
    test.inferEqual = true;
    require(test.check(true) && test.equalQueries == 2,
            "product equality bypassed source precondition inference");
  });
  cases.run("empty product does not erase an earlier strict zip obligation",
            [] {
              Formation test;
              auto a = test.add(DomainBinding::Kind::Elements, {{0}});
              auto b = test.add(DomainBinding::Kind::Elements, {{1}});
              auto zip = test.add(DomainBinding::Kind::Zip, {}, {a, b});
              auto zero = test.add(DomainBinding::Kind::Range, {{2}, {2}});
              test.add(DomainBinding::Kind::Product, {}, {zero, zip});
              test.constants = {{2, 0}};
              test.extents = {{{0, 0}, 2}, {{1, 0}, 3}};
              require(!test.check(true, 0), "empty count erased zip admission");
              test.refused("source.data-bound");
            });
  cases.run("unused matrix selector still requires its bound", [] {
    Formation test;
    test.add(DomainBinding::Kind::MatrixRow, {{0}, {1}});
    test.add(DomainBinding::Kind::Range, {{2}, {2}});
    test.constants = {{2, 0}};
    test.allowBound = false;
    require(!test.check(true, 0) && test.boundQueries == 1,
            "unused selector lost its bound");
    test.refused("source.data-bound");
  });
  cases.run("Local zip keeps runtime admission separate from first count", [] {
    Formation test;
    test.shape->inputs = {arrayType(2), arrayType(3)};
    test.extents = {{{0, 0}, 2}, {{1, 0}, 3}};
    auto a = test.add(DomainBinding::Kind::Elements, {{0}});
    auto b = test.add(DomainBinding::Kind::Elements, {{1}});
    test.add(DomainBinding::Kind::Zip, {}, {a, b});
    require(test.check(false, 2), "Local runtime admission became total proof");
  });
  cases.run(
      "filtered fixed collection is refused even with exact input size", [] {
        Formation test;
        test.add(DomainBinding::Kind::Elements, {{0}});
        test.extents = {{{0, 0}, 2}};
        test.filtered = true;
        require(!test.check(true, 2), "filter was treated as exact count");
        test.refused("source.data-bound");
      });
  cases.run("formation exhaustion retains source.limit", [] {
    Formation test;
    test.add(DomainBinding::Kind::Range, {{0}, {1}});
    test.constants = {{0, 0}, {1, 2}};
    test.work.used = test.limits.work;
    require(!test.check(true, 2), "exhaustion admitted a fixed result");
    test.refused("source.limit");
  });
  for (auto callback :
       {Formation::Exhaust::Extent, Formation::Exhaust::Integer,
        Formation::Exhaust::Identity, Formation::Exhaust::Equality})
    cases.run("leaf callback exhaustion remains capacity " +
                  std::to_string(unsigned(callback)),
              [&] {
                Formation test;
                test.exhaust = callback;
                if (callback == Formation::Exhaust::Extent ||
                    callback == Formation::Exhaust::Integer) {
                  unsigned zero;
                  // A literal zero range can precede an exhausted extent
                  // callback. For integer exhaustion the empty extent supplies
                  // the zero instead.
                  if (callback == Formation::Exhaust::Extent) {
                    zero = test.add(DomainBinding::Kind::Range, {{0}, {0}});
                    test.constants = {{0, 0}};
                  } else {
                    zero = test.add(DomainBinding::Kind::Elements, {{0}});
                    test.extents = {{{0, 0}, 0}};
                  }
                  auto other = test.add(callback == Formation::Exhaust::Extent
                                            ? DomainBinding::Kind::Elements
                                            : DomainBinding::Kind::Range,
                                        callback == Formation::Exhaust::Extent
                                            ? std::vector<ValueId>{{1}}
                                            : std::vector<ValueId>{{1}, {2}});
                  test.add(DomainBinding::Kind::Product, {}, {zero, other});
                  require(!test.check(true, 0), "zero hid callback exhaustion");
                } else {
                  auto kind = callback == Formation::Exhaust::Identity
                                  ? DomainBinding::Kind::Range
                                  : DomainBinding::Kind::Elements;
                  auto a = test.add(kind, kind == DomainBinding::Kind::Range
                                              ? std::vector<ValueId>{{0}, {1}}
                                              : std::vector<ValueId>{{0}});
                  auto b = test.add(kind, kind == DomainBinding::Kind::Range
                                              ? std::vector<ValueId>{{2}, {3}}
                                              : std::vector<ValueId>{{1}});
                  test.add(DomainBinding::Kind::Zip, {}, {a, b});
                  require(!test.check(true),
                          "callback exhaustion admitted equality");
                }
                test.refused("source.limit");
              });
  cases.run("valid Local native field array source closes", [] {
    take(close(prelude + R"(
domain fn elements<F:Field,N:nat>(xs:Array<F,N>)->domain<F>=domain("elements");
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
math fn fixed<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item,rows))->Array<Fr,N>=finite("math.collect.field_array");
math fn make(a:Fr)->Array<Fr,2>{return fixed(array([a,a]),fn(x)=>x);}
fn work(xs:Array<Fr,2>)->Array<Fr,2> effects(stop){return collect(elements(xs),fn(x)=>x);}
protocol Run roles(P)(a:Fr@P)->(r:Array<Fr,2>@P) effects(stop){return work(make(a));}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)"));
  });
  cases.run("Local source array mismatch refuses before IR admission", [] {
    refuses(close(prelude + R"(
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
fn work(a:Fr)->Array<Fr,2> effects(stop){return collect(array([a,a]),fn(x)=>x);}
protocol Run roles(P)(a:Fr@P)->(r:Array<Fr,2>@P) effects(stop){return work(a);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)"),
            "source.data-bound");
  });
  cases.run("valid Local constant range has no declaration-level fixed count",
            [] {
              refuses(close(prelude + R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
fn work(a:Fr)->Array<Fr,2> effects(stop){return collect(range(0,2),fn(i)=>a);}
protocol Run roles(P)(a:Fr@P)->(r:Array<Fr,2>@P) effects(stop){return work(a);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
)"),
                      "source.data-bound");
            });
  return cases.result();
}
