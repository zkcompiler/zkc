#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Relation/Formula.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Translation/Language.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
constexpr StringLiteral braces = R"(
module m;
domain F=field("bls12-381.fr");
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Oracle<K:OracleKind>=builtin("oracle",K);
type Vector<T:Field>=builtin("vector",T);
math fn length<T:Field>(data:Vector<T>)->index=primitive("vector.length");
math fn mapped(position:index,mask:index)->index=primitive("index.bit_and");
math fn combine<T:Field>(a:T,b:T,flag:bool)->T {
  return a+b;
}
#[shape(left.rows,bound=Max)]
#[shape(right.rows,bound=Max)]
#[shape(result.rows,value=rows,bound=Max)]
oracle def Select<T:Field,Max:nat>(left:Oracle<Table<T>>,right:Oracle<Table<T>>,
    padding:(index,(index,())),rows:index,mask:index,flag:bool)
    ->Oracle<Table<T>> {
  requires left_rows: oracle.rows(left)==rows;
  requires right_data: length<T>(oracle.data(right))==rows;
  query(position:index) {
    let unused <- oracle.query(left,position);
    let first <- oracle.query(left,position);
    let offset=mapped(position,mask);
    let second <- oracle.query(right,offset);
    return combine<T>(first,second,flag);
  }
}
oracle def Dormant(source:Oracle<Fixed<F,16>>,capture:index)
    ->Oracle<Fixed<F,16>> {
  requires rows: oracle.rows(source)==capture;
  query(position:index) {
    let unused <- oracle.query(source,position);
    let answer <- oracle.query(source,position);
    return answer;
  }
}
oracle def Open<T:Field>(source:Oracle<Fixed<T,16>>)->Oracle<Fixed<T,16>> {
  query(position:index) {
    let answer <- oracle.query(source,position);
    return answer;
  }
}
protocol Run roles(P,V)(left:Oracle<Fixed<F,16>>@P->V,
    right:Oracle<Fixed<F,16>>@P->V,padding:(index,(index,()))@(P,V),
    mask:index@(P,V),flag:bool@(P,V),position:index@V)->(answer:F@V) {
  let a=oracle.forget_rows(left);
  let b=oracle.forget_rows(right);
  let rows=oracle.rows(a);
  let selected <- Select<F,32>(a,b,padding,rows,mask,flag);
  let unused <- Select<F,32>(b,a,padding,rows,mask,flag);
  let answer@V <- query selected at position;
  return(answer=answer);
}
)";

constexpr StringLiteral layout = R"(
module m
domain F = field("bls12-381.fr")
type Table<T: Type + Copy + Drop> = builtin("oracle.table", T)
type Fixed<T: Type + Copy + Drop, N: nat> = builtin("oracle.table", T, N)
type Oracle<K: OracleKind> = builtin("oracle", K)
type Vector<T: Field> = builtin("vector", T)
def mapped(position: index, mask: index) -> index:
    mask
def combine<T: Field>(a: T, b: T, flag: bool) -> T:
    a + b

#[shape(left.rows, bound = Max)]
#[shape(right.rows, bound = Max)]
#[shape(result.rows, value = rows, bound = Max)]
oracle def Select<T: Field, Max: nat>(left: Oracle<Table<T>>, right: Oracle<Table<T>>, padding: (index, (index, ())), rows: index, mask: index, flag: bool) -> Oracle<Table<T>>:
    requires left_rows: oracle.rows(left) == rows
    requires right_rows: oracle.rows(right) == rows
    query(position: index):
        unused <- oracle.query(left, position)
        first <- oracle.query(left, position)
        offset = mapped(position, mask)
        second <- oracle.query(right, offset)
        return combine<T>(first, second, flag)

oracle def Dormant(source: Oracle<Fixed<F, 16>>, capture: index) -> Oracle<Fixed<F, 16>>:
    requires rows: oracle.rows(source) == capture
    query(position: index):
        unused <- oracle.query(source, position)
        answer <- oracle.query(source, position)
        return answer

oracle def Open<T: Field>(source: Oracle<Fixed<T, 16>>) -> Oracle<Fixed<T, 16>>:
    query(position: index):
        answer <- oracle.query(source, position)
        return answer

protocol Run roles(P, V)(left: Oracle<Fixed<F, 16>> @P -> V; right: Oracle<Fixed<F, 16>> @P -> V; padding: (index, (index, ())) @(P, V); mask: index @(P, V); flag: bool @(P, V); position: index @V) -> F @V:
    a = oracle.forget_rows(left)
    b = oracle.forget_rows(right)
    rows = oracle.rows(a)
    selected <- Select<F, 32>(a, b, padding, rows, mask, flag)
    unused <- Select<F, 32>(b, a, padding, rows, mask, flag)
    answer <- oracle.query(selected, position)
    return answer
)";

Expected<CheckedProject> check(StringRef text, StringRef format = "zkc") {
  CaptureOptions options;
  options.format = format.str();
  auto captured =
      capture({{"m", text.str(), "virtual-translation.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  auto analysis = analyze(*captured);
  auto project = analysis.checkedProject();
  if (!project) {
    consumeError(project.takeError());
    return createStringError(
        inconvertibleErrorCode(),
        formatDiagnostics(analysis.diagnostics(), analysis.sources()));
  }
  return project;
}
struct Fixture {
  ClosedEntry entry;
  CheckedOriginal original;
  explicit Fixture(StringRef source, StringRef format)
      : entry(take(closeNativeRun(take(check(source, format)), "m::Run"))),
        original(take(prepareOriginal(entry))) {}
  const Declaration &definition(StringRef name) const {
    for (const auto &decl : entry.declarations())
      if (decl.kind == Declaration::Kind::Oracle && decl.parameters.empty() &&
          decl.name == name)
        return decl;
    throw std::runtime_error("missing retained closed oracle: " + name.str());
  }
};
pir::ProtocolModuleOp unit(mlir::ModuleOp module) {
  return mlir::cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
pir::OracleDefinitionOp definition(mlir::ModuleOp module,
                                   const Declaration &decl) {
  return mlir::SymbolTable(unit(module))
      .lookup<pir::OracleDefinitionOp>(decl.symbol);
}
SmallVector<pir::OracleQueryOp> queries(pir::OracleDefinitionOp definition) {
  SmallVector<pir::OracleQueryOp> result;
  for (auto query : definition.getBody().front().getOps<pir::OracleQueryOp>())
    result.push_back(query);
  return result;
}
SmallVector<pir::OracleVirtualOp> constructions(mlir::ModuleOp module) {
  SmallVector<pir::OracleVirtualOp> result;
  module.walk([&](pir::OracleVirtualOp op) { result.push_back(op); });
  return result;
}
// Keep a mutated predicate's native identity internally consistent. Comparison
// must still refuse its actual body against the checked source.
void refreshPredicates(const Fixture &fixture, mlir::ModuleOp module) {
  uint64_t remaining = 8000000;
  Layouts layouts(fixture.entry);
  LayoutIdentities schemas(remaining);
  relation::FormulaIdentities formulas(remaining, 16777216);
  mlir::SymbolTable symbols(unit(module));
  for (const auto &decl : fixture.entry.declarations()) {
    if (!decl.relation || !decl.origin || !decl.body ||
        decl.relation->kind != RelationDefinition::Kind::Formula)
      continue;
    auto native = symbols.lookup<relation::DeclareOp>(decl.symbol);
    auto helper = symbols.lookup<mlir::func::FuncOp>(formulaSymbol(decl));
    if (!native || !helper)
      continue;
    std::vector<std::string> types, purposes;
    for (unsigned i = 0; i < decl.inputs.size(); ++i) {
      types.push_back(
          take(schemas.get(*take(layouts.get(decl.inputs[i].type)))));
      purposes.push_back(
          decl.relation->purposes[i] == RelationPurpose::Parameter ? "parameter"
          : decl.relation->purposes[i] == RelationPurpose::Statement
              ? "statement"
              : "witness");
    }
    native->setAttr(
        "revision",
        mlir::StringAttr::get(module.getContext(),
                              take(formulas.get(helper, types, purposes))));
  }
}
void mutation(const Fixture &fixture, mlir::MLIRContext &context,
              function_ref<void(mlir::ModuleOp)> change,
              StringRef diagnostic = "source.correspondence") {
  auto module = mlir::parseSourceString<mlir::ModuleOp>(
      fixture.original.bytes(), &context);
  require(bool(module), "original did not parse");
  change(*module);
  if (diagnostic == "source.correspondence") {
    require(succeeded(mlir::verify(*module)),
            "mutation lost native verification");
    require(succeeded(admitStage(*module)),
            "mutation lost mathematical admission");
  }
  refuses(compareOriginal(fixture.entry, *module), diagnostic);
}
void roundTrip(const Fixture &fixture, mlir::MLIRContext &context) {
  auto module = mlir::parseSourceString<mlir::ModuleOp>(
      fixture.original.bytes(), &context);
  require(bool(module) && succeeded(mlir::verify(*module)) &&
              succeeded(admitStage(*module)),
          "source original failed native admission");
  take(compareOriginal(fixture.entry, *module));
  const auto &closed = fixture.definition("Select");
  auto actual = definition(*module, closed);
  require(actual && actual.getNumSources() == 2 &&
              actual.getFunctionType().getNumInputs() == 8 &&
              actual.getFunctionType().getNumResults() == 1,
          "query signature was confused with the constructor ABI");
  auto shape = actual.getShapeArguments().getAs<mlir::IntegerAttr>("rows");
  auto bound = actual.getShapeBounds().getAs<mlir::IntegerAttr>("rows");
  require(shape && shape.getValue().getZExtValue() == 4 && bound &&
              bound.getValue().getZExtValue() == 32,
          "shape capture ignored nested/empty capture flattening");
  require(closed.oracleDefinition->sourceBounds.size() == 2 &&
              closed.oracleDefinition->predicates.size() == 2,
          "source formation bounds or authored predicate clauses disappeared");
  const auto &predicate =
      fixture.entry
          .declarations()[closed.oracleDefinition->admissibility.index];
  auto helper = mlir::SymbolTable(unit(*module))
                    .lookup<mlir::func::FuncOp>(formulaSymbol(predicate));
  require(bool(helper), "generated predicate helper disappeared");
  unsigned sourceBounds = 0;
  helper.walk([&](data::LessOp op) {
    auto maximum = op.getRhs().getDefiningOp<data::IndexOp>();
    require(maximum && maximum.getValue() == 32,
            "source bound did not survive predicate specialization");
    ++sourceBounds;
  });
  require(sourceBounds == 2,
          "generated predicate lost a source-bound conjunct");
  unsigned dimensions = 0;
  module->walk([&](data::DimOp) { ++dimensions; });
  require(
      dimensions >= 2 && queries(actual).size() == 3 &&
          queries(definition(*module, fixture.definition("Dormant"))).size() ==
              2 &&
          constructions(*module).size() == 2,
      "source data predicates or unused/repeated occurrences disappeared");
  for (auto query : queries(actual))
    require(!query.getOwnerAttr(), "role-free source query acquired an owner");
  for (const auto &decl : fixture.entry.declarations())
    if (decl.kind == Declaration::Kind::Oracle && !decl.parameters.empty())
      require(!mlir::SymbolTable(unit(*module)).lookup(decl.symbol),
              "open generic template acquired a monomorphic body");
  module->walk([&](mlir::Operation *op) {
    op->setLoc(mlir::UnknownLoc::get(&context));
  });
  take(compareOriginal(fixture.entry, *module));
}
} // namespace

int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  mlir::ScopedDiagnosticHandler quiet(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  std::optional<Fixture> fixture;
  cases.run("checked virtual source reaches independent native comparison",
            [&] {
              fixture.emplace(braces, "zkc");
              roundTrip(*fixture, context);
            });
  cases.run("explicit layout retains metadata and ordered occurrences",
            [&] { roundTrip(Fixture(layout, "zkc-layout"), context); });
  auto test = [&](StringRef name,
                  function_ref<void(const Fixture &, mlir::ModuleOp)> change,
                  StringRef diagnostic = "source.correspondence") {
    cases.run(name, [&] {
      require(fixture.has_value(), "brace fixture did not close");
      mutation(
          *fixture, context,
          [&](mlir::ModuleOp module) { change(*fixture, module); }, diagnostic);
    });
  };
  test("source query must select its exact source block argument",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto d = definition(m, f.definition("Select"));
         queries(d)[0]->setOperand(0, d.getBody().front().getArgument(1));
       });
  test("source query must retain its actual position",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto d = definition(m, f.definition("Select"));
         queries(d)[0]->setOperand(1, d.getBody().front().getArgument(5));
       });
  test("unused source queries cannot be dropped",
       [](const Fixture &f, mlir::ModuleOp m) {
         queries(definition(m, f.definition("Select")))[0].erase();
       });
  test("repeated source queries cannot be reordered",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto q = queries(definition(m, f.definition("Select")));
         q[1]->moveBefore(q[0]);
       });
  test("extra unused queries cannot be hidden", [](const Fixture &f,
                                                   mlir::ModuleOp m) {
    auto q = queries(definition(m, f.definition("Select")))[0];
    auto *extra = q->clone();
    extra->setAttr("site", mlir::StringAttr::get(m.getContext(), "additional"));
    mlir::OpBuilder(q).insert(extra);
  });
  test("source query sites cannot be substituted",
       [](const Fixture &f, mlir::ModuleOp m) {
         queries(definition(m, f.definition("Select")))[0]->setAttr(
             "site", mlir::StringAttr::get(m.getContext(), "changed"));
       });
  test("construction must retain actual source operands",
       [](const Fixture &, mlir::ModuleOp m) {
         auto c = constructions(m)[0];
         c->setOperand(0, c->getOperand(1));
       });
  test("construction must retain nested capture operands",
       [](const Fixture &, mlir::ModuleOp m) {
         auto c = constructions(m)[0];
         c->setOperand(2, c->getOperand(3));
       });
  test("construction must retain its actual shape operand",
       [](const Fixture &, mlir::ModuleOp m) {
         auto c = constructions(m)[0];
         c->setOperand(4, c->getOperand(5));
       });
  test("unused construction allocations cannot be dropped",
       [](const Fixture &, mlir::ModuleOp m) { constructions(m)[1].erase(); });
  test("construction allocations cannot be reordered",
       [](const Fixture &, mlir::ModuleOp m) {
         auto c = constructions(m);
         c[1]->moveBefore(c[0]);
       });
  test("construction closed callee cannot be substituted",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto d = definition(m, f.definition("Select"));
         auto *other = d->clone();
         other->setAttr("sym_name",
                        mlir::StringAttr::get(m.getContext(), "other_closed"));
         mlir::OpBuilder builder(m.getContext());
         builder.setInsertionPointToEnd(&unit(m).getBody().front());
         builder.insert(other);
         constructions(m)[0]->setAttr(
             "callee",
             mlir::FlatSymbolRefAttr::get(m.getContext(), "other_closed"));
       });
  for (StringRef name : {"shape_arguments", "shape_bounds"})
    test(("definition must retain " + name).str(), [=](const Fixture &f,
                                                       mlir::ModuleOp m) {
      auto d = definition(m, f.definition("Select"));
      mlir::OpBuilder b(m.getContext());
      auto value =
          b.getIntegerAttr(mlir::IntegerType::get(m.getContext(), 64,
                                                  mlir::IntegerType::Unsigned),
                           name == "shape_arguments" ? 5 : 31);
      d->setAttr(name, b.getDictionaryAttr({b.getNamedAttr("rows", value)}));
    });
  test("unused closed definitions cannot be changed",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto d = definition(m, f.definition("Dormant"));
         queries(d)[0]->setOperand(1, d.getBody().front().getArgument(1));
       });
  test("unused closed definitions cannot be omitted",
       [](const Fixture &f, mlir::ModuleOp m) {
         definition(m, f.definition("Dormant")).erase();
       });
  test("dormant answer must preserve the selected query result",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto d = definition(m, f.definition("Dormant"));
         d.getBody().front().back().setOperand(0, queries(d)[0].getAnswer());
       });
  test("unused total work cannot be hidden in a dormant body",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto d = definition(m, f.definition("Dormant"));
         mlir::OpBuilder builder(&d.getBody().front().back());
         mlir::arith::ConstantOp::create(builder, d.getLoc(),
                                         builder.getBoolAttr(true));
       });
  test("query helper body must match actual checked mathematics",
       [](const Fixture &, mlir::ModuleOp m) {
         bool changed = false;
         m.walk([&](data::IndexBitAndOp op) {
           if (!changed) {
             require(op->getOperand(0) != op->getOperand(1),
                     "helper mutation must change an operand");
             op->setOperand(1, op->getOperand(0));
             changed = true;
           }
         });
         require(changed, "closed query helper was not retained");
       });
  test("extra unused closed definitions cannot be introduced",
       [](const Fixture &f, mlir::ModuleOp m) {
         auto d = definition(m, f.definition("Dormant"));
         auto *extra = d->clone();
         extra->setAttr("sym_name",
                        mlir::StringAttr::get(m.getContext(), "extra_closed"));
         mlir::OpBuilder(d).insert(extra);
       });
  test("actual predicate source data cannot be substituted",
       [](const Fixture &f, mlir::ModuleOp m) {
         const auto &d = f.definition("Select");
         const auto &p =
             f.entry.declarations()[d.oracleDefinition->admissibility.index];
         auto helper = mlir::SymbolTable(unit(m)).lookup<mlir::func::FuncOp>(
             formulaSymbol(p));
         bool changed = false;
         helper.walk([&](data::DimOp op) {
           if (!changed) {
             op->setOperand(0, helper.front().getArgument(1));
             changed = true;
           }
         });
         require(changed,
                 "source rows predicate had no actual data dimension read");
         refreshPredicates(f, m);
       });
  test("dormant predicate body cannot hide behind an updated identity",
       [](const Fixture &f, mlir::ModuleOp m) {
         const auto &p =
             f.entry.declarations()[f.definition("Dormant")
                                        .oracleDefinition->admissibility.index];
         auto helper = mlir::SymbolTable(unit(m)).lookup<mlir::func::FuncOp>(
             formulaSymbol(p));
         auto *ret = &helper.front().back();
         mlir::OpBuilder b(ret);
         auto truth = mlir::arith::ConstantOp::create(b, ret->getLoc(),
                                                      b.getBoolAttr(true));
         ret->setOperand(0, truth.getResult());
         refreshPredicates(f, m);
       });
  test("every authored predicate conjunct must remain in the actual helper",
       [](const Fixture &f, mlir::ModuleOp m) {
         const auto &p =
             f.entry.declarations()[f.definition("Select")
                                        .oracleDefinition->admissibility.index];
         auto helper = mlir::SymbolTable(unit(m)).lookup<mlir::func::FuncOp>(
             formulaSymbol(p));
         auto conjunction = helper.front()
                                .back()
                                .getOperand(0)
                                .getDefiningOp<mlir::arith::AndIOp>();
         // Source bounds follow the authored conjunction in source order.
         for (unsigned i = 0;
              i < f.definition("Select").oracleDefinition->sourceBounds.size();
              ++i) {
           require(bool(conjunction), "missing source-bound conjunction");
           conjunction =
               conjunction.getLhs().getDefiningOp<mlir::arith::AndIOp>();
         }
         require(conjunction && conjunction.getLhs() != conjunction.getRhs(),
                 "generated predicate lost its authored conjunction");
         conjunction->setOperand(1, conjunction.getLhs());
         refreshPredicates(f, m);
       });
  for (unsigned source = 0; source < 2; ++source)
    test(("each declared source bound must remain an actual predicate "
          "conjunct " +
          Twine(source))
             .str(),
         [=](const Fixture &f, mlir::ModuleOp m) {
           const auto &p =
               f.entry
                   .declarations()[f.definition("Select")
                                       .oracleDefinition->admissibility.index];
           auto helper = mlir::SymbolTable(unit(m)).lookup<mlir::func::FuncOp>(
               formulaSymbol(p));
           auto conjunction = helper.front()
                                  .back()
                                  .getOperand(0)
                                  .getDefiningOp<mlir::arith::AndIOp>();
           if (source == 0) {
             require(bool(conjunction), "missing second source-bound conjunct");
             conjunction =
                 conjunction.getLhs().getDefiningOp<mlir::arith::AndIOp>();
           }
           require(
               conjunction &&
                   conjunction.getRhs().getDefiningOp<mlir::arith::OrIOp>() &&
                   conjunction.getLhs() != conjunction.getRhs(),
               "source bound has no distinct <= predicate conjunct");
           conjunction->setOperand(1, conjunction.getLhs());
           refreshPredicates(f, m);
         });
  test("unused generated predicates cannot be omitted",
       [](const Fixture &f, mlir::ModuleOp m) {
         const auto &p =
             f.entry.declarations()[f.definition("Dormant")
                                        .oracleDefinition->admissibility.index];
         mlir::SymbolTable symbols(unit(m));
         auto *predicate = symbols.lookup(p.symbol);
         auto *replacement = predicate->clone();
         replacement->setAttr(
             "sym_name",
             mlir::StringAttr::get(m.getContext(), "replacement_predicate"));
         mlir::OpBuilder(predicate).insert(replacement);
         definition(m, f.definition("Dormant"))
             ->setAttr("admissibility",
                       mlir::FlatSymbolRefAttr::get(m.getContext(),
                                                    "replacement_predicate"));
         predicate->erase();
       });
  test(
      "unused predicate helpers cannot be omitted",
      [](const Fixture &f, mlir::ModuleOp m) {
        const auto &p =
            f.entry.declarations()[f.definition("Dormant")
                                       .oracleDefinition->admissibility.index];
        mlir::SymbolTable(unit(m)).lookup(formulaSymbol(p))->erase();
      },
      "target.admission");
  test("extra unused predicates cannot be introduced",
       [](const Fixture &f, mlir::ModuleOp m) {
         const auto &p =
             f.entry.declarations()[f.definition("Dormant")
                                        .oracleDefinition->admissibility.index];
         auto declaration =
             mlir::SymbolTable(unit(m)).lookup<relation::DeclareOp>(p.symbol);
         auto *extra = declaration->clone();
         extra->setAttr("sym_name", mlir::StringAttr::get(m.getContext(),
                                                          "extra_predicate"));
         mlir::OpBuilder(declaration).insert(extra);
       });
  test(
      "partial mathematics cannot be hidden inside a virtual body",
      [](const Fixture &f, mlir::ModuleOp m) {
        auto d = definition(m, f.definition("Select"));
        auto &body = d.getBody().front();
        mlir::OpBuilder b(&body.back());
        mlir::OperationState state(d.getLoc(), "arith.divui");
        state.addOperands({body.getArgument(4), body.getArgument(5)});
        state.addTypes(body.getArgument(4).getType());
        b.create(state);
      },
      "target.admission");
  test(
      "construction holder cannot be changed",
      [](const Fixture &, mlir::ModuleOp m) {
        constructions(m)[0]->setAttr(
            "holder", mlir::StringAttr::get(m.getContext(), nativeRoleName(1)));
      },
      "target.admission");
  test(
      "construction receivers cannot be changed",
      [](const Fixture &, mlir::ModuleOp m) {
        mlir::OpBuilder b(m.getContext());
        constructions(m)[0]->setAttr("receivers",
                                     b.getStrArrayAttr({nativeRoleName(0)}));
      },
      "target.admission");
  cases.run("zero-source policy is explicit and one source is supported", [&] {
    refuses(check(R"(module m;
domain F=field("bls12-381.fr");
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Oracle<K:OracleKind>=builtin("oracle",K);
oracle def Zero(value:F)->Oracle<Fixed<F,16>> {
  query(position:index) { return value; }
})"),
            "source.oracle-signature");
    require(fixture.has_value(), "brace fixture did not close");
    require(fixture->definition("Dormant").oracleDefinition->sourceCount == 1,
            "single direct source was not supported");
  });
  cases.run("virtual correspondence retains the comparison operation ceiling",
            [&] {
              require(fixture.has_value(), "brace fixture did not close");
              auto module = mlir::parseSourceString<mlir::ModuleOp>(
                  fixture->original.bytes(), &context);
              require(bool(module), "original did not parse");
              Limits limits;
              limits.operations = 1;
              refuses(compareOriginal(fixture->entry, *module, limits),
                      "source.limit");
            });
  return cases.result();
}
