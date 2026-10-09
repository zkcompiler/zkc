#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
namespace {
template <class T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
Expected<CheckedProject> check(StringRef source) {
  return analyze(take(capture({{"sample", source.str(), "polynomial.zkc"}})))
      .checkedProject();
}
std::string source(StringRef body) {
  return ("module sample;domain F=field(\"bls12-381.fr\");"
          "type Poly<N:nat>=formal(\"polynomial\",F,N);" +
          body)
      .str();
}
mlir::Operation *first(mlir::ModuleOp module, StringRef name) {
  mlir::Operation *found = nullptr;
  module.walk([&](mlir::Operation *op) {
    if (!found && op->getName().getStringRef() == name)
      found = op;
  });
  require(found, "mutation target missing");
  return found;
}
std::string replaceText(StringRef input, StringRef from, StringRef to) {
  auto s = input.str();
  auto at = s.find(from.str());
  require(at != std::string::npos, "fixture edit missing");
  s.replace(at, from.size(), to.str());
  return s;
}
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "expected source fixture");
  auto bytes = MemoryBuffer::getFile(argv[1]);
  require(bool(bytes), "cannot read source fixture");
  auto checked = take(check((*bytes)->getBuffer()));
  zkc::test::Cases cases;
  std::vector<CheckedOriginal> originals;
  for (StringRef name : {"sample::Demo", "sample::LocalDemo"})
    cases.run(name, [&] {
      auto original = take(prepareOriginal(take(closeEntry(checked, name))));
      require(original.bytes().contains("poly.mle"),
              "formal original was erased");
      require(!original.interfaceJson().contains("formal("),
              "formal interface port escaped");
      for (bool simplify : {false, true})
        take(compileEntry(original, {simplify, false}));
      originals.push_back(std::move(original));
    });
  cases.run("shared helper inputs keep distinct participant values", [&] {
    auto text = (*bytes)->getBuffer().str() + R"(
      protocol Shared roles(P,V)(a:Fr@(P,V),b:Fr@(P,V),x:Fr@(P,V))
        ->(r:(Fr,Fr,Fr,Fr,Fr,Fr)@(P,V)){return(r=calculate(a,b,x));}
      entry SharedDemo=Shared;
    )";
    auto original = take(prepareOriginal(
        take(closeEntry(take(check(text)), "sample::SharedDemo"))));
    take(compileEntry(original));
  });
  cases.run("formal products and zero-arity math compile", [&] {
    auto text = source(R"(
      struct Box<N:nat>{pub p:Poly<N>,pub x:F}
      math fn wrap(x:F)->Box<0>{return Box<0>{p:intrinsic<F,0>("poly.constant",x),x:x};}
      math fn empty()->[Poly<0>;0]{return [];}
      math fn value(x:F)->F{
        let box=wrap(x);
        let discarded=empty();
        let fixed=intrinsic<F,0,0>("poly.fix",box.p,[]);
        let sum=intrinsic<F,0,0>("poly.sum_suffix",fixed);
        return intrinsic<F,0>("poly.evaluate",sum,[]);
      }
      protocol Run roles(P)(x:F@P)->(r:F@P){return(r=value(x));}entry Demo=Run;
    )");
    auto original = take(
        prepareOriginal(take(closeEntry(take(check(text)), "sample::Demo"))));
    take(compileEntry(original));
  });
  auto refuses = [&](StringRef name, const Twine &body, StringRef code) {
    cases.run(name, [&] {
      auto result = check(source(body.str()));
      require(!result, "invalid formal source admitted");
      auto message = toString(result.takeError());
      require(StringRef(message).contains(code), message);
    });
  };
  refuses("unknown formal constructor", "type X=formal(\"vector\",F,1);",
          "source.formal");
  refuses("wrong formal arguments", "type X=formal(\"polynomial\",1,F);",
          "source.formal");
  for (StringRef type : {"Poly<1>", "[Poly<1>;0]", "(F,Poly<1>)"}) {
    refuses("local formal port", "fn bad(x:" + type + ")->(){return ();}",
            "source.formal");
    refuses("protocol formal port",
            "protocol Bad roles(P)(x:" + type + "@P)->(){return ();}",
            "source.formal");
  }
  refuses("formal variant", "enum Bad{P(Poly<1>)}", "source.formal");
  refuses("forward formal record in variant",
          "enum Bad{P(Later)}struct Later{pub p:Poly<1>}", "source.formal");
  refuses("formal nominal runtime argument",
          "struct Box<T:Type>{value:T}type Bad=Box<Poly<1>>;", "source.formal");
  refuses("formal builtin argument", "type Bad=builtin(\"sequence\",Poly<1>);",
          "source.builtin");
  refuses("formal local intermediate", R"(
    math fn p(x:F)->Poly<1>{return intrinsic<F,1>("poly.constant",x);}
    fn bad(x:F)->F{let discarded=p(x);return x;}
  )",
          "source.formal");
  refuses("local data intrinsic",
          "fn bad(x:[F;2])->builtin(\"field_array\",F,2){return "
          "intrinsic<F,2>(\"array.pack\",x);}",
          "source.mode");
  refuses("unknown intrinsic",
          "math fn bad(x:F)->F{return intrinsic<F>(\"field.inverse\",x);}",
          "source.intrinsic");
  refuses(
      "static sort",
      "math fn bad(x:F)->Poly<1>{return intrinsic<1,F>(\"poly.constant\",x);}",
      "source.intrinsic");
  refuses(
      "missing shape argument",
      "math fn bad(x:F)->Poly<1>{return intrinsic<F>(\"poly.constant\",x);}",
      "source.intrinsic");
  refuses("unexpected parameters",
          "math fn bad(x:F)->Poly<1>{return "
          "intrinsic<F,1>(\"poly.constant\",x;\"0\");}",
          "source.intrinsic");
  refuses("out of bounds array index", R"(
    math fn bad(x:builtin("field_array",F,2))->F{return intrinsic<F,2,2>("array.at",x);}
  )",
          "source.bound");
  refuses("empty coefficient source", R"(
    math fn bad(x:builtin("field_array",F,0))->Poly<1>{return intrinsic<F,0>("poly.from_coefficients",x);}
  )",
          "source.bound");
  refuses("closed generic contract needs bound", R"(
    math fn bad<N:nat,I:nat>(x:builtin("field_array",F,N))->F where () {return intrinsic<F,N,I>("array.at",x);}
  )",
          "source.bound");
  refuses("wrong table shape", R"(
    math fn bad(x:builtin("field_array",F,3))->Poly<2>{return intrinsic<F,2>("poly.mle",x);}
  )",
          "source.type");
  refuses("duplicate domain", R"(
    math fn bad(x:Poly<1>)->builtin("field_array",F,2){return intrinsic<F>("poly.evaluate_domain",x;"1","1");}
  )",
          "source.intrinsic");
  refuses("noncanonical domain", R"(
    math fn bad(x:Poly<1>)->builtin("field_array",F,1){return intrinsic<F>("poly.evaluate_domain",x;"01");}
  )",
          "source.intrinsic");
  refuses("generic domain literal", R"(
    math fn bad<G:Field>(x:formal("polynomial",G,1))->builtin("field_array",G,1){return intrinsic<G>("poly.evaluate_domain",x;"2");}
  )",
          "source.intrinsic");
  refuses("empty formal local value", R"(
    math fn empty()->[Poly<1>;0]{return [];}
    fn bad()->(){let discarded=empty();return ();}
  )",
          "source.formal");
  refuses("formal associated representation", R"(
    interface I{type Item:Copy+Drop;}
    component C:I{type Item=Poly<1>;}
  )",
          "source.formal");
  for (StringRef roles : {"P", "(P,V)"})
    refuses(
        "protocol formal intermediate",
        "math fn p(x:F)->Poly<1>{return intrinsic<F,1>(\"poly.constant\",x);}"
        "protocol Bad roles(P,V)(x:F@" +
            roles + ")->(){let q=p(x);return();}",
        "source.formal");
  refuses("formal type mismatch", R"(
    math fn p(x:Poly<1>)->F{return intrinsic<F,1>("poly.evaluate",x,[0]);}
    math fn bad(x:Poly<2>)->F{return p(x);}
  )",
          "source.type");
  refuses("formal inferred runtime type argument", R"(
    math fn identity<T:Type+Copy+Drop>(x:T)->T{return x;}
    math fn bad(x:Poly<1>)->Poly<1>{return identity(x);}
  )",
          "source.formal");
  refuses("empty formal variant", "enum Bad{P([Poly<1>;0])}", "source.formal");
  cases.run("native formal arity ceiling remains a target obligation", [&] {
    auto project = take(check(source(R"(
      math fn p(x:F)->Poly<33>{return intrinsic<F,33>("poly.constant",x);}
      math fn value(x:F)->F{let discarded=p(x);return x;}
      protocol Run roles(P)(x:F@P)->(r:F@P){return(r=value(x));}
      entry Demo=Run;
    )")));
    auto closed = take(closeEntry(project, "sample::Demo"));
    auto result = prepareOriginal(closed);
    require(!result, "oversized native arity admitted");
    auto message = toString(result.takeError());
    require(StringRef(message).contains("target.admission") &&
                StringRef(message).contains("sample::value") &&
                StringRef(message).contains("arity at most 32"),
            message);
  });
  std::string tooMany =
      "math fn bad(x:Poly<1>)->builtin(\"field_array\",F,65){return "
      "intrinsic<F>(\"poly.evaluate_domain\",x;";
  for (unsigned i = 0; i < 65; ++i) {
    if (i)
      tooMany += ",";
    tooMany += "\"" + std::to_string(i) + "\"";
  }
  tooMany += ");}";
  refuses("domain point count bounded", tooMany, "source.intrinsic");
  cases.run("formal product and zero array layouts", [&] {
    auto project = take(check(source("struct Pair{pub p:Poly<1>,pub x:F}math "
                                     "fn id(x:Pair)->Pair{return x;}")));
    Layouts layouts(project);
    Type field(Type::Kind::Field, "bls12-381.fr"), n(Type::Kind::Natural);
    n.dimension = Natural::constant(1);
    auto p = take(formalType("polynomial", {field, n}));
    auto runtimeType = take(builtinType("polynomial", {field}));
    auto runtime = take(layouts.get(runtimeType));
    require(!runtime->formal && runtime->leaves.size() == 1 &&
                runtime->leaves[0].data() &&
                typeIdentity(p) != typeIdentity(runtimeType),
            "formal and executable polynomial layouts alias");
    require(StringRef(spelling(p)).starts_with("formal(\"polynomial\""),
            "formal diagnostic spelling missing");
    auto polynomial = take(layouts.get(p));
    require(polynomial->formal && polynomial->leaves.size() == 1 &&
                polynomial->leaves[0].polynomial(),
            "formal layout is not typed");
    Type empty(Type::Kind::Array);
    empty.arguments = {p};
    auto zero = take(layouts.get(empty));
    require(zero->formal && zero->leaves.empty(),
            "empty array lost formal meaning");
    auto pair = take(layouts.get(Type(Type::Kind::Record, "sample::Pair")));
    require(pair->formal && pair->leaves.size() == 2,
            "formal product layout differs");
  });
  cases.run("zero arrays retain executable element permissions", [&] {
    auto project = take(check(source("struct Hidden{x:F}")));
    Layouts layouts(project);
    Type hidden(Type::Kind::Record, "sample::Hidden"), empty(Type::Kind::Array);
    empty.arguments = {hidden};
    auto element = take(layouts.get(hidden));
    auto zero = take(layouts.get(empty));
    require(!element->permissions.wire && !zero->permissions.wire &&
                !zero->formal && zero->leaves.empty(),
            "zero array erased its element permissions");
  });
  cases.run("selected closure checks generic intrinsic shape ceiling", [&] {
    auto project = take(check(source(R"(
      math fn p<N:nat>(x:F)->F where 1<=pow2(N){
        let a=intrinsic<F,N>("poly.constant",x);
        let unused=intrinsic<F,pow2(N)>("poly.coefficients",intrinsic<F,1>("poly.constant",x));
        return x;
      }
      protocol Run<N:nat> roles(P)(x:F@P)->(r:F@P) where 1<=pow2(N){return(r=p<N>(x));}
      entry Demo=Run<21>;
    )")));
    auto closed = closeEntry(project, "sample::Demo");
    require(!closed, "oversized closed intrinsic shape admitted");
    auto message = toString(closed.takeError());
    require(StringRef(message).contains("source.builtin"), message);
  });
  for (StringRef entry :
       {"sample::Demo", "sample::LocalDemo", "sample::NestedDemo"})
    for (bool used : {false, true})
      for (bool simplify : {false, true})
        cases.run(
            "degree checked before simplification in each body mode", [&] {
              auto changed = replaceText(
                  (*bytes)->getBuffer(),
                  "let coeff = coefficients<Fr,3>(square);",
                  used ? "let coeff = coefficients<Fr,2>(square);"
                       : "let unused = coefficients<Fr,2>(square);let "
                         "coeff = coefficients<Fr,3>(square);");
              if (used)
                changed = replaceText(changed,
                                      "intrinsic<Fr,3,2>(\"array.at\",coeff)",
                                      "intrinsic<Fr,2,1>(\"array.at\",coeff)");
              changed += R"(
            protocol Nested roles(P)(n:index@P,a:Fr@P,b:Fr@P,x:Fr@P)
                ->(r:(Fr,Fr,Fr,Fr,Fr,Fr)@P){
              let mut r@P=(a,a,a,a,a,a);
              for _ in 0..n roles(P) max 2 {
                r=calculate(a,b,x);
              }
              return(r=r);
            }entry NestedDemo=Nested;
          )";
              auto project = take(check(changed));
              auto original =
                  take(prepareOriginal(take(closeEntry(project, entry))));
              auto result = compileEntry(original, {simplify, false});
              require(!result, "under-width observation accepted");
              auto message = toString(result.takeError());
              require(StringRef(message).contains("fitting degree bound"),
                      message);
            });
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  for (bool valid : {false, true})
    cases.run(
        "unexecuted helper observations are checked without mutation", [&] {
          auto text = source(R"(
        math fn observe(x:F)->F {
          let p=intrinsic<F,1>("poly.constant",x);
          let q=intrinsic<F,2>("poly.from_coefficients",intrinsic<F,2>("array.pack",[x,x]));
          let product=intrinsic<F,1>("poly.multiply",p,q);
          let coefficients=intrinsic<F,2>("poly.coefficients",product);
          return x;
        }
        protocol Run roles(P)(x:F@P)->(r:F@P){return(r=x);}
        entry Demo=Run;
      )");
          // Close the helper through an ordinary call, then remove that call
          // from the admitted original. The helper remains available only for
          // analysis.
          text = replaceText(text, "return(r=x);", "return(r=observe(x));");
          if (!valid)
            text = replaceText(text, "intrinsic<F,2>(\"poly.coefficients\"",
                               "intrinsic<F,1>(\"poly.coefficients\"");
          auto original = take(prepareOriginal(
              take(closeEntry(take(check(text)), "sample::Demo"))));
          auto module = mlir::parseSourceString<mlir::ModuleOp>(
              original.bytes(), &context);
          require(bool(module), "cannot parse observation original");
          auto *call = first(*module, "func.call");
          auto target = call->getAttrOfType<mlir::FlatSymbolRefAttr>("callee")
                            .getValue()
                            .str();
          call->getResult(0).replaceAllUsesWith(call->getOperand(0));
          call->erase();
          require(succeeded(mlir::verify(*module)),
                  "uncalled helper original invalid");
          auto print = [&] {
            std::string result;
            raw_string_ostream stream(result);
            module->print(stream, mlir::OpPrintingFlags().printGenericOpForm());
            return result;
          };
          auto before = print();
          mlir::ScopedDiagnosticHandler quiet(
              &context, [](mlir::Diagnostic &) { return mlir::success(); });
          require(succeeded(zkc::mathematical::verifyHelperObservations(
                      *module, {target})) == valid,
                  "uncalled helper observation validity differs");
          require(print() == before, "observation analysis mutated its input");
          require(failed(zkc::mathematical::verifyHelperObservations(
                      *module, {"missing"})),
                  "missing helper accepted");
          require(failed(zkc::mathematical::verifyHelperObservations(
                      *module, {target, target})),
                  "duplicate roots accepted");
        });
  auto mutate = [&](StringRef name,
                    function_ref<void(mlir::ModuleOp)> mutation) {
    cases.run(name, [&] {
      require(!originals.empty(),
              "source original unavailable after failed case");
      auto module = mlir::parseSourceString<mlir::ModuleOp>(
          originals[0].bytes(), &context);
      require(bool(module), "cannot parse source original");
      mutation(*module);
      require(succeeded(mlir::verify(*module)),
              "mutation must be admitted native IR");
      auto result = compareOriginal(originals[0].entry(), *module);
      require(!result, "altered formal operation matched");
      auto message = toString(result.takeError());
      require(StringRef(message).contains("source.correspondence"), message);
    });
  };
  mutate("polynomial operation identity changed", [&](auto module) {
    auto *add = first(module, "poly.add");
    mlir::OpBuilder builder(add);
    mlir::OperationState state(add->getLoc(), "poly.multiply");
    state.addOperands(add->getOperands());
    state.addTypes(add->getResultTypes());
    auto *multiply = builder.create(state);
    add->replaceAllUsesWith(multiply);
    add->erase();
  });
  mutate("domain coordinate changed", [&](auto module) {
    mlir::Builder b(&context);
    first(module, "poly.evaluate_domain")
        ->setAttr("points", b.getStrArrayAttr({"0", "1", "3"}));
  });
  mutate("array index changed", [&](auto module) {
    mlir::Builder b(&context);
    first(module, "algebra.array_at")->setAttr("index", b.getI64IntegerAttr(1));
  });
  mutate("flattened array elements swapped", [&](auto module) {
    auto *op = first(module, "tensor.from_elements");
    auto a = op->getOperand(0);
    op->setOperand(0, op->getOperand(1));
    op->setOperand(1, a);
  });
  return cases.result();
}
