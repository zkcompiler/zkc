#include "zkc/Compiler/Language.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>

using namespace llvm;
using namespace zkc::language;
namespace {
StringRef stage;
void require(bool ok, StringRef message) {
  if (!ok) {
    errs() << stage << ": " << message << '\n';
    std::exit(1);
  }
}
template <typename T> T must(Expected<T> value) {
  if (!value) {
    errs() << stage << ": " << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
void success(Error error) {
  if (error) {
    errs() << toString(std::move(error)) << '\n';
    std::exit(1);
  }
}
void refuses(Error error, StringRef code) {
  require(bool(error), "expected refusal");
  auto message = toString(std::move(error));
  require(StringRef(message).contains(code), message);
}
template <typename T> void refuses(Expected<T> value, StringRef code) {
  require(!value, "expected refusal");
  refuses(value.takeError(), code);
}
std::string read(StringRef name) {
  auto file =
      MemoryBuffer::getFile((Twine(ZKC_LANGUAGE_FIXTURES) + "/" + name).str());
  require(bool(file), "missing fixture");
  return (*file)->getBuffer().str();
}
CheckedProject check(StringRef source, const Limits &limits = {}) {
  return must(analyze(must(capture({{"m", source.str(), "m.zkc"}})), limits)
                  .checkedProject());
}
void sourceRefuses(StringRef source, StringRef code,
                   const Limits &limits = {}) {
  auto result = analyze(must(capture({{"m", source.str(), "m.zkc"}})), limits)
                    .checkedProject();
  if (result)
    errs() << "unexpectedly accepted source (" << code << "): " << source
           << '\n';
  require(!result, "expected source refusal");
  auto message = toString(result.takeError());
  if (!StringRef(message).contains(code))
    errs() << "expected " << code << " for:\n" << source << '\n';
  require(StringRef(message).contains(code), message);
}
CheckedOriginal original(StringRef source) {
  return must(prepareOriginal(must(closeEntry(check(source), "m::Demo"))));
}
std::string replace(std::string text, StringRef from, StringRef to) {
  auto at = text.find(from.str());
  require(at != std::string::npos, "test replacement missing");
  text.replace(at, from.size(), to);
  return text;
}
constexpr StringLiteral basic = R"(module m;
domain Fr = field("bls12-381.fr");
protocol Run roles(P, V)(x: Fr @P, c: Fr @(P,V)) -> (r: Fr @V) {
 let a = x + c;
 let received = send P -> V(a);
 return (r = received);
}
entry Demo = Run;
)";
mlir::Operation *first(mlir::ModuleOp module, StringRef name,
                       unsigned occurrence = 0) {
  mlir::Operation *found = nullptr;
  module.walk([&](mlir::Operation *op) {
    if (op->getName().getStringRef() == name && !found && occurrence-- == 0)
      found = op;
  });
  require(found, "missing mutation target");
  return found;
}
void mutation(const CheckedOriginal &original, StringRef name,
              const std::function<void(mlir::ModuleOp)> &mutate) {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
  require(bool(module), "original parsing failed");
  mutate(*module);
  require(mlir::succeeded(mlir::verify(*module)),
          "mutation failed IR admission instead of correspondence");
  auto result = compareOriginal(original.entry(), *module);
  if (result) {
    errs() << "mutation accepted: " << name << '\n';
    std::exit(1);
  }
  refuses(result.takeError(), "source.correspondence");
}
void sourceControls() {
  for (const auto &entry : std::vector<std::pair<std::string, std::string>>{
           {replace(basic.str(), "module m", "module wrong"), "source.module"},
           {replace(basic.str(), "x + c", "unknown + c"), "source.name"},
           {replace(basic.str(), "x + c", "true + false"), "source.type"},
           {replace(basic.str(), "let a = x + c;", "let a = 1;"),
            "source.inference"},
           {replace(basic.str(), "let a = x + c;",
                    "let a: Fr = "
                    "5243587517512619047944774050818596583769055250052763782260"
                    "3658699938581184513;"),
            "source.literal"},
           {replace(basic.str(), "let a", "let x"), "source.name"},
           {replace(basic.str(), "let a", "let Fr"), "source.shadow"},
           {replace(basic.str(), "send P -> V", "send P -> P"), "source.send"},
           {replace(basic.str(), "send P -> V", "send V -> P"), "source.roles"},
           {replace(basic.str(), "return (r = received)",
                    "return (r = received, r = received)"),
            "source.return"},
           {replace(basic.str(), "return (r = received)", "return ()"),
            "source.type"},
           {replace(basic.str(), "return (r = received)",
                    "return (other = received)"),
            "source.return"},
           {replace(basic.str(), "r: Fr @V", "r: Fr @P"), "source.roles"},
           {replace(basic.str(), "let a =", "let a @V ="), "source.roles"},
           {replace(basic.str(), "roles(P, V)", "roles(P, P)"), "source.roles"},
           {replace(basic.str(), "let a = x + c", "let a = (x == c == x)"),
            "source.syntax"},
           {replace(basic.str(), "entry Demo = Run", "entry Demo = Fr"),
            "source.entry"},
           {basic.str() + "math fn bad(x: Fr) -> Fr { return bad(x); }",
            "source.cycle"},
           {basic.str() + "math fn unused(x: Fr) -> Fr { return missing; }",
            "source.name"},
           {replace(basic.str(), "let a = x + c", "let a = Run(x,c)"),
            "source.cycle"},
       })
    sourceRefuses(entry.first, entry.second);
  auto unknown = capture({{"m", "module m;", {}}}, CaptureOptions{"json", {}});
  refuses(std::move(unknown), "source.format");
  refuses(capture({{"m", std::string("\xff", 1), {}}}), "source.encoding");
  refuses(capture({{"m", "module m;", {}}, {"m", "module m;", {}}}),
          "source.module");
  sourceRefuses("module m; domain F = field(\"bls12-381\\x.fr\");",
                "source.string");
  sourceRefuses("module m; use absent::{F};", "source.import");
  sourceRefuses("module m; use absent{F};", "source.syntax");
  auto cycle = must(capture(
      {{"a", "module a; use b::{B}; pub domain A=field(\"bls12-381.fr\");", {}},
       {"b",
        "module b; use a::{A}; pub domain B=field(\"bls12-381.fr\");",
        {}}}));
  refuses(analyze(cycle).checkedProject(), "source.cycle");
  auto privacy = must(
      capture({{"a", "module a; domain F=field(\"bls12-381.fr\");", {}},
               {"m", "module m; math fn f(x:a::F)->bool{return true;}", {}}}));
  refuses(analyze(privacy).checkedProject(), "source.private");
  std::string helpers = R"(module m; domain Fr=field("bls12-381.fr");
math fn first(a: Fr,b: Fr)->Fr {return a;}
protocol Run roles(P,V)(a:Fr@P,b:Fr@V)->(r:Fr@P){let result=first(a,b);return(r=result);}
entry Demo=Run;)";
  auto ignored = original(helpers);
  must(compileEntry(ignored));
  sourceRefuses(replace(helpers, "{return a;}", "{let unused=a+b;return a;}"),
                "source.roles");
  auto subset = original(
      R"(module m;protocol Run roles(P,V)(x:bool@(P,V))->(a:bool@V,b:bool@V){return(b=true,a=x);}entry Demo=Run;)");
  require(!subset.bytes().contains("restrict_roles"),
          "narrow output inserted a restriction");
  auto same = original(
      R"(module m;protocol Run roles(P)(x:bool@P)->(r:bool@P){let y @P=x;return(r=y);}entry Demo=Run;)");
  require(!same.bytes().contains("restrict_roles"),
          "equal role annotation inserted a restriction");
  auto qualified =
      must(capture({{"a",
                     "module a; pub domain F=field(\"bls12-381.fr\"); pub math "
                     "fn identity(x:F)->F{return x;}",
                     {}},
                    {"m",
                     "module m; protocol Run "
                     "roles(P)(x:a::F@P)->(r:a::F@P){return(r=a::identity(x));}"
                     " entry Demo=Run;",
                     {}}}));
  must(compileEntry(must(prepareOriginal(must(
      closeEntry(must(analyze(qualified).checkedProject()), "m::Demo"))))));
}
void nameResolution() {
  const std::string definitions = R"(module m;
interface I { type State: Copy + Drop; }
component C: I { type State: Copy + Drop = bool; }
)";
  const std::string unrelated =
      "module C;pub domain State=field(\"bls12-381.fr\");"
      "pub type Missing=bool;";
  auto checked = [&](StringRef body, bool extra) {
    std::vector<SourceBuffer> sources{{"m", definitions + body.str(), {}}};
    if (extra)
      sources.push_back({"C", unrelated, {}});
    return analyze(must(capture(std::move(sources)))).checkedProject();
  };
  for (bool extra : {false, true}) {
    auto project =
        must(checked("fn f(x:C::State)->C::State{return x;}", extra));
    require(project.declarations().back().inputs.front().type.kind ==
                Type::Kind::Associated,
            "captured module replaced lexical component member");
    refuses(checked("fn f(x:C::Missing)->bool{return x;}", extra),
            "source.name");
    refuses(checked("fn f(x:C::State)->index{return x;}", extra),
            "source.type");
  }
  must(checked("fn f(x: ::C::State)->::C::State{return x;}", true));
  auto captureMember = must(
      capture({{"m", definitions + "fn f(x:C::Ghost)->bool{return x;}", {}},
               {"m::C", "module m::C;pub type Ghost=bool;", {}}}));
  refuses(analyze(captureMember).checkedProject(), "source.name");
  // Private prefix lookup must preserve the original refusal and its source.
  auto project = must(capture(
      {{"a", "module a;domain G=group(\"bls12-381.g1\");", {}},
       {"m", "module m;fn f(x:a::G::Scalar)->bool{return true;}", {}}}));
  auto analysis = analyze(project);
  require(!analysis.diagnostics().empty(), "private projection accepted");
  require(analysis.diagnostics().front().code == "source.private",
          "private prefix diagnostic was lost");
  require(analysis.diagnostics().front().primary.has_value(),
          "private projection lost source location");

  // Repeated lookups in a wide component must account for the member scans.
  constexpr unsigned width = 512, uses = 32;
  std::string wide = "module m;interface I{";
  for (unsigned i = 0; i < width; ++i)
    wide += "type T" + std::to_string(i) + ": Copy + Drop;";
  wide += "}component C:I{";
  for (unsigned i = 0; i < width; ++i)
    wide += "type T" + std::to_string(i) + ": Copy + Drop=bool;";
  wide += "}";
  auto baseWork = check(wide).checkedWork();
  auto projected = wide, unprojected = wide;
  for (unsigned i = 0; i < uses; ++i) {
    projected +=
        "fn p" + std::to_string(i) + "<T:I>(x:T::T511)->T::T511{return x;}";
    unprojected +=
        "fn p" + std::to_string(i) + "<T:I>(x:bool)->bool{return x;}";
  }
  require(check(projected).checkedWork() >=
              check(unprojected).checkedWork() + 2 * width * uses,
          "associated projection scans escaped the work budget");
  for (unsigned i = 0; i < uses; ++i)
    wide += "fn f" + std::to_string(i) + "(x:C::T511)->C::T511{return x;}";
  auto full = check(wide);
  require(full.checkedWork() >= baseWork + 2 * width * uses,
          "component lookup scans escaped the work budget");
  Limits limit;
  limit.work = full.checkedWork() - 1;
  sourceRefuses(wide, "source.limit", limit);
}
void specializationSnapshotBounds() {
  // Many static instances copy the same nested literal payload. Closure must
  // refuse a budget smaller than that payload, even if checking fit it.
  constexpr unsigned instances = 64, literals = 64, digits = 76;
  std::string source = "module m;domain Fr=field(\"bls12-381.fr\");fn "
                       "f<N:nat>(go:bool)->Fr{return if go {";
  for (unsigned i = 0; i < literals; ++i)
    source +=
        "let x" + std::to_string(i) + ":Fr=" + std::string(digits, '1') + ";";
  source += " x63}else{ 0};}protocol Run roles(P)(go:bool@P)->(){";
  for (unsigned i = 0; i < instances; ++i)
    source +=
        "let v" + std::to_string(i) + "@P=f<" + std::to_string(i) + ">(go);";
  source += "return();}entry Demo=Run;";
  auto project = check(source);
  must(closeEntry(project, "m::Demo"));
  Limits limit;
  limit.work = instances * literals * digits - 1;
  require(project.checkedWork() < limit.work,
          "snapshot fixture exceeds the checking budget");
  refuses(closeEntry(project, "m::Demo", limit), "source.limit");
}
void semanticDiagnosticLocations() {
  for (StringRef expression : {"18446744073709551615+1", "pow2(64)"}) {
    std::string source = "module m;type A=[bool;" + expression.str() + "];";
    auto analysis = analyze(must(capture({{"m", source, {}}})));
    require(analysis.diagnostics().size() == 1, "missing arithmetic refusal");
    const auto &diagnostic = analysis.diagnostics().front();
    require(diagnostic.code == "source.natural", "arithmetic code changed");
    require(diagnostic.primary.has_value(), "arithmetic source span lost");
    auto span = *diagnostic.primary;
    require(span.module.index == 0 &&
                StringRef(source).slice(span.begin, span.end) == expression,
            "arithmetic span does not select the failing expression");
  }
}
void syntaxTreeBounds() {
  Limits limits;
  limits.parseDepth = 4;
  for (StringRef expression : {"1+1+1", "1+1*1", "1*1*1"})
    check("module m;type A=[bool;" + expression.str() + "];", limits);
  for (StringRef expression : {"1+1+1+1", "1*1*1*1"})
    sourceRefuses("module m;type A=[bool;" + expression.str() + "];",
                  "source.limit", limits);
  // Recursive-descent depth stays small for a flat operator chain. Refuse
  // before it forms a syntax tree whose destruction can overflow the stack.
  std::string flat = "module m;type A=[bool;1";
  for (unsigned i = 1; i < 150000; ++i)
    flat += "+1";
  flat += "];";
  sourceRefuses(flat, "source.limit");
}
void depthAndAggregateBounds() {
  auto modules = must(
      capture({{"a",
                "module a; pub domain F=field(\"bls12-381.fr\"); pub math fn "
                "add(x:F)->F{return x+x;}",
                {}},
               {"m",
                "module m; use a::{F,add}; protocol Run "
                "roles(P)(x:F@P)->(r:F@P){return(r=add(x));} entry Demo=Run;",
                {}}}));
  auto all = must(analyze(modules).checkedProject());
  Limits limits;
  for (auto member : {&Limits::importDepth, &Limits::callDepth}) {
    limits = {};
    limits.*member = 2;
    must(analyze(modules, limits).checkedProject());
    limits.*member = 1;
    refuses(analyze(modules, limits).checkedProject(), "source.limit");
  }
  for (auto member : {&Limits::parseDepth, &Limits::expressionDepth}) {
    limits = {};
    limits.*member = 2;
    check(basic, limits);
    limits.*member = 1;
    sourceRefuses(basic, "source.limit", limits);
  }
  for (auto member : {&Limits::tokens, &Limits::declarations,
                      &Limits::operations, &Limits::work}) {
    limits = {};
    limits.*member =
        member == &Limits::tokens
            ? all.tokens(ModuleId{0}).size() + all.tokens(ModuleId{1}).size()
        : member == &Limits::declarations ? all.declarations().size()
        : member == &Limits::operations   ? 2
                                          : all.checkedWork();
    must(analyze(modules, limits).checkedProject());
    --(limits.*member);
    refuses(analyze(modules, limits).checkedProject(), "source.limit");
  }
  limits = {};
  limits.identifierBytes = 9;
  auto names = replace(replace(basic.str(), "let a =", "let abcdefghi ="),
                       "V(a)", "V(abcdefghi)");
  check(names, limits);
  limits.identifierBytes = 8;
  sourceRefuses(names, "source.limit", limits);
  limits = {};
  limits.captureBytes = 18;
  must(capture({{"m", "module m;", {}}, {"n", "module n;", {}}},
               {"zkc", limits}));
  limits.captureBytes = 17;
  refuses(capture({{"m", "module m;", {}}, {"n", "module n;", {}}},
                  {"zkc", limits}),
          "source.limit");
  auto selected = must(closeEntry(check(basic), "m::Demo"));
  refuses(closeEntry(selected.project(), std::string(4097, 'a')),
          "source.limit");
}
void reviewControls() {
  for (StringRef feature : {"service", "predicate", "requires", "construct"})
    sourceRefuses("module m; " + feature.str() + " X;", "source.unsupported");
  sourceRefuses("module m; math fn f<F>() -> bool {return true;}",
                "source.syntax");
  sourceRefuses("module m; domain F=field(\"missing\");", "source.domain");
  sourceRefuses("module m; domain F=field(\"bls12-381.g1\");", "source.domain");
  sourceRefuses(
      R"(module m;domain A=field("bls12-381.fr");domain B=field("bn254.fr");
math fn f(x:A,y:B)->A{return x+y;})",
      "source.type");
  sourceRefuses(R"(module m;protocol Run roles(P,V)(x:bool@V)->(r:bool@V){
let sent=send V->P(x);return(r=sent);}entry Demo=Run;)",
                "source.roles");
  for (unsigned size : {128, 129}) {
    auto text = replace(
        replace(basic.str(), "let a =", "let " + std::string(size, 'a') + " ="),
        "V(a)", "V(" + std::string(size, 'a') + ")");
    if (size == 128)
      check(text);
    else
      sourceRefuses(text, "source.limit");
  }
  for (unsigned depth : {64, 65}) {
    std::string parens = "module m;math fn f(x:bool)->bool{return " +
                         std::string(depth - 1, '(') + "x" +
                         std::string(depth - 1, ')') + ";}";
    std::string sum =
        "module m;domain F=field(\"bls12-381.fr\");math fn f(x:F)->F{return x";
    for (unsigned i = 1; i < depth; ++i)
      sum += "+x";
    sum += ";}";
    std::string calls = "module m;math fn f0()->bool{return true;}";
    for (unsigned i = 1; i < depth; ++i)
      calls += "math fn f" + std::to_string(i) + "()->bool{return f" +
               std::to_string(i - 1) + "();}";
    std::vector<SourceBuffer> modules;
    for (unsigned i = 0; i < depth; ++i) {
      std::string name = "m" + std::to_string(i);
      auto own = i % 2 ? "D" : "F", next = i % 2 ? "F" : "D";
      std::string text =
          "module " + name + ";pub domain " + own + "=field(\"bls12-381.fr\");";
      if (i + 1 < depth)
        text += "use m" + std::to_string(i + 1) + "::{" + next + "};";
      modules.push_back({name, text, {}});
    }
    if (depth == 64) {
      check(parens);
      check(sum);
      check(calls);
      must(analyze(must(capture(modules))).checkedProject());
    } else {
      sourceRefuses(parens, "source.limit");
      sourceRefuses(sum, "source.limit");
      sourceRefuses(calls, "source.limit");
      refuses(analyze(must(capture(modules))).checkedProject(), "source.limit");
    }
  }
  std::string expansion =
      "module m;domain F=field(\"bls12-381.fr\");math fn f0()->F{return 1;}";
  for (unsigned i = 1; i < 18; ++i)
    expansion += "\nmath fn f" + std::to_string(i) + "()->F{return f" +
                 std::to_string(i - 1) + "()+f" + std::to_string(i - 1) +
                 "();}";
  expansion += "\nprotocol Small roles(P)()->(r:F@P){return(r=1);}";
  expansion += "\nprotocol Unused roles(P)()->(r:F@P){return(r=f17());}entry "
               "Demo=Small;entry Large=Unused;";
  auto alternatives = check(expansion);
  must(prepareOriginal(must(closeEntry(alternatives, "m::Demo"))));
  auto failure = prepareOriginal(must(closeEntry(alternatives, "m::Large")));
  require(!failure, "selected target expansion was not checked");
  bool identified = false;
  handleAllErrors(failure.takeError(), [&](const zkc::CompilationError &error) {
    identified = llvm::any_of(error.refusals,
                              [](const auto &r) {
                                return r.code == "target.admission";
                              }) &&
                 llvm::any_of(error.locations, [](const auto &l) {
                   return l.filename == "m.zkc" && l.line > 1;
                 });
  });
  require(identified,
          "target admission lost its phase or related source declaration");
  auto full = original(basic);
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  mlir::ScopedDiagnosticHandler silence(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  auto module = mlir::parseSourceString<mlir::ModuleOp>(full.bytes(), &context);
  require(bool(module), "missing original");
  first(*module, "protocol.func")
      ->setAttr("roles", mlir::StringAttr::get(&context, "bad"));
  refuses(compareOriginal(full.entry(), *module), "target.admission");
  auto usedSource = replace(basic.str(), "let a = x + c;",
                            "let ignored = helper(true); let a = x + c;");
  auto withUnused = original(
      usedSource + "math fn helper(x:bool)->bool{let y=x==x;return x;}");
  auto identityHelper =
      original(usedSource + "math fn helper(x:bool)->bool{return x;}");
  for (auto signedness :
       {mlir::IntegerType::Signed, mlir::IntegerType::Unsigned}) {
    auto candidate = mlir::parseSourceString<mlir::ModuleOp>(
        identityHelper.bytes(), &context);
    auto *function = first(*candidate, "func.func");
    auto type = mlir::IntegerType::get(&context, 1, signedness);
    function->setAttr(
        "function_type",
        mlir::TypeAttr::get(mlir::FunctionType::get(&context, {type}, {type})));
    function->getRegion(0).front().getArgument(0).setType(type);
    // Whole-module admission already rejects non-signless helper signatures.
    refuses(compareOriginal(identityHelper.entry(), *candidate),
            "target.admission");
  }
  mutation(withUnused, "Boolean equality changed to inequality",
           [](auto candidate) {
             auto *comparison = first(candidate, "arith.cmpi");
             comparison->setAttr(
                 "predicate",
                 mlir::IntegerAttr::get(
                     mlir::IntegerType::get(candidate.getContext(), 64),
                     static_cast<int64_t>(mlir::arith::CmpIPredicate::ne)));
           });
  mutation(withUnused, "extra helper inserted", [](auto m) {
    auto *existing = first(m, "func.func");
    auto *copy = existing->clone();
    copy->setAttr("sym_name", mlir::StringAttr::get(m.getContext(), "extra"));
    mlir::OpBuilder builder(existing);
    builder.insert(copy);
  });
  mutation(withUnused, "unused operation omitted",
           [](auto m) { first(m, "arith.cmpi")->erase(); });
}
void protocolApplications() {
  auto source = replace(read("application.zkc"), "module sample;", "module m;");
  auto checked = original(source);
  const auto &protocol = checked.entry().protocol();
  bool found = false;
  for (const auto &op : protocol.body->operations)
    if (std::holds_alternative<ProtocolApplication>(op.action)) {
      require(op.results.size() == 2, "application lost its separate results");
      require(protocol.body->values[op.results[0].index].components ==
                      std::vector<unsigned>{0} &&
                  protocol.body->values[op.results[1].index].components ==
                      std::vector<unsigned>{1},
              "application combined unrelated participant sets");
      found = true;
    }
  require(found, "missing checked protocol application");
  for (bool simplify : {false, true})
    must(compileEntry(checked, {simplify, false}));
  sourceRefuses(replace(source, "roles(V,P)(x, y)", "roles(P,P)(x, y)"),
                "source.roles");
  sourceRefuses(replace(source, "roles(V,P)(x, y)", "roles()(x, y)"),
                "source.roles");
  sourceRefuses(replace(source, "roles(V,P)(x, y)", "roles(Unknown,P)(x, y)"),
                "source.roles");
  sourceRefuses(replace(source, "let (atV, atP)", "let (atV, atV)"),
                "source.binding");
  sourceRefuses(replace(replace(source, "p = atP", "p = atV"), "let (atV, atP)",
                        "let atV"),
                "source.binding");
  sourceRefuses(replace(source, "p = atP, v = atV", "p = atV, v = atP"),
                "source.roles");
  sourceRefuses(replace(source, "x: Fr @(P,V)", "x: Fr @P"), "source.roles");
  sourceRefuses(replace(source, "Segment(x, y)", "Run(x, y)"), "source.cycle");
  sourceRefuses(replace(source, "Segment(x, y)", "Segment(x)"), "source.call");
  check(replace(source, "let (a, b) = Segment(x, y);", "let (a, b) = (x, y);"));
  auto limits = Limits{};
  limits.callDepth = 2;
  sourceRefuses(source, "source.limit", limits);
  mutation(checked, "application argument swap", [](auto module) {
    auto *op = first(module, "protocol.apply");
    auto a = op->getOperand(0), b = op->getOperand(1);
    op->setOperand(0, b);
    op->setOperand(1, a);
  });
  mutation(checked, "application site change", [](auto module) {
    first(module, "protocol.apply")
        ->setAttr("site",
                  mlir::StringAttr::get(module.getContext(), "changed"));
  });
  mutation(checked, "omitted resultless application", [](auto module) {
    module.walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() == "protocol.apply" &&
          op->getNumResults() == 0)
        op->erase();
    });
  });
}
void reviewedSourceBoundaries() {
  auto distinctServices = original(
      replace(read("service_order.zkc"), "module sample;", "module m;"));
  must(compileEntry(distinctServices));
  mutation(distinctServices, "application service roots swapped", [](auto m) {
    auto *apply = first(m, "protocol.apply");
    auto left = apply->getOperand(0), right = apply->getOperand(1);
    apply->setOperand(0, right);
    apply->setOperand(1, left);
  });
  for (auto key : {"owner", "contract", "native", "name"}) {
    auto forged = must(json::parse(distinctServices.interfaceJson()));
    auto *service = forged.getAsObject()
                        ->getArray("protocols")
                        ->front()
                        .getAsObject()
                        ->getArray("services")
                        ->front()
                        .getAsObject();
    (*service)[key] = "forged";
    std::string bytes;
    raw_string_ostream(bytes) << forged;
    refuses(checkInterface(distinctServices, bytes), "source.interface");
  }
  for (auto source : {
           R"(module m;domain Fr=field("bls12-381.fr");
protocol Run roles(A,B)(x:Fr@(A,B),y:Fr@B)->(r:(Fr,Fr)@B){let t=(x,y);return(r=t);}entry Demo=Run;)",
           R"(module m;domain Fr=field("bls12-381.fr");
interface Mix {math fn mix(a:Fr,b:Fr)->Fr;}
component First:Mix {math fn mix(a:Fr,b:Fr)->Fr{return a;}}
math fn keep<C:Mix>(x:Fr,y:Fr)->Fr{return C::mix(x,y);}
protocol Run roles(A,B)(x:Fr@(A,B),y:Fr@B)->(r:Fr@B){return(r=keep<First>(x,y));}entry Demo=Run;)",
           R"(module m;domain Fr=field("bls12-381.fr");
math fn pair(x:Fr,y:Fr)->(Fr,Fr){return(x,y);}
protocol Run roles(A,B)(x:Fr@(A,B),y:Fr@B)->(r:(Fr,Fr)@B){return(r=pair(x,y));}entry Demo=Run;)",
           R"(module m;math fn yes(x:bool)->bool{return x;}
protocol Run roles(V)(go:bool@V)->(){guard @V yes(go);return();}entry Demo=Run;)",
           R"(module m;domain Fr=field("bls12-381.fr");
protocol Run roles(V)(x:Fr@V)using(coins:Random<Fr>@V)->(){guard @V coins.draw()==x;return();}entry Demo=Run;)",
       })
    must(compileEntry(original(source)));
  sourceRefuses(R"(module m;fn yes(x:bool)->bool{return x;}
protocol Run roles(V)(go:bool@V)->(){guard @V yes(go);return();}entry Demo=Run;)",
                "source.mode");
  auto emptyMessage = check(R"(module m;
protocol Relay<T:Type+Copy+Drop+Share+Wire> roles(P,V)(x:T@P)->(r:T@V){let y=send P->V(x);return(r=y);}entry Demo=Relay<()>;)");
  refuses(closeEntry(emptyMessage, "m::Demo"), "source.wire");
  auto distinct = original(R"(module m;domain Fr=field("bls12-381.fr");
interface Mix {math fn mix(a:Fr,b:Fr)->Fr;}
component First:Mix {math fn mix(a:Fr,b:Fr)->Fr{return a;}}
component Second:Mix {math fn mix(a:Fr,b:Fr)->Fr{return b;}}
math fn keep<C:Mix>(x:Fr,y:Fr)->Fr{return C::mix(x,y);}
protocol Run roles(P)(x:Fr@P,y:Fr@P)->(a:Fr@P,b:Fr@P){return(a=keep<First>(x,y),b=keep<Second>(x,y));}entry Demo=Run;)");
  must(compileEntry(distinct));
  mutation(distinct, "selected component changed", [](auto m) {
    std::vector<mlir::Operation *> calls;
    m.walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() == "func.call")
        calls.push_back(op);
    });
    require(calls.size() >= 2, "dispatch calls missing");
    calls.back()->setAttr("callee", calls[calls.size() - 2]->getAttr("callee"));
  });
}
void participantCompletion() {
  auto source = replace(read("completion.zkc"), "module sample;", "module m;");
  auto checked = original(source);
  for (auto fixture :
       {"completion.zkc", "completion_nested.zkc", "completion_affine.zkc"})
    for (bool simplify : {false, true})
      must(compileEntry(
          original(replace(read(fixture), "module sample;", "module m;")),
          {simplify, false}));
  for (const auto &[from, to, code] :
       std::vector<std::tuple<std::string, std::string, std::string>>{
           {" completes", "", "source.completion"},
           {"finish_if @V(go)", "finish_if @P(go)", "source.roles"},
           {"(result = x)", "()", "source.completion"},
           {"(result = x)", "(unknown = x)", "source.completion"},
           {"(result = x)", "(result = x, result = x)", "source.completion"},
           {"let () = finish_if", "let unusedResult = finish_if",
            "source.binding"},
           {"finish_if @V(go)", "finish_if @V(x)", "source.type"},
       })
    sourceRefuses(replace(source, from, to), code);
  sourceRefuses(source + R"(
protocol Reuse roles(P,V)(go:bool@V,x:Fr@(P,V))using(coins:Random<Fr>@V)->(result:Fr@(P,V)){
 let result=Run(go,x)using(coins);return(result=result);
})",
                "source.completion");
  auto affine =
      replace(read("completion_affine.zkc"), "module sample;", "module m;");
  sourceRefuses(replace(affine, "state = next;", "state = state;"),
                "source.move");
  sourceRefuses(replace(replace(affine, "state = next;", ""),
                        "let next = finish_if", "let () = finish_if"),
                "source.binding");
  must(compileEntry(original(R"(module m;domain Fr=field("bls12-381.fr");
protocol Run<T:Type>roles(P)(x:T@P,go:bool@P)->(value:T@P)completes {
 let next=finish_if @P(go)(value=x);return(value=next);
}entry Demo=Run<Fr>;)")));
  mutation(checked, "completion occurrence changed", [](auto m) {
    first(m, "protocol.finish_if")
        ->setAttr("site", mlir::StringAttr::get(m.getContext(), "changed"));
  });
  mutation(checked, "completion omitted",
           [](auto m) { first(m, "protocol.finish_if")->erase(); });
  mutation(checked, "completion condition changed", [](auto m) {
    auto *op = first(m, "protocol.finish_if");
    m.getContext()->template getOrLoadDialect<mlir::arith::ArithDialect>();
    mlir::OpBuilder builder(op);
    auto replacement = mlir::arith::ConstantOp::create(
        builder, op->getLoc(), builder.getBoolAttr(false));
    op->setOperand(0, replacement);
  });
}
void distributedRepetition() {
  auto source = replace(read("repeat.zkc"), "module sample;", "module m;");
  auto checked = original(source);
  for (bool simplify : {false, true})
    must(compileEntry(checked, {simplify, false}));
  for (const auto &[from, to, code] :
       std::vector<std::tuple<std::string, std::string, std::string>>{
           {"n: index @(P,V)", "n: index @V", "source.roles"},
           {"let mut vb = b", "let mut vb @P = b", "source.roles"},
           {"pa = x;", "pa = y;", "source.roles"},
           {"guard @V go;", "guard @V missing;", "source.name"},
           {"using(coins);", "using();", "source.service"},
           {"max N", "max Fr", "source.bound"},
           {"max N", "max 1048577", "source.bound"},
           {"let (x, y)", "let (x, x)", "source.binding"},
           {"for _ in", "for pa in", "source.shadow"},
       })
    sourceRefuses(replace(source, from, to), code);
  sourceRefuses(
      replace(replace(source, "vb = y;", "vb = x;"), "let (x, y)", "let x"),
      "source.binding");
  auto generic = check(source + "entry Large = Run<1048577>;");
  must(prepareOriginal(must(closeEntry(generic, "m::Demo"))));
  refuses(closeEntry(generic, "m::Large"), "source.bound");
  mutation(checked, "repeat maximum changed", [](auto m) {
    first(m, "protocol.repeat")
        ->setAttr("maximum",
                  mlir::IntegerAttr::get(
                      mlir::IntegerType::get(m.getContext(), 64), 3));
  });
  mutation(checked, "repeat occurrence changed", [](auto m) {
    auto *repeat = first(m, "protocol.repeat");
    repeat->setAttr("site", mlir::StringAttr::get(m.getContext(), "changed"));
  });
  for (auto fixture : {"repeat_nested.zkc", "repeat_affine.zkc"})
    for (bool simplify : {false, true})
      must(compileEntry(
          original(replace(read(fixture), "module sample;", "module m;")),
          {simplify, false}));
  auto conditional = original(
      replace(read("conditional_query.zkc"), "module sample;", "module m;"));
  must(compileEntry(conditional));
  const std::string affine = R"(module m;
struct State:Drop {} fn make()->State{return State{};}
fn identity(x:State)->State{return x;}
fn consume_state(x:State)->(){consume x;return ();}
protocol Run roles(P)(n:index@P)->(){
 let mut state@P=make();
 for _ in 0..n roles(P) max 4 { state=identity(state); }
 let done@P=consume_state(state);return();
}entry Demo=Run;
)";
  must(compileEntry(original(affine)));
  sourceRefuses(replace(affine, "let mut state", "let state"),
                "source.assignment");
  auto subset = replace(source, "0..n roles(P, V)", "0..n roles(V)");
  sourceRefuses(subset, "source.roles");
  auto empty = original(R"(module m;
fn truth()->bool{return true;}
protocol Run roles(P,V)(n:index@V)->(){
 for _ in 0..n roles(V) max 2 {let x@V=truth();}return();
}entry Demo=Run;
)");
  must(compileEntry(empty));
  auto restricted = R"(module m;
math fn truth()->bool{return true;}
protocol Run roles(P,V)(n:index@V)->(){
 for _ in 0..n roles(V) max 2 {
   let literal@V=true;let constant@V=truth();
 }return();
}entry Demo=Run;)";
  must(compileEntry(original(restricted)));
  sourceRefuses(replace(restricted, "literal@V", "literal@P"), "source.roles");
  sourceRefuses(replace(restricted, "constant@V", "constant@P"),
                "source.roles");
  auto nonparticipant = R"(module m;fn truth()->bool{return true;}
protocol Run roles(P,V)(n:index@V)->(){for _ in 0..n roles(V) max 2{let x@P=truth();}return();}entry Demo=Run;)";
  sourceRefuses(nonparticipant, "source.roles");
}

void managedServices() {
  auto source = replace(read("services.zkc"), "module sample;", "module m;");
  auto checked = original(source);
  const auto &protocol = checked.entry().protocol();
  require(protocol.services.size() == 1 && protocol.inputs.size() == 1,
          "managed signature was mixed into data ports");
  for (const auto &operation : protocol.body->operations)
    if (auto *application = std::get_if<ProtocolApplication>(&operation.action))
      require(application->services.size() == 2 &&
                  application->services[0].index ==
                      application->services[1].index,
              "alias manufactured a new service root");
  for (bool simplify : {false, true})
    must(compileEntry(checked, {simplify, false}));
  for (const auto &[from, to, code] :
       std::vector<std::tuple<std::string, std::string, std::string>>{
           {"using(alias, coins)", "using(alias)", "source.service"},
           {"using(alias, coins)", "using(unknown, coins)", "source.name"},
           {"using(alias, coins)", "using(go, coins)", "source.service"},
           {"Random<Fr> @V", "Random<Fr> @(P,V)", "source.service"},
           {"Random<Fr> @V", "Random<Fr> @P", "source.service"},
           {"Random<Fr>", "Random<bool>", "source.service"},
           {"let alias = coins", "let go = coins", "source.shadow"},
           {"let alias = coins", "let alias = go", "source.service"},
           {"let unused = first.draw()", "let unused = first.draw(true)",
            "source.service"},
           {"let unused = first.draw()", "let unused = first.other()",
            "source.service"},
           {"let unused = first.draw()", "let first = first.draw()",
            "source.shadow"},
           {"let unused = first.draw()", "let unused = (first,)",
            "source.name"},
           {"guard @V go", "guard @P go", "source.roles"},
           {"let unused = first.draw()", "let unused = send V -> P(first)",
            "source.service"},
           {"entry Demo = Run;",
            "entry Demo = Run;fn bad(x:Random<Fr>)->(){return ();}",
            "source.name"},
       })
    sourceRefuses(replace(source, from, to), code);
  auto alternate = source + R"(
    domain Small=field("koala-bear");
    entry Other=Draw<Small>;
  )";
  auto project = check(alternate);
  must(prepareOriginal(must(closeEntry(project, "m::Demo"))));
  refuses(closeEntry(project, "m::Other"), "source.service");
  mutation(checked, "unused random occurrence omitted",
           [](auto m) { first(m, "protocol.query")->erase(); });
  mutation(checked, "guard omitted",
           [](auto m) { first(m, "protocol.guard")->erase(); });
  mutation(checked, "same-contract query root changed", [](auto m) {
    auto *query = first(m, "protocol.query");
    query->setOperand(0, query->getBlock()->getArgument(1));
  });
  mutation(checked, "query occurrence changed", [](auto m) {
    first(m, "protocol.query")
        ->setAttr("site", mlir::StringAttr::get(m.getContext(), "changed"));
  });
}
void selectedClosure() {
  auto source = replace(read("application.zkc"), "module sample;", "module m;");
  auto project = check(source);
  const auto definitions = project.declarations().size();
  auto closed = must(closeEntry(project, "m::Demo"));
  auto base = must(prepareOriginal(closed));
  require(closed.entry().target &&
              closed.entry().target->index == closed.protocol().id.index,
          "closed Entry points outside its closed declaration graph");
  require(project.declarations().size() == definitions,
          "Entry closure mutated the definition graph");
  for (const auto &decl : project.declarations())
    require(!decl.origin, "analysis produced a closed instance");
  auto extended =
      original(replace(source, "domain Fr",
                       "math fn unrelated(x:bool)->bool{return x;} domain Fr") +
               "protocol Other roles(P)()->(){return();} entry Extra=Other;");
  require(base.bytes() == extended.bytes(),
          "unrelated declaration changed selected original");
  require(base.identity() == extended.identity(),
          "unrelated declaration changed instance identity");
  require(base.entry().project().capture().identity() !=
              extended.entry().project().capture().identity(),
          "capture stopped binding unselected source");
  must(prepareOriginal(must(closeEntry(project, "m::Demo"))));
  auto privateState = original(R"(module m;
    struct State:Drop {} fn make()->State{return State{};}
    fn discard(state:State)->(){consume state;return ();}
    protocol Create roles(P)()->(state:State@P){let state @P =make();return(state=state);}
    protocol Consume roles(P)(state:State@P)->(){let done @P =discard(state);return();}
    protocol Run roles(P)()->(){let state=Create();let ()=Consume(state);return();}
    entry Demo=Run;
  )");
  must(compileEntry(privateState));
}
void bounds() {
  Limits limits;
  limits.files = 1;
  must(capture({{"m", "module m;", {}}}, {"zkc", limits}));
  refuses(capture({{"m", "module m;", {}}, {"n", "module n;", {}}},
                  {"zkc", limits}),
          "source.limit");
  limits = {};
  limits.fileBytes = 9;
  limits.captureBytes = 9;
  must(capture({{"m", "module m;", {}}}, {"zkc", limits}));
  refuses(capture({{"m", "module m; ", {}}}, {"zkc", limits}), "source.limit");
  limits.fileBytes = 100;
  refuses(capture({{"m", "module m;", {}}, {"n", "module n;", {}}},
                  {"zkc", limits}),
          "source.limit");
  limits = {};
  limits.identifierBytes = 1;
  limits.moduleBytes = 1;
  must(capture({{"m", "module m;", {}}}, {"zkc", limits}));
  refuses(capture({{"mm", "module mm;", {}}}, {"zkc", limits}),
          "source.module");
  limits = {};
  limits.files += 1;
  refuses(checkLimits(limits), "source.limit");
  auto project = check(basic);
  auto selected = must(closeEntry(project, "m::Demo"));
  auto full = must(prepareOriginal(selected));
  for (auto member :
       {&Limits::irBytes, &Limits::interfaceBytes, &Limits::locationBytes}) {
    limits = {};
    auto size = member == &Limits::irBytes ? full.bytes().size()
                : member == &Limits::interfaceBytes
                    ? full.interfaceJson().size()
                    : full.locations().size() * 5 * sizeof(uint64_t);
    limits.*member = size;
    must(prepareOriginal(selected, limits));
    limits.*member = size - 1;
    refuses(prepareOriginal(selected, limits), "source.limit");
  }
  limits = {};
  limits.declarations = project.declarations().size();
  check(basic, limits);
  must(prepareOriginal(must(closeEntry(project, "m::Demo", limits)), limits));
  --limits.declarations;
  sourceRefuses(basic, "source.limit", limits);
  limits = {};
  limits.work = project.checkedWork();
  // Analysis owns this exact boundary. Entry closure has its own phase work.
  check(basic, limits);
  --limits.work;
  sourceRefuses(basic, "source.limit", limits);
  uint64_t tokenCount = project.tokens(ModuleId{0}).size();
  limits = {};
  limits.tokens = tokenCount;
  check(basic, limits);
  --limits.tokens;
  sourceRefuses(basic, "source.limit", limits);
  limits = {};
  limits.operations = 4;
  check(basic, limits);
  --limits.operations;
  sourceRefuses(basic, "source.limit", limits);
  // Native emission counts the module, definition and terminator as well.
  limits = {};
  limits.operations = 6;
  must(prepareOriginal(selected, limits));
  --limits.operations;
  refuses(prepareOriginal(selected, limits), "source.limit");
  limits = {};
  auto symbol = must(encodeSymbol("ab::c"));
  limits.symbolBytes = symbol.size();
  must(encodeSymbol("ab::c", limits));
  --limits.symbolBytes;
  refuses(encodeSymbol("ab::c", limits), "source.limit");
  require(must(encodeSymbol("a_b::c")) != must(encodeSymbol("a::b_c")),
          "symbol collision");
  limits = {};
  limits.tokenBytes = 14;
  check(basic, limits);
  --limits.tokenBytes;
  sourceRefuses(basic, "source.limit", limits);
  limits = {};
  limits.parseDepth = 1;
  sourceRefuses(replace(basic.str(), "x + c", "(x)"), "source.limit", limits);
  limits = {};
  limits.expressionDepth = 1;
  sourceRefuses(basic, "source.limit", limits);
  limits = {};
  limits.importDepth = 0;
  sourceRefuses(basic, "source.limit", limits);
  limits = {};
  limits.callDepth = 0;
  sourceRefuses(basic, "source.limit", limits);
}
} // namespace
int main(int argc, char **argv) {
  InitLLVM initialization(argc, argv);
  stage = "reviewedSourceBoundaries";
  reviewedSourceBoundaries();
  stage = "participantCompletion";
  participantCompletion();
  stage = "distributedRepetition";
  distributedRepetition();
  stage = "managedServices";
  managedServices();
  stage = "selectedClosure";
  selectedClosure();
  stage = "protocolApplications";
  protocolApplications();
  stage = "sourceControls";
  sourceControls();
  stage = "bounds";
  bounds();
  stage = "nameResolution";
  nameResolution();
  stage = "specializationSnapshotBounds";
  specializationSnapshotBounds();
  stage = "semanticDiagnosticLocations";
  semanticDiagnosticLocations();
  stage = "syntaxTreeBounds";
  syntaxTreeBounds();
  stage = "depthAndAggregateBounds";
  depthAndAggregateBounds();
  stage = "reviewControls";
  reviewControls();
  auto algebra = read("algebra.zkc"), transfer = read("transfer.zkc");
  auto captured = must(capture({{"transfer", transfer, "transfer.zkc"},
                                {"algebra", algebra, "algebra.zkc"}}));
  auto checked = must(analyze(captured).checkedProject());
  auto entry = must(closeEntry(checked, "transfer::Demo"));
  auto full = must(prepareOriginal(entry));
  auto reversed = must(capture({{"algebra", algebra, "/elsewhere/a.zkc"},
                                {"transfer", transfer, "/elsewhere/t.zkc"}}));
  require(captured.identity() == reversed.identity(),
          "capture depends on paths or caller order");
  auto spaced = must(capture({{"algebra", "// comment 한글\n" + algebra, {}},
                              {"transfer", "\n  " + transfer, {}}}));
  auto reformatted = must(prepareOriginal(must(
      closeEntry(must(analyze(spaced).checkedProject()), "transfer::Demo"))));
  require(full.bytes() == reformatted.bytes() &&
              captured.identity() != spaced.identity(),
          "spelling changed original semantics or capture lost bytes");
  require(full.locationsIdentity() != reformatted.locationsIdentity(),
          "diagnostic map lost capture binding");
  require(!full.bytes().contains("loc("), "original contains debug locations");
  success(checkInterface(full, full.interfaceJson()));
  for (const auto &key :
       {"entry", "protocol", "capture", "original", "toolchain", "format"}) {
    auto interface = must(json::parse(full.interfaceJson()));
    (*interface.getAsObject())[key] = "wrong";
    std::string text;
    raw_string_ostream(text) << interface;
    refuses(checkInterface(full, text), "source.interface");
  }
  for (StringRef key : {"entry", "entr\\u0079"}) {
    std::string duplicate = "{\"" + key.str() + "\":\"wrong\"," +
                            full.interfaceJson().drop_front().str();
    require(must(json::parse(duplicate)) ==
                must(json::parse(full.interfaceJson())),
            "duplicate-key control would already fail ordinary equality");
    refuses(checkInterface(full, duplicate), "source.interface");
  }
  for (StringRef key : {"name", "type", "roles", "index"}) {
    auto altered = must(json::parse(full.interfaceJson()));
    auto &port = *altered.getAsObject()
                      ->getArray("protocols")
                      ->front()
                      .getAsObject()
                      ->getArray("outputs")
                      ->front()
                      .getAsObject();
    port[key] = "wrong";
    std::string bytes;
    raw_string_ostream(bytes) << altered;
    refuses(checkInterface(full, bytes), "source.interface");
  }
  auto aliasProject = check(basic.str() + "entry Alias=Run;");
  auto selected =
      must(prepareOriginal(must(closeEntry(aliasProject, "m::Demo"))));
  auto alias =
      must(prepareOriginal(must(closeEntry(aliasProject, "m::Alias"))));
  require(selected.bytes() == alias.bytes(), "aliases changed original IR");
  refuses(checkInterface(selected, alias.interfaceJson()), "source.interface");
  auto extra = must(json::parse(full.interfaceJson()));
  (*extra.getAsObject())["clauses"] = json::Array();
  std::string unknown;
  raw_string_ostream(unknown) << extra;
  refuses(checkInterface(full, unknown), "source.interface");
  auto repeated = must(prepareOriginal(entry));
  require(full.bytes() == repeated.bytes() &&
              full.interfaceJson() == repeated.interfaceJson() &&
              full.locationsIdentity() == repeated.locationsIdentity(),
          "repeated compilation identity differs");
  require(must(compileEntry(full)).bytes() ==
              must(compileEntry(repeated)).bytes(),
          "repeated bundle differs");
  auto saved = full.bytes().str();
  mutation(full, "return replaced with local shared input", [](auto module) {
    first(module, "protocol.return")
        ->setOperand(0,
                     first(module, "protocol.restrict_roles", 2)->getResult(0));
  });
  mutation(full, "message pairs reordered", [](auto module) {
    auto *a = first(module, "protocol.exchange"),
         *b = first(module, "protocol.exchange", 1);
    auto *restriction = b->getNextNode();
    b->moveBefore(a);
    restriction->moveAfter(b);
  });
  mutation(full, "helper target", [](auto module) {
    auto *call = first(module, "func.call");
    call->setAttr("callee", mlir::FlatSymbolRefAttr::get(module.getContext(),
                                                         "s7_algebra5_other"));
  });
  mutation(full, "helper operand order", [](auto module) {
    auto *call = first(module, "func.call");
    auto a = call->getOperand(0), b = call->getOperand(1);
    call->setOperands({b, a});
  });
  mutation(full, "combined helper edit", [](auto module) {
    auto *call = first(module, "func.call");
    call->setAttr("callee", mlir::FlatSymbolRefAttr::get(module.getContext(),
                                                         "s7_algebra5_other"));
    auto a = call->getOperand(0), b = call->getOperand(1);
    call->setOperands({b, a});
  });
  mutation(full, "commutative rewrite", [](auto module) {
    auto *op = first(module, "algebra.field_add");
    auto a = op->getOperand(0), b = op->getOperand(1);
    op->setOperands({b, a});
  });
  mutation(full, "duplicate receive", [](auto module) {
    auto *ret = first(module, "protocol.return");
    ret->setOperand(1, ret->getOperand(0));
  });
  mutation(full, "swapped receives", [](auto module) {
    auto *ret = first(module, "protocol.return");
    auto a = ret->getOperand(0), b = ret->getOperand(1);
    ret->setOperand(0, b);
    ret->setOperand(1, a);
  });
  mutation(full, "sender payload changed", [](auto module) {
    auto *op = first(module, "protocol.exchange", 1);
    op->setOperand(0, first(module, "protocol.exchange")->getOperand(0));
  });
  mutation(full, "site changed", [](auto module) {
    first(module, "protocol.exchange")
        ->setAttr("site",
                  mlir::StringAttr::get(module.getContext(), "different"));
  });
  mutation(full, "unused operation inserted", [](auto module) {
    auto *op = first(module, "algebra.field_add");
    auto *clone = op->clone();
    mlir::OpBuilder builder(op);
    builder.insert(clone);
  });
  mutation(full, "receiver restriction omitted", [](auto module) {
    auto *op = first(module, "protocol.restrict_roles");
    op->getResult(0).replaceAllUsesWith(op->getOperand(0));
    op->erase();
  });
  mutation(full, "explicit restriction omitted", [](auto module) {
    auto *op = first(module, "protocol.restrict_roles", 2);
    op->getResult(0).replaceAllUsesWith(op->getOperand(0));
    op->erase();
  });
  mutation(full, "wrong subtraction", [](auto module) {
    auto *op = first(module, "algebra.field_subtract");
    mlir::OpBuilder b(op);
    mlir::OperationState state(op->getLoc(), "algebra.field_add");
    state.addOperands(op->getOperands());
    state.addTypes(op->getResultTypes());
    auto *sum = b.create(state);
    op->getResult(0).replaceAllUsesWith(sum->getResult(0));
    op->erase();
  });
  require(full.bytes() == saved, "caller mutation changed retained original");
  for (bool simplify : {false, true})
    for (bool release : {false, true}) {
      auto run = must(compileEntry(full, {simplify, release}));
      require(run.original().identity() == full.identity(),
              "compile changed original");
      require(
          mlir::succeeded(mlir::verify(
              std::get<zkc::CompiledRun>(run.artifact()).compilation.module())),
          "invalid final IR");
    }
  mlir::registerAsmPrinterCLOptions();
  const char *arguments[] = {"language-test", "--mlir-print-debuginfo",
                             "--mlir-print-local-scope",
                             "--mlir-print-value-users"};
  require(cl::ParseCommandLineOptions(4, arguments),
          "printer flag setup failed");
  auto embedded = must(prepareOriginal(entry));
  require(embedded.bytes() == full.bytes() &&
              embedded.locationsIdentity() == full.locationsIdentity(),
          "host printer preferences changed source identity or positions");
  outs() << "fresh source admission, independent correspondence, limits and "
            "Entry compilation passed\n";
}
