#include "zkc/Compiler/Language.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>

using namespace llvm;
using namespace zkc::language;
namespace {
void require(bool ok, StringRef message) {
  if (!ok) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T must(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
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
  refuses(analyze(must(capture({{"m", source.str(), "m.zkc"}})), limits)
              .checkedProject(),
          code);
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
  zkc::registerNativeDialects(registry);
  mlir::MLIRContext context(registry);
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
  require(bool(module), "original parsing failed");
  mutate(*module);
  require(mlir::succeeded(mlir::verify(*module)),
          "mutation failed IR admission instead of correspondence");
  auto result = compareOriginal(original.entry().project(), *module);
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
           {replace(basic.str(), "let a", "let x"), "source.shadow"},
           {replace(basic.str(), "let a", "let Fr"), "source.shadow"},
           {replace(basic.str(), "send P -> V", "send P -> P"), "source.send"},
           {replace(basic.str(), "send P -> V", "send V -> P"), "source.roles"},
           {replace(basic.str(), "return (r = received)",
                    "return (r = received, r = received)"),
            "source.return"},
           {replace(basic.str(), "return (r = received)", "return ()"),
            "source.return"},
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
            "source.call"},
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
  for (StringRef feature :
       {"local", "service", "predicate", "relation", "construct"})
    sourceRefuses("module m; " + feature.str() + " X;", "source.unsupported");
  sourceRefuses("module m; math fn f<F>() -> bool {return true;}",
                "source.unsupported");
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
               "Demo=Small;";
  auto failure = prepareOriginal(must(closeEntry(check(expansion), "m::Demo")));
  require(!failure, "unused target expansion was not checked");
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
  zkc::registerNativeDialects(registry);
  mlir::MLIRContext context(registry);
  mlir::ScopedDiagnosticHandler silence(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  auto module = mlir::parseSourceString<mlir::ModuleOp>(full.bytes(), &context);
  require(bool(module), "missing original");
  first(*module, "protocol.func")
      ->setAttr("roles", mlir::StringAttr::get(&context, "bad"));
  refuses(compareOriginal(full.entry().project(), *module), "target.admission");
  auto withUnused = original(
      basic.str() + "math fn unused(x:bool)->bool{let y=x==x;return x;}");
  auto identityHelper =
      original(basic.str() + "math fn unused(x:bool)->bool{return x;}");
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
    refuses(compareOriginal(identityHelper.entry().project(), *candidate),
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
  mutation(withUnused, "unused helper omitted",
           [](auto m) { first(m, "func.func")->erase(); });
  mutation(withUnused, "unused operation omitted",
           [](auto m) { first(m, "arith.cmpi")->erase(); });
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
  --limits.declarations;
  sourceRefuses(basic, "source.limit", limits);
  limits = {};
  limits.work = project.checkedWork();
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
  limits.operations = 2;
  check(basic, limits);
  --limits.operations;
  sourceRefuses(basic, "source.limit", limits);
  // The emitter additionally accounts for the receiver restriction.
  limits = {};
  limits.operations = 3;
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
int main() {
  sourceControls();
  bounds();
  depthAndAggregateBounds();
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
    auto &port =
        *altered.getAsObject()->getArray("outputs")->front().getAsObject();
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
  require(must(compileEntry(full)).run().bundle ==
              must(compileEntry(repeated)).run().bundle,
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
      require(mlir::succeeded(mlir::verify(run.run().compilation.module())),
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
