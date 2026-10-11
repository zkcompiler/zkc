#include "mlir/IR/AttrTypeSubElements.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "zkc/Translation/Packing.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>
using namespace llvm;
using namespace zkc::language;
namespace {
using zkc::test::require;
template <class T> T must(Expected<T> value) {
  return zkc::test::take(std::move(value));
}
CheckedProject check(StringRef source, const Limits &limits = {}) {
  return must(analyze(must(capture({{"m", source.str(), "types.zkc"}})), limits)
                  .checkedProject());
}
void refuses(StringRef source, StringRef code, const Limits &limits = {}) {
  auto value =
      analyze(must(capture({{"m", source.str(), "types.zkc"}})), limits)
          .checkedProject();
  if (value) {
    errs() << "unexpected acceptance: " << source << '\n';
    throw std::runtime_error("source refusal failed");
  }
  auto message = toString(value.takeError());
  if (!namesIdentifier(message, code)) {
    errs() << "expected " << code << ", got " << message << " in " << source
           << '\n';
    throw std::runtime_error("source refusal failed");
  }
}
void closureRefuses(StringRef source, StringRef code,
                    const Limits &limits = {}) {
  auto project = check(source, limits);
  auto selected = closeEntry(project, "m::Demo", limits);
  require(!selected, "Entry closure unexpectedly accepted");
  auto message = toString(selected.takeError());
  require(namesIdentifier(message, code), message);
}
CheckedOriginal original(StringRef source) {
  return must(prepareOriginal(must(closeEntry(check(source), "m::Demo"))));
}
mlir::Operation *first(mlir::ModuleOp module, StringRef name) {
  mlir::Operation *found = nullptr;
  module.walk([&](mlir::Operation *op) {
    if (!found && op->getName().getStringRef() == name)
      found = op;
  });
  require(found, "missing mutation target");
  return found;
}
void mutation(const CheckedOriginal &source,
              const std::function<void(mlir::ModuleOp)> &edit) {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
  require(bool(module), "cannot parse original");
  edit(*module);
  require(succeeded(mlir::verify(*module)),
          "mutation must remain valid native IR");
  auto comparison = compareOriginal(source.entry(), *module);
  require(!comparison, "mutation escaped correspondence");
  require(namesIdentifier(toString(comparison.takeError()),
                          "source.correspondence"),
          "wrong mutation refusal phase");
}
const std::string prefix = "module m;domain Fr=field(\"bls12-381.fr\");\n";
const std::string unit = "protocol Run roles(P)()->(){return();}run Demo=Run;";

const std::string sequence = R"(
type Sequence<T:Type+Copy+Drop> = builtin("sequence",T);
fn empty<T:Type+Copy+Drop>()->Sequence<T> = primitive("sequence.empty");
fn append<T:Type+Copy+Drop>(xs:Sequence<T>,x:T)->Sequence<T> = primitive("sequence.append");
fn get<T:Type+Copy+Drop>(xs:Sequence<T>,i:index)->T = primitive("sequence.at");
fn length<T:Type+Copy+Drop>(xs:Sequence<T>)->index = primitive("sequence.length");
fn roundtrip<T:Type+Copy+Drop>(x:T)->T {
  let xs=append(empty<T>(),x); return get(xs,0);
}
)";
void product(const std::string &type) {
  auto source = original(prefix + sequence + R"(
struct Pair<F:Field>{pub first:F,pub second:F}
struct Nested{pub pair:Pair<Fr>,pub array:[(Fr,bool);2]}
struct Empty{}
enum Choice{Some(Fr),None()}
protocol Run roles(P)(x:)" +
                         type + R"(@P)->(r:)" + type + R"(@P){
  let r @P =roundtrip(x);return(r=r);
}run Demo=Run;
)");
  must(compileEntry(source));
}
void mutations() {
  auto source = original(prefix + sequence + R"(
struct Pair{pub first:Fr,pub second:Fr}
protocol Run roles(P)(x:Pair@P)->(r:Pair@P){
  let r @P =roundtrip(x);return(r=r);
}run Demo=Run;
)");
  require(source.bytes().contains("local.variant_inject") &&
              source.bytes().contains("local.match"),
          "missing explicit packing bridge");
  mutation(source, [](auto module) {
    auto *pack = first(module, "local.variant_inject");
    auto a = pack->getOperand(0), b = pack->getOperand(1);
    pack->setOperand(0, b);
    pack->setOperand(1, a);
  });
  mutation(source, [](auto module) {
    auto *unpack = first(module, "local.match");
    auto &yield = unpack->getRegion(0).front().back();
    auto a = yield.getOperand(0), b = yield.getOperand(1);
    yield.setOperand(0, b);
    yield.setOperand(1, a);
  });
  mutation(source, [](auto module) {
    auto *unpack = first(module, "local.match");
    // Change an actual result use, preserving the native function type.
    auto *ret = unpack->getNextNode();
    require(ret && ret->getNumOperands() == 2, "missing unpack result use");
    ret->setOperand(0, unpack->getResult(1));
    ret->setOperand(1, unpack->getResult(0));
  });
  mutation(source, [](auto module) {
    auto oldType =
        first(module, "local.variant_inject")->getResult(0).getType();
    auto old = must(zkc::protocol::encodeBoundType(oldType, false)).spelling();
    auto descriptor = zkc::protocol::decodeVariant(old);
    require(bool(descriptor), "missing packed descriptor");
    descriptor->nominal = json::Array{"another.nominal.record"};
    auto encoded = zkc::protocol::encodeVariant(*descriptor);
    require(bool(encoded), "cannot encode replacement nominal");
    auto replacement = zkc::protocol::decodeBoundType(
        module.getContext(),
        must(zkc::protocol::parseBoundType(*encoded, false)));
    mlir::AttrTypeReplacer replacer;
    replacer.addReplacement([&](mlir::Type type) -> std::optional<mlir::Type> {
      if (type == oldType)
        return replacement;
      return std::nullopt;
    });
    replacer.addReplacement(
        [&](mlir::StringAttr value) -> std::optional<mlir::Attribute> {
          if (value.getValue() == old)
            return mlir::StringAttr::get(module.getContext(), *encoded);
          return std::nullopt;
        });
    replacer.recursivelyReplaceElementsIn(module, true, false, true);
  });
}
void identities() {
  auto project = check(prefix + R"(
struct Pair<F:Field>{pub first:F,pub second:F}
struct Other{pub first:Fr,pub second:Fr}
struct Phantom<T:Type>{pub value:bool}
)" + unit);
  Layouts layouts(project);
  Type pair(Type::Kind::Record, "m::Pair");
  pair.arguments = {Type(Type::Kind::Field, "bls12-381.fr")};
  auto packed = must(layouts.packed(pair));
  require(packed.product && packed.flat->leaves.size() == 2,
          "ordinary product ABI changed");
  auto descriptor = zkc::protocol::decodeVariant(packed.carrier.spelling());
  require(descriptor && descriptor->alternatives.size() == 1 &&
              descriptor->alternatives[0].payload.size() == 2,
          "packed product descriptor differs");
  auto other = must(layouts.packed(Type(Type::Kind::Record, "m::Other")));
  require(packed.carrier.spelling() != other.carrier.spelling(),
          "nominal record identity erased");
  pair.arguments = {Type(Type::Kind::Field, "koala-bear")};
  require(packed.carrier.spelling() !=
              must(layouts.packed(pair)).carrier.spelling(),
          "generic identity erased");
  Type phantom(Type::Kind::Record, "m::Phantom");
  phantom.arguments = {Type{}};
  auto firstPhantom = must(layouts.packed(phantom));
  phantom.arguments = {Type(Type::Kind::Index)};
  auto secondPhantom = must(layouts.packed(phantom));
  require(firstPhantom.carrier.spelling() != secondPhantom.carrier.spelling(),
          "phantom static identity erased despite equal payloads");
  Type oversized(Type::Kind::Array);
  oversized.arguments = {Type{}};
  oversized.dimension = Natural::constant(129);
  zkc::test::refuses(layouts.packed(oversized), "source.limit");
}

void kernelProducts() {
  auto source = original(prefix + R"(
    type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
    fn singleton<T:Type+Copy+Drop>(x:T)->Sequence<T>{
      let empty=kernel<T>("sequence.empty");
      return kernel<T>("sequence.append",empty,x);
    }
    fn first<T:Type+Copy+Drop>(xs:Sequence<T>)->T{return kernel<T>("sequence.at",xs,0);}
    struct Pair{pub left:Fr,pub right:Fr}
    protocol Run roles(P,V)(x:Pair@P)->(r:Pair@V){
      let xs @P =singleton(x);let ys=send P->V(xs);
      let r @V =first(ys);return(r=r);
    }run Demo=Run;
  )");
  must(compileEntry(source));
  auto unitSource = original(prefix + sequence + R"(
    protocol Run roles(P)()->(){let value @P =roundtrip(());return();}run Demo=Run;
  )");
  mutation(unitSource,
           [](auto module) { first(module, "local.match")->erase(); });
}
void authority() {
  const std::string lib = R"(module lib;
    #[sealed] pub struct Secret {pub value:bool}
    pub struct Hidden {value:bool}
    pub struct Public {pub first:bool,pub second:bool}
    pub type Alias=Public;
    pub fn make(x:bool)->Secret{return Secret{value:x};}
    pub fn open(x:Secret)->bool{let fields=unpack(x);return fields.0;}
    pub fn hidden(x:bool)->Hidden{return Hidden{value:x};}
  )";
  auto project = [&](StringRef body) {
    return analyze(must(capture(
                       {{"lib", lib, "lib.zkc"},
                        {"m", "module m;" + sequence + body.str(), "m.zkc"}})))
        .checkedProject();
  };
  auto selected = must(project(R"(
    fn work(x:bool)->bool{return lib::open(roundtrip(lib::make(x)));}
    protocol Run roles(P)(x:bool@P)->(r:bool@P){let r @P =work(x);return(r=r);}
    run Demo=Run;
  )"));
  must(compileEntry(
      must(prepareOriginal(must(closeEntry(selected, "m::Demo"))))));
  for (
      auto body :
      {R"(fn bad(x:lib::Secret)->bool{let item=roundtrip(x);return item.value;})",
       R"(fn bad(x:lib::Hidden)->bool{let item=roundtrip(x);return item.value;})",
       R"(fn bad(x:bool)->Sequence<lib::Secret>{return append(empty<lib::Secret>(),lib::Secret{value:x});})"}) {
    auto checked = project(body);
    require(!checked, "sequence leaked private source authority");
    require(namesIdentifier(toString(checked.takeError()), "source.private"),
            "wrong constructor/field refusal");
  }
  auto alias = must(project(R"(
    fn work(x:lib::Public)->lib::Alias{return get<lib::Alias>(append(empty<lib::Public>(),x),0);}
    protocol Run roles(P)(x:lib::Public@P)->(r:lib::Alias@P){let r @P =work(x);return(r=r);}
    run Demo=Run;
  )"));
  must(compileEntry(must(prepareOriginal(must(closeEntry(alias, "m::Demo"))))));
}

void mathematicalPacking() {
  auto project = check(prefix + unit);
  Layouts layouts(project);
  Type pair(Type::Kind::Tuple);
  pair.arguments = {Type{}, Type{}};
  auto packed = must(layouts.packed(pair));
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = mlir::parseSourceString<mlir::ModuleOp>(R"(
    module { func.func @bridge(%a:i1,%b:i1)->(i1,i1) {
      return %a,%b : i1,i1
    }}
  )",
                                                        &context);
  require(bool(module), "cannot parse mathematical bridge");
  auto *ret = first(*module, "func.return");
  mlir::OpBuilder builder(ret);
  auto value = must(emitPack(builder, ret->getLoc(), packed, ret->getOperands(),
                             PackingMode::Mathematical));
  auto leaves = must(emitUnpack(builder, ret->getLoc(), packed, value,
                                PackingMode::Mathematical));
  ret->setOperands(leaves);
  require(succeeded(mlir::verify(*module)),
          "mathematical packing API emitted invalid data operations");
  require(first(*module, "data.make")->getNumOperands() == 2,
          "mathematical pack arity differs");
  unsigned index = 0;
  module->walk([&](mlir::Operation *op) {
    if (op->getName().getStringRef() == "data.get") {
      require(op->getAttrOfType<mlir::IntegerAttr>("index").getInt() == index,
              "mathematical unpack field order differs");
      require(leaves[index++] == op->getResult(0),
              "mathematical unpack result order differs");
    }
  });
  require(index == 2, "mathematical unpack omitted fields");
  auto wrong =
      emitPack(builder, ret->getLoc(), packed, {}, PackingMode::Mathematical);
  zkc::test::refuses(std::move(wrong), "source.layout");
}
void refusals() {
  refuses(prefix + "type Bad<T:Type>=builtin(\"sequence\",T);" + unit,
          "source.sequence");
  refuses(prefix +
              "#[affine] struct Token {pub value:Fr}type "
              "Bad=builtin(\"sequence\",Token);" +
              unit,
          "source.sequence");
  refuses(prefix +
              "#[linear] struct Token {pub value:Fr}type "
              "Bad=builtin(\"sequence\",Token);" +
              unit,
          "source.sequence");
  refuses(prefix + "type Bad=builtin(\"sequence\",builtin(\"transcript\"));" +
              unit,
          "source.builtin");
  refuses(prefix +
              "type Bad=builtin(\"sequence\",formal(\"polynomial\",Fr,1));" +
              unit,
          "source.builtin");
  refuses(prefix + sequence + R"(
struct Secret{value:Fr}
protocol Relay<T:Type+Copy+Drop+Share+Wire> roles(P,V)(x:T@P)->(r:T@V){let y=send P->V(x);return(r=y);}
run Demo=Relay<Sequence<Secret>>;
)",
          "source.permission");
  closureRefuses(prefix + sequence + R"(
struct Secret{value:Fr}
protocol Run roles(P)(xs:Sequence<Secret>@P)->(){return();}run Demo=Run;
)",
                 "source.ingress");
  refuses(prefix + sequence + R"(
struct A{pub value:Fr}struct B{pub value:Fr}
fn bad(xs:Sequence<A>,x:B)->Sequence<A>{return append(xs,x);}
)" + unit,
          "source.type");
  // An unrelated native Type root retains its existing admission rule.
  refuses(prefix + R"(
struct Secret{pub value:Fr}
fn bad(x:Secret)->Secret{return kernel<Secret>("value.copy",x);}
)" + unit,
          "source.kernel");
}
} // namespace
int main() {
  zkc::test::Cases cases;
  for (const std::string type : {"Pair<Fr>", "Nested", "(Fr,Fr)", "[Fr;2]",
                                 "()", "Empty", "[Fr;0]", "Choice"})
    cases.run("product " + type, [&] { product(type); });
  cases.run("packing mutations", mutations);
  cases.run("generic kernel products and unit mutation", kernelProducts);
  cases.run("nominal layout identities", identities);
  cases.run("private authority and export aliases", authority);
  cases.run("definition refusals", refusals);
  cases.run("mathematical packing API", mathematicalPacking);
  return cases.result();
}
