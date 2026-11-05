#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/SourceCorrespondence.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Companions.h"
#include "zkc/Language/InspectionData.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject checked(StringRef code) {
  CaptureOptions options;
  options.format = "zkc-layout";
  return take(analyze(take(capture({{"m", code.str(), "record-transport.zkc"}},
                                   options)))
                  .checkedProject());
}
void original(StringRef code,
              function_ref<void(const ClosedEntry &, mlir::ModuleOp)> test) {
  auto project = checked(code);
  auto entry = take(closeNativeRun(project, "m::Run"));
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto bytes = take(emitOriginal(entry, context));
  auto candidate = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(candidate), "record source original did not parse");
  take(compareOriginal(entry, *candidate));
  require(mlir::succeeded(admitStage(*candidate)),
          "record source original failed native stage admission");
  test(entry, *candidate);
}
std::string digest(StringRef value) {
  return toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
}
CheckedProject check(std::vector<SourceBuffer> sources,
                     StringRef format = "zkc") {
  CaptureOptions options;
  options.format = format.str();
  return take(
      analyze(take(capture(std::move(sources), options))).checkedProject());
}
// Published nominal identities bind the defining source revision: equal paths
// from different source bytes differ, while unrelated client edits, lookup
// keys, instance symbols and companion keys stay put.
constexpr StringLiteral dependency =
    "module dep;pub fn f(x:bool)->bool{return x;}";
constexpr StringLiteral library = R"(module lib;
pub struct Secret {pub value:bool}
pub struct Box<T:Type> {pub value:bool}
pub fn g(x:bool)->bool{return ::dep::f(x);}
pub fn same<T:Type+Copy+Drop>(x:T)->T{return x;}
)";
constexpr StringLiteral client = R"(module client;
struct A{}
struct B{}
protocol Run roles(P,V)(secret:lib::Secret@P,a:lib::Box<A>@P,
    b:lib::Box<B>@P)->(ok:bool@V){
  let kept @P = lib::same(secret);
  let ok@V=send P->V(lib::g(kept.value));
  return(ok=ok);
}
)";
std::vector<SourceBuffer> clientCapture(StringRef extra = {},
                                        StringRef dependencyText = dependency,
                                        StringRef libraryText = library) {
  return {{"client", (client + extra).str(), "client.zkc"},
          {"dep", dependencyText.str(), "dep.zkc"},
          {"lib", libraryText.str(), "lib.zkc"}};
}
/// The published facts of one compiled capture.
struct Published {
  /// Input port name to its published schema identity.
  std::map<std::string, std::string> identities;
  std::string protocol;
  std::vector<std::string> instances;
};
Published publish(std::vector<SourceBuffer> sources) {
  auto project = check(std::move(sources));
  auto closed = take(closeSubject(project, "client::Run"));
  auto original = take(prepareOriginal(closed));
  auto document = take(json::parse(original.interfaceJson()));
  Published result;
  const auto &protocol =
      *(*document.getAsObject()->getArray("protocols"))[0].getAsObject();
  result.protocol = protocol.getString("symbol")->str();
  for (const auto &port : *protocol.getArray("inputs")) {
    const auto &object = *port.getAsObject();
    result.identities[object.getString("name")->str()] =
        object.getObject("schema")->getString("identity")->str();
  }
  auto instances = take(sourceInstancesData(closed, Limits{}));
  for (const auto &item : *instances.getAsObject()->getArray("instances"))
    result.instances.push_back(item.getAsObject()->getString("symbol")->str());
  return result;
}
/// Neither the placeholder frame nor its hex encoding may be published.
void requireNoPlaceholder(StringRef bytes, StringRef what) {
  std::string placeholder(64, '-');
  require(!bytes.contains(placeholder) &&
              !bytes.contains(toHex(placeholder, true)),
          ("a checking-phase authority placeholder reached the " + what).str());
}
void revisionBoundIdentities(Cases &cases) {
  cases.run("a library nominal keeps its identity across clients", [] {
    auto first = publish(clientCapture());
    auto second =
        publish(clientCapture("fn unrelated(x:bool)->bool{return x;}"));
    require(first.identities.at("secret") == second.identities.at("secret"),
            "an unrelated client declaration changed a library nominal");
    require(first.identities.at("a") != first.identities.at("b"),
            "phantom arguments no longer distinguish nominal instances");
  });
  cases.run("a homonymous nominal from other library bytes differs", [] {
    auto base = publish(clientCapture());
    auto other = publish(clientCapture(
        {}, dependency, (library + "pub fn k(x:bool)->bool{return x;}").str()));
    require(base.identities.at("secret") != other.identities.at("secret"),
            "equal paths from different library bytes share an identity");
  });
  cases.run("a changed private dependency changes the library nominal", [] {
    auto base = publish(clientCapture());
    auto changed = publish(
        clientCapture({}, "module dep;pub fn f(x:bool)->bool{return !x;}"));
    require(base.identities.at("secret") != changed.identities.at("secret"),
            "a changed private dependency kept the library identity");
  });
  cases.run("a comment changes identities, not symbols or companion keys", [] {
    auto base = publish(clientCapture());
    auto commented =
        publish(clientCapture({}, dependency, (library + "// note\n").str()));
    require(base.identities.at("secret") != commented.identities.at("secret"),
            "a comment in the defining unit kept the nominal identity");
    require(base.protocol == commented.protocol &&
                base.instances == commented.instances &&
                base.instances.size() > 1,
            "a comment changed instance symbols");
    for (unsigned i = 0; i < base.instances.size(); ++i)
      require(
          take(companionIdentity("client::Run", StringRef(base.instances[i]),
                                 ObligationRole::Postcondition, {}, 0)) ==
              take(companionIdentity("client::Run",
                                     StringRef(commented.instances[i]),
                                     ObligationRole::Postcondition, {}, 0)),
          "a comment changed a companion key");
  });
  cases.run("checking-phase placeholders reach no output", [] {
    auto project = check({{"m", R"(module m;
#[affine] struct Ticket{}
struct Pair{pub a:bool,pub b:bool}
enum Choice{Yes(bool),No()}
type S<T:Type+Copy+Drop>=builtin("sequence",T);
protocol Run roles(P,V)(t:Ticket@P,c:Choice@P,s:S<Pair>@P)->(ok:bool@V){
  let ok@V=send P->V(true);return(ok=ok);}
)",
                           "m.zkc"}});
    auto closed = take(closeSubject(project, "m::Run"));
    auto original = take(prepareOriginal(closed));
    requireNoPlaceholder(original.bytes(), "native module");
    requireNoPlaceholder(original.interfaceJson(), "interface");
    requireNoPlaceholder(take(exportSourceCorrespondence(original)),
                         "source correspondence");
    // The provisional frame has the final frame's width, so every byte-limit
    // decision taken during checking equals the final one.
    Layouts layouts(closed);
    for (StringRef path : {"m::Ticket", "m::Pair", "m::Choice"}) {
      Type type(path == "m::Choice" ? Type::Kind::Variant : Type::Kind::Record,
                path.str());
      auto final = take(canonicalTypeKey(type, [&](StringRef path) {
        return sourceAuthority(project, path);
      }));
      auto provisional = take(canonicalTypeKey(
          type, [&](StringRef path) -> Expected<std::optional<std::string>> {
            auto authority = sourceAuthority(project, path);
            if (!authority || !*authority)
              return authority;
            return std::optional<std::string>(std::string(64, '-'));
          }));
      require(final.size() == provisional.size() && final != provisional,
              "provisional and final authority frames differ in width");
      auto layout = take(layouts.get(type));
      require(layout->identity.key == final &&
                  layout->identity.digest == digest(final) &&
                  layout->identity.key != typeIdentity(type),
              "a layout lacks its revision-bound identity");
    }
  });
  cases.run("a canonical key past the nominal byte limit refuses", [] {
    // Each authored nominal node adds a 67-byte authority frame, so a phantom
    // argument of 2,048 nominals fits as a lookup key, even hex-encoded in the
    // native descriptor, but not as a canonical key. The type is far inside
    // typeDepth and has one leaf. Complete message-payload admission observes
    // the layout during checking and refuses: provisional authority frames
    // have the same width as final frames.
    std::string row = "(", rows = "(";
    for (unsigned i = 0; i < 64; ++i)
      row += i ? ",A" : "A";
    row += ")";
    for (unsigned i = 0; i < 32; ++i)
      rows += (i ? "," : "") + row;
    rows += ")";
    auto source = "module m;struct A{}enum Choice<T:Type>{Only()}"
                  "type Wide=Choice<" +
                  rows +
                  ">;protocol Run roles(P,V)(x:Wide@P)->(r:Wide@V)"
                  "{let y=send P->V(x);return y;}";
    Type inner(Type::Kind::Tuple), outer(Type::Kind::Tuple);
    inner.arguments.assign(64, Type(Type::Kind::Record, "m::A"));
    outer.arguments.assign(32, inner);
    Type wide(Type::Kind::Variant, "m::Choice");
    wide.arguments = {outer};
    auto authored = [](StringRef) -> Expected<std::optional<std::string>> {
      return std::optional<std::string>(std::string(64, '0'));
    };
    require(typeIdentity(wide).size() <
                    zkc::protocol::VariantSpellingBytes / 4 &&
                take(canonicalTypeKey(wide, authored)).size() >
                    zkc::protocol::VariantSpellingBytes / 2,
            "the limit fixture does not separate the two keys");
    auto captured = take(capture({{"m", source, "m.zkc"}}));
    refuses(analyze(captured).checkedProject(), "source.limit");
  });
  cases.run("the interface reader recomputes identities over the carrier", [] {
    auto project = check({{"m", R"(module m
struct Payload roles(P,V):
    pub value: index @(P,V)
pub protocol Run roles(P,V)(state: Payload roles(P,V)) -> Payload roles(P,V):
    return state
)",
                           "m.zkc"}},
                         "zkc-layout");
    auto original =
        take(prepareOriginal(take(closeSubject(project, "m::Run"))));
    take(readInterface(original.bytes(), original.interfaceJson()));
    auto revision = *take(sourceAuthority(project, "m::Payload"));
    require(StringRef(original.bytes()).contains("\"" + revision + "\""),
            "the retained carrier lacks the record's authority row");
    auto mutate = [&](StringRef replacement) {
      std::string bytes = original.bytes().str();
      auto at = bytes.find("\"" + revision + "\"");
      bytes.replace(at, revision.size() + 2, replacement.str());
      auto document = take(json::parse(original.interfaceJson()));
      (*document.getAsObject())["original"] = digest(bytes);
      return readInterface(bytes, zkc::printJson(document));
    };
    refuses(mutate("\"" + digest("another revision") + "\""),
            "source.interface");
    refuses(mutate("unit"), "source.interface");
  });
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "distributed payload passage compares actual equal-typed operands", [] {
        original(
            R"(struct State roles(P, V):
    pub left: index @P
    pub right: index @P
    pub empty: () @V
protocol read roles(P, V)(state: State roles(P, V)) -> index @P:
    return state.left
pub protocol Run roles(P, V)() -> index @P:
    state = State roles(P, V) {right: 2, empty: (), left: 1}
    result <- state.read()
    return result
)",
            [](const ClosedEntry &entry, mlir::ModuleOp candidate) {
              unsigned changed = 0;
              candidate.walk([&](mlir::Operation *operation) {
                if (operation->getName().getStringRef() != "protocol.apply")
                  return;
                require(operation->getNumOperands() == 2 &&
                            operation->getOperand(0).getType() ==
                                operation->getOperand(1).getType(),
                        "record payload fixture has unexpected ABI");
                auto first = operation->getOperand(0);
                operation->setOperand(0, operation->getOperand(1));
                operation->setOperand(1, first);
                ++changed;
              });
              require(
                  changed == 1 && mlir::succeeded(admitStage(candidate)),
                  "equal-role payload mutation should remain natively formed");
              refuses(compareOriginal(entry, candidate),
                      "source.correspondence");
            });
      });
  cases.run(
      "empty restricted record keeps every role-local custody fragment", [] {
        original(
            R"(#[linear]
struct Ticket roles(P, V):
protocol forward roles(P, V)(ticket: Ticket roles(P, V)) -> Ticket roles(P, V):
    return ticket
pub protocol Run roles(P, V)() -> bool @V:
    ticket <- Ticket roles(P, V) {}
    next <- ticket.forward()
    empty <- unpack(next)
    return true
)",
            [](const ClosedEntry &entry, mlir::ModuleOp candidate) {
              unsigned applications = 0, localCalls = 0;
              candidate.walk([&](mlir::Operation *operation) {
                if (operation->getName().getStringRef() ==
                    "protocol.local_call")
                  ++localCalls;
                if (operation->getName().getStringRef() != "protocol.apply")
                  return;
                require(operation->getNumOperands() == 2 &&
                            operation->getNumResults() == 2,
                        "empty record lost distinct native custody fragments");
                operation->setOperand(1, operation->getOperand(0));
                ++applications;
              });
              require(applications == 1 && localCalls == 4,
                      "empty custody creation or destruction was erased");
              refuses(compareOriginal(entry, candidate), "target.admission");
            });
      });
  cases.run("qualified installed unpack retains distributed field placements",
            [] {
              original(R"(#[linear]
struct Ticket roles(P, V):
    pub value: index @P
    pub empty: () @V
pub protocol Run roles(P, V)() -> index @P:
    ticket <- Ticket roles(P, V) {value: 7, empty: ()}
    fields <- zkc::records::unpack(ticket)
    return fields.0
)",
                       [](const ClosedEntry &, mlir::ModuleOp) {});
            });
  cases.run("authored unpack spelling keeps its protocol target", [] {
    original(R"(struct State roles(P, V):
    pub value: index @P
protocol unpack roles(P, V)(state: State roles(P, V)) -> index @P:
    return 9
pub protocol Run roles(P, V)() -> index @P:
    state = State roles(P, V) {value: 7}
    result <- unpack(state)
    return result
)",
             [](const ClosedEntry &, mlir::ModuleOp candidate) {
               unsigned calls = 0;
               candidate.walk([&](mlir::Operation *operation) {
                 calls +=
                     operation->getName().getStringRef() == "protocol.apply";
               });
               require(calls == 1,
                       "authored unpack was intercepted by its spelling");
             });
  });
  cases.run("two holders retain distinct anchors across a nested record", [] {
    original(
        R"(domain F = field("bls12-381.fr")
type Vec = builtin("vector", F)
type Kind = builtin("oracle.table", F, 16)
type O = builtin("oracle", Kind)
struct Pair roles(A, B, V):
    pub left: O @A -> V
    pub right: O @B -> V
struct State roles(A, B, V):
    pub pair: Pair roles(B, A, V)
protocol read roles(A, B, V)(state: State roles(A, B, V)) -> F @V:
    word = state.pair.right
    answer <- query word at 0
    return answer
pub protocol Run roles(P, Q, V)(xs: Vec @P, ys: Vec @Q) -> F @V:
    first <- send xs from P to V as oracle<Kind>
    second <- send ys from Q to V as oracle<Kind>
    pair = Pair roles(P, Q, V) {left: first, right: second}
    state = State roles(Q, P, V) {pair: pair}
    answer <- state.read()
    return answer
)",
        [](const ClosedEntry &entry, mlir::ModuleOp candidate) {
          unsigned applications = 0;
          candidate.walk([&](mlir::Operation *operation) {
            if (operation->getName().getStringRef() != "protocol.apply")
              return;
            require(operation->getNumOperands() == 4,
                    "two holders did not retain two independent native pairs");
            require(operation->getOperand(1).getType() ==
                        operation->getOperand(3).getType(),
                    "anchor fixture does not have equal static kinds");
            auto first = operation->getOperand(1);
            operation->setOperand(1, operation->getOperand(3));
            operation->setOperand(3, first);
            ++applications;
          });
          require(applications == 1, "missing nested record application");
          refuses(compareOriginal(entry, candidate), "target.admission");
        });
  });
  revisionBoundIdentities(cases);
  return cases.result();
}
