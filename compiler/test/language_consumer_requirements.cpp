#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(const Twine &source, Limits limits = {}) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "consumer.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return const_cast<Declaration &>(decl);
  throw std::runtime_error("missing declaration " + name.str());
}
void witness(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
void refusesWitness(const CheckedProject &project) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "checked mutation passed source replay");
  require(namesIdentifier(toString(std::move(error)), "source.scoped-witness"),
          "consumer replay returned wrong diagnostic");
}
void closes(const CheckedProject &project, StringRef name = "m::Demo",
            std::vector<Type> arguments = {}) {
  witness(project);
  auto closed = take(closeNativeRun(project, name, {}, std::move(arguments)));
  for (const auto &decl : closed.declarations())
    if (decl.origin)
      require(decl.admissions.empty() && decl.consumerRequirements.empty(),
              "closed specialization retained a conditional requirement");
  take(prepareOriginal(closed));
}
CheckedProject snapshotProject(unsigned clauses, unsigned instances,
                               bool callback = false, unsigned levels = 0) {
  std::string source =
      "use zkc::transport::{NativeMessage}\ndef apply(x: bool, "
      "body: fn(bool) -> bool) -> bool:\n    return body(x)\ndef "
      "keep<N: nat>(x: bool) -> bool where (";
  for (unsigned i = 0; i < clauses; ++i)
    source += (i ? ", " : "") + std::string("NativeMessage(bool)");
  source +=
      callback ? "):\n    return apply(x, fn(y) => y)\n" : "):\n    return x\n";
  if (levels) {
    for (unsigned i = 0; i < levels; ++i) {
      const auto target = i ? "level" + std::to_string(i - 1) : "keep";
      source += "def level" + std::to_string(i) +
                "<N: nat>(x: bool) -> bool:\n"
                "    first = " +
                target +
                "<N * 2>(x)\n"
                "    second = " +
                target +
                "<N * 2 + 1>(x)\n"
                "    return second\n";
    }
    source += "pub protocol Demo roles(P)(x: bool @P) -> bool @P:\n"
              "    result = level" +
              std::to_string(levels - 1) +
              "<0>(x)\n"
              "    return result\n";
    return take(check(source));
  }
  source += "pub protocol Demo roles(P)(x: bool @P) -> bool @P:\n";
  for (unsigned i = 0; i < instances; ++i)
    source += "    value" + std::to_string(i) + " = keep<" + std::to_string(i) +
              ">(x)\n";
  source += "    return value" + std::to_string(instances - 1) + "\n";
  return take(check(source));
}
CheckedProject unusedAdmissionProject() {
  return take(
      check(R"(protocol Unused<T: Type> roles(P, V)(x: T @P) -> T @V where ():
    y <- send x to V
    return y
pub protocol Demo<T: Type> roles(P)(x: bool @P) -> bool @P:
    return x
)"));
}
std::pair<uint64_t, bool> specializeSnapshot(const CheckedProject &project,
                                             uint64_t allowance,
                                             unsigned &copies) {
  // Use the real native specializer with an explicit phase
  // allowance. Public selection also enforces checkedWork, which
  // can be larger than this phase and would hide the boundary under
  // test.
  auto authentic = take(closeNativeRun(project, "m::Demo"));
  std::vector<Declaration> declarations(project.declarations().begin(),
                                        project.declarations().end());
  auto owner = authentic.entry();
  owner.target = named(project, "m::Demo").id;
  declarations.push_back(owner);
  Limits limits;
  limits.work = allowance;
  zkc::language::detail::Work work{limits};
  zkc::language::detail::Work::Scope phase(work,
                                           SourceWorkPhase::Specialization);
  auto error = zkc::language::detail::specialize(declarations, project.assets(),
                                                 work, owner.id);
  copies = llvm::count_if(declarations, [&](const auto &decl) {
    return decl.origin &&
           decl.origin->index == named(project, "m::keep").id.index;
  });
  for (const auto &decl : declarations)
    if (decl.origin)
      require(decl.consumerRequirements.empty() &&
                  decl.consumerRequirements.capacity() == 0 &&
                  decl.admissions.empty() && decl.admissions.capacity() == 0,
              "closed snapshot retained discharged allocation");
  if (error) {
    handleAllErrors(std::move(error), [&](const DiagnosticError &failure) {
      require(failure.diagnostic().code == "source.limit" &&
                  StringRef(failure.diagnostic().message)
                      .contains("in specialization"),
              "snapshot limit missed the real specialization phase");
    });
    return std::make_pair(work.used, false);
  }
  return std::make_pair(work.used, true);
}
const char *relay = R"(use zkc::transport::{NativeMessage}
interface Relay:
    protocol keep<T: Type + Copy + Drop> roles(P, V)(x: T @P) -> T @P effects() where NativeMessage(T)
module SentRelay: Relay:
    protocol keep<U: Type + Copy + Drop> roles(A, B)(x: U @A) -> U @A where NativeMessage(U):
        discarded <- send x to B
        return x
pub protocol Forward<T: Type + Copy + Drop, C: Relay> roles(P, V)(x: T @P) -> T @P where NativeMessage(T):
    result <- C::keep<T>(x) @(P, V)
    return result
)";
} // namespace
int main() {
  Cases cases;
  cases.run("alpha renamed abstract Relay and generic Forward close bool", [] {
    auto project = take(check(
        Twine(relay) + R"(pub protocol Demo roles(P, V)(x: bool @P) -> bool @P:
    result <- Forward<bool, SentRelay>(x) @(P, V)
    return result
)"));
    require(named(project, "m::Relay::keep").consumerRequirements.size() == 1,
            "abstract contract lost explicit consumer identity");
    require(named(project, "m::SentRelay::keep").admissions.size() == 3,
            "consumer expansion lost independent boundary atoms");
    closes(project);
  });
  cases.run("transparent complete record payload", [] {
    closes(take(check(Twine(relay) + R"(struct Packet:
    pub flag: bool
    pub count: index
pub protocol Demo roles(P, V)(x: Packet @P) -> Packet @P:
    result <- Forward<Packet, SentRelay>(x) @(P, V)
    return result
)")));
  });
  cases.run("complete Envelope index and generic caller", [] {
    closes(take(check(R"(use zkc::transport::{NativeMessage}
struct Envelope<T: Type + Copy + Drop>:
    pub tag: bool
    pub payload: T
interface Relay:
    protocol keep<T: Type + Copy + Drop> roles(P, V)(x: Envelope<T> @P) -> Envelope<T> @P effects() where NativeMessage(Envelope<T>)
module Impl: Relay:
    protocol keep<U: Type + Copy + Drop> roles(A, B)(x: Envelope<U> @A) -> Envelope<U> @A where NativeMessage(Envelope<U>):
        discarded <- send x to B
        return x
protocol Forward<T: Type + Copy + Drop, C: Relay> roles(P, V)(x: Envelope<T> @P) -> Envelope<T> @P where NativeMessage(Envelope<T>):
    result <- C::keep<T>(x) @(P, V)
    return result
pub protocol Demo roles(P, V)(x: Envelope<bool> @P) -> Envelope<bool> @P:
    result <- Forward<bool, Impl>(x) @(P, V)
    return result
)")));
  });
  cases.run("broad interface still refuses hidden generic send", [] {
    refuses(check(R"(interface Relay:
    protocol keep<T: Type + Copy + Drop> roles(P, V)(x: T @P) -> T @P effects()
module Impl: Relay:
    protocol keep<U: Type + Copy + Drop> roles(A, B)(x: U @A) -> U @A:
        discarded <- send x to B
        return x
)"),
            "source.conformance");
  });
  cases.run("implementation declared demand cannot prove itself", [] {
    refuses(check(R"(use zkc::transport::{NativeMessage}
interface Relay:
    protocol keep<T: Type + Copy + Drop> roles(P)(x: T @P) -> T @P effects()
module Impl: Relay:
    protocol keep<U: Type + Copy + Drop> roles(A)(x: U @A) -> U @A where NativeMessage(U):
        return x
)"),
            "source.conformance");
  });
  cases.run("weaker implementation retains the interface caller demand", [] {
    auto project = take(check(R"(use zkc::transport::{NativeMessage}
interface Relay:
    protocol keep<T: Type + Copy + Drop> roles(P)(x: T @P) -> T @P effects() where NativeMessage(T)
module Impl: Relay:
    protocol keep<U: Type + Copy + Drop> roles(A)(x: U @A) -> U @A where ():
        return x
protocol Forward<T: Type + Copy + Drop, C: Relay> roles(P)(x: T @P) -> T @P where NativeMessage(T):
    result <- C::keep<T>(x) @P
    return result
pub protocol Demo<T: Type + Copy + Drop> roles(P)(x: T @P) -> T @P:
    result <- Forward<T, Impl>(x) @P
    return result
)"));
    closes(project, "m::Demo", {Type(Type::Kind::Boolean)});
    refuses(closeNativeRun(project, "m::Demo", {}, {Type(Type::Kind::Unit)}),
            "source.message-payload");
  });
  for (StringRef payload : {"()", "[bool; 0]", "Empty"}) {
    cases.run(
        "empty concrete requirement refuses unused declaration " + payload,
        [&] {
          refuses(check("use zkc::transport::{NativeMessage}\nstruct Empty:\n"
                        "protocol unused roles(P)(x: bool @P) -> bool @P where "
                        "NativeMessage(" +
                        payload + "):\n    return x\n"),
                  "source.message-payload");
        });
    cases.run(
        "unused generic demand discharges on closed selection " + payload, [&] {
          auto project =
              take(check("use zkc::transport::{NativeMessage}\nstruct Empty:\n"
                         "pub protocol Demo<T: Type> roles(P)(x: bool @P) -> "
                         "bool @P where NativeMessage(T):\n    return x\n"));
          Type value(Type::Kind::Unit);
          if (payload == "[bool; 0]") {
            value.kind = Type::Kind::Array;
            value.arguments = {Type(Type::Kind::Boolean)};
            value.dimension = Natural::constant(0);
          } else if (payload == "Empty") {
            value.kind = Type::Kind::Record;
            value.domain = "m::Empty";
          }
          refuses(closeNativeRun(project, "m::Demo", {}, {value}),
                  "source.message-payload");
        });
  }
  for (StringRef definition : {"#[sealed]\nstruct Secret:\n    pub bit: bool\n",
                               "struct Secret:\n    bit: bool\n"})
    cases.run(
        "known construction invalidity precedes matching " + definition, [&] {
          refuses(check("use zkc::transport::{NativeMessage}\n" + definition +
                        "interface I:\n    protocol keep roles(P)(x: bool @P) "
                        "-> bool @P effects() where NativeMessage(Secret)\n"),
                  "source.ingress");
        });
  cases.run("opaque associated requirement refuses before symbolic assumption",
            [] {
              refuses(check(R"(use zkc::transport::{NativeMessage}
interface Opaque:
    type Item: Type + Copy + Drop
protocol unused<C: Opaque> roles(P)(x: bool @P) -> bool @P where NativeMessage(C::Item):
    return x
)"),
                      "source.ingress");
            });
  cases.run("where empty preserves all send-derived goals", [] {
    auto project = take(check(
        R"(protocol Forward<T: Type> roles(P, V)(x: T @P) -> T @V where ():
    y <- send x to V
    return y
)"));
    const auto &decl = named(project, "m::Forward");
    require(decl.admissions.size() == 3 && decl.consumerRequirements.empty(),
            "where empty suppressed consumer-use demands");
  });
  for (unsigned mutation = 0; mutation < 9; ++mutation)
    cases.run(
        "independent written source consumer replay " + Twine(mutation), [&] {
          auto project = take(check(relay));
          witness(project);
          auto &required = named(project, "m::Relay::keep");
          auto &provided = named(project, "m::SentRelay::keep");
          for (auto *decl : {&required, &provided}) {
            auto &bound = decl->consumerRequirements.front();
            if (mutation == 0) {
              bound.arguments[0] = Type(Type::Kind::Boolean);
              for (auto &obligation : decl->admissions)
                obligation.type = Type(Type::Kind::Boolean);
            } else if (mutation == 1)
              bound.reference.target = named(project, "m::Relay").id;
            else if (mutation == 2)
              bound.reference.provider = named(project, "m::SentRelay").id;
            else if (mutation == 3)
              bound.reference.category = ResolutionCategory::Callable;
            else if (mutation == 4)
              decl->consumerRequirements.clear();
            else if (mutation == 5)
              decl->admissions.clear();
            else if (mutation == 7)
              bound.span.source =
                  named(project, "zkc::transport::NativeMessage").span.source;
            else if (mutation == 8)
              bound.span.begin += 1;
            else {
              bound.arguments.push_back(Type(Type::Kind::Boolean));
              bound.reference.path.clear();
            }
          }
          auto error = checkScopedElaboration(project);
          require(bool(error),
                  "mutually consistent checked mutation passed source replay");
          require(namesIdentifier(toString(std::move(error)),
                                  "source.scoped-witness"),
                  "consumer replay returned wrong diagnostic");
        });
  cases.run("selected associated Field retains native installed identity", [] {
    closes(take(check(R"(use zkc::transport::{NativeMessage}
domain Fr = field("bls12-381.fr")
interface Scalars:
    type Scalar: Field
module ScalarImpl: Scalars:
    type Scalar = Fr
protocol Forward<C: Scalars> roles(P, V)(x: C::Scalar @P) -> C::Scalar @V where NativeMessage(C::Scalar):
    y <- send x to V
    return y
pub protocol Demo roles(P, V)(x: Fr @P) -> Fr @V:
    y <- Forward<ScalarImpl>(x) @(P, V)
    return y
)")));
  });
  cases.run("owner interface header and multiple demands survive permutation",
            [] {
              closes(take(check(R"(use zkc::transport as Wire
interface Relay<T: Type + Copy + Drop, N: nat> where Wire::NativeMessage([T; N]):
    protocol keep<U: Type + Copy + Drop> roles(P, V)(x: [T; N] @P, y: U @P) -> U @P effects() where (Wire::NativeMessage(U), Wire::NativeMessage([T; N]))
module Impl<K: nat, A: Type + Copy + Drop>: Relay<A, K> where Wire::NativeMessage([A; K]):
    protocol keep<B: Type + Copy + Drop> roles(R, S)(x: [A; K] @R, y: B @R) -> B @R where Wire::NativeMessage(B):
        discarded <- send x to S
        return y
protocol Forward<N: nat, U: Type + Copy + Drop, T: Type + Copy + Drop, C: Relay<T, N>> roles(P, V)(x: [T; N] @P, y: U @P) -> U @P where (Wire::NativeMessage(U), Wire::NativeMessage([T; N])):
    result <- C::keep<U>(x, y) @(P, V)
    return result
pub protocol Demo roles(P, V)(x: [bool; 2] @P, y: index @P) -> index @P:
    r <- Forward<2, index, bool, Impl<2, bool>>(x, y) @(P, V)
    return r
)")));
            });
  cases.run("complete payload indices do not imply arbitrary envelopes", [] {
    refuses(check(R"(use zkc::transport::{NativeMessage}
struct Envelope<T: Type + Copy + Drop>:
    pub tag: bool
    pub payload: T
interface Relay:
    protocol keep<T: Type + Copy + Drop> roles(P, V)(x: Envelope<T> @P) -> Envelope<T> @P effects() where NativeMessage(T)
module Impl: Relay:
    protocol keep<U: Type + Copy + Drop> roles(A, B)(x: Envelope<U> @A) -> Envelope<U> @A where NativeMessage(Envelope<U>):
        discarded <- send x to B
        return x
)"),
            "source.conformance");
  });
  cases.run("framed zero cardinality is a nonempty native carrier", [] {
    closes(take(check(R"(use zkc::transport::{NativeMessage}
domain Fr = field("bls12-381.fr")
pub protocol Demo roles(P, V)(x: builtin("field_array", Fr, 0) @P) -> builtin("field_array", Fr, 0) @V where NativeMessage(builtin("field_array", Fr, 0)):
    y <- send x to V
    return y
)")));
  });
  for (StringRef payload :
       {"builtin(\"polynomial\", Fr)", "builtin(\"table\", Fr)"})
    cases.run("unsupported native logical payload " + payload, [&] {
      refuses(check("use zkc::transport::{NativeMessage}\ndomain Fr = "
                    "field(\"bls12-381.fr\")\n"
                    "protocol unused roles(P)(x: bool @P) -> bool @P where "
                    "NativeMessage(" +
                    payload + "):\n    return x\n"),
              "source.codec");
    });
  cases.run("ordinary user proof cannot manufacture a consumer requirement",
            [] {
              refuses(check(R"(def NativeMessage<T: Type>(x: bool) -> bool:
    x
protocol unused<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T):
    return x
)"),
                      "source.capability");
            });
  for (StringRef head : {"polynomial", "table"})
    cases.run("custom codec cannot admit an unsupported logical payload " +
                  head,
              [&] {
                auto captured = take(capture({{"m",
                                               (R"(module m;
domain F=field("bls12-381.fr");
type Payload=builtin(")" + head + R"(",F);
protocol Round roles(P,V)(public:bool@(P,V),secret:Payload@P)->(ok:bool@V){
  let received=send P->V(secret);return true;
}
type Bytes=builtin("bytes");
fn empty()->Bytes=primitive("bytes.empty");
interface RecordCodec{
  type Record:Copy+Drop;
  fn initialize(layout:bool)->Record effects(stop,opaque);
  fn write(record:Record)->Bytes effects(stop,opaque);
  fn finish(record:Record,proof:Bytes)->() effects(stop,opaque);
}
module Codec:RecordCodec{
  type Record:Copy+Drop=();
  fn initialize(layout:bool)->Record{return Record(());}
  fn write(record:Record)->Bytes{return empty();}
  fn finish(record:Record,proof:Bytes)->(){return ();}
}
construction Encoded for Round{base authored;format Codec(public);}
)")
                                                   .str(),
                                               "codec.zkc"}}));
                refuses(analyze(captured).checkedProject(), "source.codec");
              });
  cases.run("a requirement is neither an executable call nor a View descriptor",
            [] {
              refuses(check(R"(use zkc::transport::{NativeMessage}
view def pretend() -> NativeMessage<bool>:
    return NativeMessage<bool>()
)"),
                      "source.type");
            });
  cases.run("bounded work cannot publish a partially discharged selection", [] {
    auto project = take(check(
        Twine(relay) + R"(pub protocol Demo roles(P, V)(x: bool @P) -> bool @P:
    result <- Forward<bool, SentRelay>(x) @(P, V)
    return result
)"));
    Limits limits;
    limits.work = 50;
    refuses(closeNativeRun(project, "m::Demo", limits), "source.limit");
    closes(project);
  });
  cases.run("all unused demands discharge before clearing the declaration", [] {
    auto project = take(check(R"(use zkc::transport::{NativeMessage}
pub protocol Demo<A: Type, B: Type> roles(P)(x: bool @P) -> bool @P where (NativeMessage(A), NativeMessage(B)):
    return x
)"));
    refuses(closeNativeRun(project, "m::Demo", {},
                           {Type(Type::Kind::Boolean), Type(Type::Kind::Unit)}),
            "source.message-payload");
    closes(project, "m::Demo",
           {Type(Type::Kind::Boolean), Type(Type::Kind::Index)});
  });
  for (unsigned mutation = 0; mutation < 13; ++mutation)
    cases.run("standalone unused demand mutation " + Twine(mutation), [&] {
      auto project = take(check(R"(use zkc::transport::{NativeMessage}
pub protocol Demo<A: Type, B: Type> roles(P)(x: bool @P) -> bool @P where (NativeMessage(A), NativeMessage(B)):
    return x
)"));
      witness(project);
      auto &decl = named(project, "m::Demo");
      auto &requirement = decl.consumerRequirements.front();
      if (mutation == 0 || mutation == 2)
        decl.consumerRequirements.clear();
      if (mutation == 1 || mutation == 2)
        decl.admissions.clear();
      if (mutation == 3) {
        requirement.arguments[0] = Type(Type::Kind::Boolean);
        for (auto &admission : decl.admissions)
          admission.type = Type(Type::Kind::Boolean);
      }
      if (mutation == 4)
        requirement.reference.provider = named(project, "m").id;
      if (mutation == 5)
        requirement.reference.target = named(project, "m::Demo").id;
      if (mutation == 6)
        requirement.reference.path.clear();
      if (mutation == 7)
        requirement.reference.category = ResolutionCategory::Callable;
      if (mutation == 8)
        requirement.arguments.push_back(Type(Type::Kind::Boolean));
      if (mutation == 9)
        ++requirement.span.begin;
      if (mutation == 10)
        decl.consumerRequirements.push_back(requirement);
      if (mutation == 11)
        requirement.span.source =
            named(project, "zkc::transport::NativeMessage").span.source;
      if (mutation == 12)
        decl.consumerRequirements.pop_back();
      refusesWitness(project);
      refuses(
          closeNativeRun(project, "m::Demo", {},
                         {Type(Type::Kind::Boolean), Type(Type::Kind::Unit)}),
          "source.scoped-witness");
    });
  for (bool section : {false, true})
    for (unsigned mutation = 0; mutation < 5; ++mutation)
      cases.run(
          "inherited standalone demand " + Twine(section) + "/" +
              Twine(mutation),
          [&] {
            auto project = take(check(
                Twine("use zkc::transport::{NativeMessage}\n") +
                (section ? "section <T: Type>:\n    module Box where "
                           "NativeMessage(T):\n        pub protocol Demo "
                           "roles(P)(x: bool @P) -> bool @P:\n            "
                           "return x\n"
                         : "module Box<T: Type> where NativeMessage(T):\n    "
                           "pub protocol Demo roles(P)(x: bool @P) -> bool "
                           "@P:\n        return x\n")));
            closes(project, "m::Box::Demo", {Type(Type::Kind::Boolean)});
            refuses(closeNativeRun(project, "m::Box::Demo", {},
                                   {Type(Type::Kind::Unit)}),
                    "source.message-payload");
            for (StringRef name : {"m::Box", "m::Box::Demo"}) {
              auto &decl = named(project, name);
              if (mutation == 0 || mutation == 2)
                decl.consumerRequirements.clear();
              if (mutation == 1 || mutation == 2)
                decl.admissions.clear();
            }
            if (mutation == 3)
              named(project, "m::Box::Demo").parent = named(project, "m").id;
            if (mutation == 4)
              named(project, "m::Box::Demo").module = named(project, "m").id;
            refusesWitness(project);
          });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run(
        "unused declaration cannot erase its demand " + Twine(mutation), [&] {
          auto project = take(check(R"(use zkc::transport::{NativeMessage}
protocol Unused<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T):
    return x
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
    return x
)"));
          closes(project);
          auto &unused = named(project, "m::Unused");
          if (mutation != 1)
            unused.consumerRequirements.clear();
          if (mutation != 0)
            unused.admissions.clear();
          refusesWitness(project);
          refuses(closeNativeRun(project, "m::Demo"), "source.scoped-witness");
        });
  cases.run(
      "foreign demand requires an authored owner even without clauses", [] {
        auto project = take(
            check(R"(pub protocol Demo<T: Type> roles(P)(x: bool @P) -> bool @P:
    return x
)"));
        auto donor = take(check(R"(use zkc::transport::{NativeMessage}
protocol Donor<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T):
    return x
)"));
        named(project, "m::Demo").consumerRequirements =
            named(donor, "m::Donor").consumerRequirements;
        refusesWitness(project);
      });
  cases.run("generated Host run still discharges the selected protocol", [] {
    auto project = take(check(R"(use zkc::transport::{NativeMessage}
pub protocol Demo<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T):
    return x
)"));
    auto closed = take(closeEntry(project, "m::Demo<bool>"));
    require(named(project, "m::Demo::run").consumerRequirements.empty(),
            "generated member invented an authored clause");
    refuses(closeEntry(project, "m::Demo<()>"), "source.message-payload");
    auto &decl = named(project, "m::Demo");
    decl.consumerRequirements.clear();
    decl.admissions.clear();
    refuses(closeEntry(project, "m::Demo<()>"), "source.scoped-witness");
  });
  cases.run("generated members cannot acquire foreign consumer metadata", [] {
    auto project = take(check(R"(use zkc::transport::{NativeMessage}
pub protocol Demo<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T):
    return x
)"));
    named(project, "m::Demo::run").consumerRequirements =
        named(project, "m::Demo").consumerRequirements;
    refusesWitness(project);
  });
  for (StringRef mode : {"def", "local def", "view def"})
    for (unsigned mutation = 0; mutation < 3; ++mutation)
      cases.run("ordinary header consumer " + mode + "/" + Twine(mutation), [&] {
        auto project = take(check(
            Twine("use zkc::transport::{NativeMessage}\n") + mode +
            R"( keep<T: Type + Copy + Drop>(x: T) -> T where NativeMessage(T):
    return x
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
)" +
            (mode == "local def" ? "    result <- keep<bool>(x)\n"
                                 : "    result = keep<bool>(x)\n") +
            "    return result\n"));
        closes(project);
        auto &decl = named(project, "m::keep");
        if (mutation != 1)
          decl.consumerRequirements.clear();
        if (mutation != 0)
          decl.admissions.clear();
        refusesWitness(project);
      });
  for (StringRef declaration :
       {"struct Demand<T:Type+Copy+Drop> where NativeMessage(T){pub value:T}",
        "type Demand<T:Type> where NativeMessage(T)=T;",
        "construction Demand<T:Type> for Demo<T> where NativeMessage(T){base "
        "authored;}"})
    for (unsigned mutation = 0; mutation < 3; ++mutation)
      cases.run("noncallable header demand " + declaration + "/" +
                    Twine(mutation),
                [&] {
                  auto captured = take(capture({{"m",
                                                 (Twine(R"(module m;
use zkc::transport::{NativeMessage};
protocol Demo<T:Type> roles(P)(x:bool@P)->(result:bool@P){return x;}
)") + declaration)
                                                     .str(),
                                                 "consumer.zkc"}}));
                  auto project = take(analyze(captured).checkedProject());
                  witness(project);
                  auto &decl = named(project, "m::Demand");
                  require(!decl.consumerRequirements.empty() &&
                              !decl.admissions.empty(),
                          "noncallable fixture lost its demands");
                  if (mutation != 1)
                    decl.consumerRequirements.clear();
                  if (mutation != 0)
                    decl.admissions.clear();
                  refusesWitness(project);
                });
  cases.run(
      "entry selector meters unused admission payload before copying", [] {
        auto project = unusedAdmissionProject();
        auto &unused = named(project, "m::Unused");
        require(
            unused.consumerRequirements.empty() &&
                unused.admissions.size() == 3,
            "fixture needs body-derived admissions without consumer metadata");
        auto selection = [&](const Limits &limits) {
          std::vector<SourceWorkBudget> budgets;
          auto result =
              resolveEntry(project, "m::Demo<bool>", limits, {}, &budgets);
          require(budgets.size() == 1 &&
                      budgets.front().phase == SourceWorkPhase::EntrySelection,
                  "selection failed before its snapshot work budget");
          auto cost = budgets.front().ledger.total;
          if (!result) {
            require(
                namesIdentifier(toString(result.takeError()), "source.limit"),
                "selection returned the wrong refusal");
            return std::make_pair(cost, false);
          }
          require(result->arguments ==
                      std::vector<Type>{Type(Type::Kind::Boolean)},
                  "snapshot charging changed generic selection");
          return std::make_pair(cost, true);
        };
        auto [smallCost, smallOK] = selection({});
        require(smallOK, "authentic selection failed");
        auto original = unused.admissions.front();
        require(original.calls.empty(),
                "unused fixture unexpectedly transports calls");
        // An adversarial retained provenance vector must be charged even when
        // the selected protocol never uses this declaration or checks its
        // arguments.
        const auto calls = project.checkedWork() + 256;
        unused.admissions.front().calls.assign(calls, original.span);
        auto [largeCost, largeOK] = selection({});
        outs() << "admission selector checked_work=" << project.checkedWork()
               << " small=" << smallCost << " large=" << largeCost
               << " retained_calls=" << calls << '\n';
        require(largeOK && largeCost == smallCost + calls,
                "unused admission payload escaped the pre-copy charge");
        Limits exact;
        exact.work = largeCost;
        require(exact.work > project.checkedWork(),
                "checked-work gate masks the snapshot boundary");
        require(selection(exact) == std::make_pair(largeCost, true),
                "warm exact selector allowance changed work");
        --exact.work;
        auto [shortCost, shortOK] = selection(exact);
        require(!shortOK && shortCost <= exact.work,
                "one-short selector allowance succeeded or overspent");
        require(unused.admissions.front().calls.size() == calls,
                "failed snapshot changed retained admissions");
        ++exact.work;
        require(selection(exact) == std::make_pair(largeCost, true),
                "failed snapshot changed exact-budget retry");
        unused.admissions.front() = std::move(original);
        require(selection({}) == std::make_pair(smallCost, true),
                "restored cold selector changed work");
        closes(project, "m::Demo", {Type(Type::Kind::Boolean)});
      });
  for (bool consumer : {false, true})
    cases.run("closed replay rejects residual requirements " + Twine(consumer),
              [&] {
                auto project = unusedAdmissionProject();
                auto closed = take(closeNativeRun(project, "m::Demo", {},
                                                  {Type(Type::Kind::Boolean)}));
                auto &root = const_cast<Declaration &>(closed.root());
                if (auto error = checkScopedSpecialization(closed))
                  throw std::runtime_error(toString(std::move(error)));
                if (consumer) {
                  auto donor = take(check(R"(use zkc::transport::{NativeMessage}
protocol Demand<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T):
    return x
)"));
                  root.consumerRequirements =
                      named(donor, "m::Demand").consumerRequirements;
                } else {
                  root.admissions = named(project, "m::Unused").admissions;
                  root.admissions.front().calls.assign(200000, root.span);
                }
                for (unsigned retry = 0; retry != 2; ++retry) {
                  auto error = checkScopedSpecialization(closed);
                  require(bool(error), "closed residual requirement accepted");
                  require(namesIdentifier(toString(std::move(error)),
                                          "source.scoped-specialization"),
                          "closed residual requirement copied or evaluated");
                }
                root.admissions.clear();
                root.consumerRequirements.clear();
                if (auto error = checkScopedSpecialization(closed))
                  throw std::runtime_error(toString(std::move(error)));
              });
  cases.run("specialization replay meters unused admission snapshot", [] {
    auto project = unusedAdmissionProject();
    auto closed = take(
        closeNativeRun(project, "m::Demo", {}, {Type(Type::Kind::Boolean)}));
    auto replay = [&](uint64_t allowance) {
      Limits limits;
      limits.work = allowance;
      std::vector<SourceWorkBudget> budgets;
      auto error = checkScopedSpecialization(closed, limits, &budgets);
      const bool ok = !error;
      if (error)
        require(namesIdentifier(toString(std::move(error)), "source.limit"),
                "specialization replay returned the wrong refusal");
      require(budgets.size() >= 2 &&
                  budgets.back().phase == SourceWorkPhase::ScopedSpecialization,
              "source check masks specialization replay snapshot budget");
      const auto cost = budgets.back().ledger.total;
      require(cost <= allowance, "specialization replay overspent");
      return std::make_pair(cost, ok);
    };
    auto [smallCost, smallOK] = replay(Limits{}.work);
    require(smallOK, "authentic specialization replay failed");
    auto &admission = named(project, "m::Unused").admissions.front();
    require(admission.calls.empty(),
            "unused fixture unexpectedly has call origins");
    const auto calls = project.checkedWork() + 256;
    admission.calls.assign(calls, admission.span);
    auto [largeCost, largeOK] = replay(Limits{}.work);
    outs() << "admission specialization replay small=" << smallCost
           << " large=" << largeCost << " retained_calls=" << calls << '\n';
    require(largeOK && largeCost == smallCost + calls,
            "independent specialization copy escaped admission charging");
    require(replay(largeCost) == std::make_pair(largeCost, true),
            "warm exact specialization replay changed work");
    require(!replay(largeCost - 1).second,
            "one-short specialization replay succeeded");
    require(admission.calls.size() == calls,
            "failed specialization replay changed the source template");
    require(replay(largeCost) == std::make_pair(largeCost, true),
            "specialization replay failure changed retry");
    admission.calls.clear();
    require(replay(Limits{}.work) == std::make_pair(smallCost, true),
            "restored specialization replay changed work");
  });
  for (bool depth : {false, true})
    cases.run("unused admission snapshot type boundary " + Twine(depth), [&] {
      auto project = unusedAdmissionProject();
      take(resolveEntry(project, "m::Demo<bool>"));
      auto &admission = named(project, "m::Unused").admissions.front();
      auto original = admission.type;
      Type nested(Type::Kind::Boolean);
      for (unsigned i = 1; i < 16; ++i) {
        Type tuple(Type::Kind::Tuple);
        tuple.arguments.push_back(std::move(nested));
        nested = std::move(tuple);
      }
      admission.type = std::move(nested);
      Limits limits;
      auto &bound = depth ? limits.typeDepth : limits.typeNodes;
      bound = 16;
      take(resolveEntry(project, "m::Demo<bool>", limits));
      --bound;
      refuses(resolveEntry(project, "m::Demo<bool>", limits), "source.limit");
      ++bound;
      take(resolveEntry(project, "m::Demo<bool>", limits));
      admission.type = std::move(original);
      closes(project, "m::Demo", {Type(Type::Kind::Boolean)});
    });
  for (bool callback : {false, true})
    for (unsigned instances : {1u, 6u})
      cases.run(
          "deferred admission snapshots callback=" + Twine(callback) +
              " instances=" + Twine(instances),
          [&] {
            std::string source = R"(use zkc::transport::{NativeMessage}
def apply<T: Type + Copy + Drop>(x: T, body: fn(T) -> T) -> T:
    return body(x)
def keep<T: Type + Copy + Drop, N: nat>(x: T) -> T where NativeMessage(T):
)";
            source += callback ? "    return apply<T>(x, fn(y) => y)\n"
                               : "    return x\n";
            source += "pub protocol Demo roles(P)(x: bool @P) -> bool @P:\n";
            for (unsigned i = 0; i < instances; ++i)
              source += "    value" + std::to_string(i) + " = keep<bool, " +
                        std::to_string(i) + ">(x)\n";
            source += "    return value" + std::to_string(instances - 1) + "\n";
            auto project = take(check(source));
            auto &demand = named(project, "m::keep");
            require(demand.admissions.size() == 3,
                    "generic snapshot fixture lost its deferred atoms");
            const auto body = demand.body;
            const auto capacity = demand.admissions.capacity();
            unsigned copies = 0;
            auto [smallCost, smallOK] =
                specializeSnapshot(project, Limits{}.work, copies);
            require(smallOK && copies == instances,
                    "cold specialization failed");
            for (auto &admission : demand.admissions)
              admission.calls.assign(64, admission.span);
            auto [largeCost, largeOK] =
                specializeSnapshot(project, Limits{}.work, copies);
            // For this fixture, argument admission, body summaries and callable
            // snapshots traverse each provenance chain three times per
            // instance. Callback checking and its cached/helper snapshots raise
            // that to eight.
            const auto traversals = (callback ? 8 : 3) * instances;
            outs() << "admission snapshots callback=" << callback
                   << " instances=" << instances << " small=" << smallCost
                   << " large=" << largeCost << " traversals=" << traversals
                   << '\n';
            require(largeOK && copies == instances &&
                        largeCost - smallCost == 64 * 3 * traversals,
                    "deferred admission copy escaped its own snapshot charge");
            require(specializeSnapshot(project, largeCost, copies) ==
                        std::make_pair(largeCost, true),
                    "warm exact specialization changed work");
            auto [spent, ok] =
                specializeSnapshot(project, largeCost - 1, copies);
            require(!ok && spent < largeCost,
                    "one-short deferred specialization succeeded or overspent");
            require(specializeSnapshot(project, largeCost, copies) ==
                        std::make_pair(largeCost, true),
                    "deferred specialization failure changed retry");
            require(demand.body == body &&
                        demand.admissions.capacity() == capacity,
                    "specialization changed the retained template");
            for (auto &admission : demand.admissions) {
              require(admission.calls.size() == 64,
                      "failed specialization changed retained provenance");
              admission.calls.clear();
            }
            closes(project);
          });
  for (bool callback : {false, true})
    for (unsigned instances : {1u, 6u})
      cases.run(
          "repeated concrete snapshot callback=" + Twine(callback) +
              " instances=" + Twine(instances),
          [&] {
            auto specialize = specializeSnapshot;
            auto small = snapshotProject(1, instances, callback);
            auto large = snapshotProject(64, instances, callback);
            const auto &demand = named(large, "m::keep");
            require(demand.consumerRequirements.size() == 64 &&
                        demand.admissions.empty(),
                    "concrete fixture retained deferred atoms or lost clauses");
            const auto originalBody = demand.body;
            const auto originalCapacity =
                demand.consumerRequirements.capacity();
            unsigned copies = 0;
            auto [smallCost, smallOK] =
                specialize(small, Limits{}.work, copies);
            require(smallOK && copies == instances,
                    "static fixture missed copies");
            auto [largeCost, largeOK] =
                specialize(large, Limits{}.work, copies);
            outs() << "snapshot measured callback=" << callback
                   << " instances=" << instances << " one_clause=" << smallCost
                   << " repeated_clauses=" << largeCost << '\n';
            require(largeOK && copies == instances && largeCost > smallCost,
                    "repeated concrete metadata was copied without charging");
            zkc::language::detail::Work metadata{Limits{}};
            if (auto error = zkc::language::detail::chargeConsumerRequirement(
                    demand.consumerRequirements.front(), metadata))
              throw std::runtime_error(toString(std::move(error)));
            const auto metadataCopyDelta = 63 * metadata.used;
            // A callback creates one cached lexical template, then a closed
            // helper per distinct static selection, in addition to each keep
            // snapshot.
            const auto snapshots = callback ? 2 * instances + 1 : instances;
            require(
                largeCost - smallCost >= metadataCopyDelta * snapshots,
                "generated or distinct static copies escaped metadata work");
            auto [exactCost, exactOK] = specialize(large, largeCost, copies);
            require(exactOK && exactCost == largeCost && copies == instances,
                    "exact specialization budget changed the result");
            auto [shortCost, shortOK] =
                specialize(large, largeCost - 1, copies);
            require(!shortOK && shortCost <= largeCost - 1,
                    "one-short specialization budget succeeded or overspent");
            if (instances > 1) {
              const auto budget = smallCost + (largeCost - smallCost) / 2;
              auto [spent, ok] = specialize(large, budget, copies);
              outs() << "snapshot intermediate callback=" << callback
                     << " budget=" << budget << " spent=" << spent
                     << " completed_instances=" << copies << '\n';
              require(
                  !ok && copies > 0 && copies < instances && spent <= budget,
                  "middle budget failed before reaching repeated snapshots");
            }
            require(demand.body == originalBody &&
                        demand.consumerRequirements.size() == 64 &&
                        demand.consumerRequirements.capacity() ==
                            originalCapacity &&
                        demand.admissions.empty(),
                    "failed closure changed the checked template");
            closes(large);
            outs() << "snapshot clauses=64 callback=" << callback
                   << " instances=" << instances << " small_work=" << smallCost
                   << " large_work=" << largeCost << " exact=" << exactCost
                   << " one_short_spent=" << shortCost << '\n';
          });
  cases.run(
      "public closure reaches repeated metadata snapshots before refusing", [] {
        constexpr unsigned clauses = 512;
        auto project = snapshotProject(clauses, 1, false, 11);
        const auto body = named(project, "m::keep").body;
        const auto capacity =
            named(project, "m::keep").consumerRequirements.capacity();
        auto closed = take(closeNativeRun(project, "m::Demo"));
        const auto copies =
            llvm::count_if(closed.declarations(), [&](const auto &decl) {
              return decl.origin &&
                     decl.origin->index == named(project, "m::keep").id.index;
            });
        require(copies == 2048,
                "public fixture missed distinct static snapshots");
        const auto phase = closed.workObservation().charged.used(
            SourceWorkPhase::Specialization);
        Limits limits;
        limits.work = std::max(project.checkedWork(), phase / 2);
        outs() << "public snapshot checked_work=" << project.checkedWork()
               << " specialization_work=" << phase
               << " refusal_budget=" << limits.work << '\n';
        require(limits.work < phase,
                "public fixture cannot reach the snapshot budget boundary");
        auto refused = closeNativeRun(project, "m::Demo", limits);
        require(!refused, "bounded public closure unexpectedly succeeded");
        handleAllErrors(
            refused.takeError(), [&](const DiagnosticError &failure) {
              require(
                  failure.diagnostic().code == "source.limit" &&
                      StringRef(failure.diagnostic().message)
                          .contains("in specialization"),
                  "public budget failed before the specialization boundary");
            });
        require(named(project, "m::keep").body == body &&
                    named(project, "m::keep").consumerRequirements.size() ==
                        clauses &&
                    named(project, "m::keep").consumerRequirements.capacity() ==
                        capacity,
                "failed public closure changed the checked template");
        limits.work = std::max(project.checkedWork(), closed.closedWork());
        auto retry = take(closeNativeRun(project, "m::Demo", limits));
        require(retry.closedWork() == closed.closedWork(),
                "failed public closure changed the next exact-budget result");
      });
  cases.run("known generic sealed invalidity precedes exact premises", [] {
    refuses(check(R"(use zkc::transport::{NativeMessage}
#[sealed]
struct Secret<T: Type + Copy + Drop>:
    pub value: T
interface Impossible:
    protocol keep<T: Type + Copy + Drop> roles(P)(x: bool @P) -> bool @P effects() where NativeMessage(Secret<T>)
)"),
            "source.ingress");
  });
  cases.run("nonempty carrier observation obeys aggregate capacity", [] {
    auto project = take(check(R"(use zkc::transport::{NativeMessage}
pub protocol Demo<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T):
    return x
)"));
    Type pair(Type::Kind::Tuple);
    pair.arguments = {Type(Type::Kind::Boolean), Type(Type::Kind::Boolean)};
    Limits limits;
    limits.aggregateLeaves = 1;
    refuses(closeNativeRun(project, "m::Demo", limits, {pair}), "source.limit");
    closes(project, "m::Demo", {pair});
  });
  cases.run(
      "public reexports and module aliases keep installed requirement identity",
      [] {
        CaptureOptions options;
        options.format = "zkc-layout";
        auto captured = take(
            capture({{"facade", "pub use zkc::transport::{NativeMessage}\n",
                      "facade.zkc"},
                     {"m", R"(use facade as Requirements
pub protocol Demo<T: Type> roles(P)(x: bool @P) -> bool @P where Requirements::NativeMessage(T):
    return x
)",
                      "relay.zkc"}},
                    options));
        auto project = take(analyze(captured).checkedProject());
        const auto &requirement =
            named(project, "m::Demo").consumerRequirements.front();
        require(
            requirement.reference.target.index ==
                    named(project, "zkc::transport::NativeMessage").id.index &&
                requirement.reference.provider.index ==
                    named(project, "facade").id.index,
            "consumer requirement lost its facade/provider distinction");
        auto api = take(json::parse(take(inspectPublicAPI(project))));
        bool installed = false;
        for (const auto &value : *api.getAsObject()->getArray("declarations")) {
          const auto &decl = *value.getAsObject();
          if (decl.getString("name") == "zkc::transport::NativeMessage") {
            require(decl.getString("kind") == "requirement" &&
                        !decl.get("inputs") && !decl.get("outputs"),
                    "installed consumer acquired callable or descriptor ports");
            installed = true;
          }
        }
        require(installed,
                "public reexport lost its installed requirement category");
        closes(project, "m::Demo", {Type(Type::Kind::Boolean)});
      });
  cases.run("captured source cannot replace an installed requirement module",
            [] {
              CaptureOptions options;
              options.format = "zkc-layout";
              refuses(capture({{"zkc::transport",
                                "pub interface NativeMessage<T: Type>:\n    "
                                "type Item: Type\n",
                                "fake.zkc"}},
                              options),
                      "source.module");
            });
  cases.run("requirement argument count is exact", [] {
    refuses(check(R"(use zkc::transport::{NativeMessage}
protocol unused<T: Type> roles(P)(x: bool @P) -> bool @P where NativeMessage(T, bool):
    return x
)"),
            "source.requirement");
  });
  cases.run("consumer demands preserve independent participant admission", [] {
    auto project = take(check(R"(use zkc::transport::{NativeMessage}
protocol Both<T: Type> roles(P, V)(x: T @(P, V)) -> T @(P, V) where NativeMessage(T):
    return x
)"));
    const auto &decl = named(project, "m::Both");
    require(decl.admissions.size() == 4 && decl.capabilityBounds.empty() &&
                decl.permissionBounds.empty(),
            "consumer demand granted a capability or permission");
    require(llvm::count_if(decl.admissions,
                           [](const auto &obligation) {
                             return obligation.boundary ==
                                    Boundary::Participants;
                           }) == 1,
            "consumer demand replaced participant admission");
  });
  cases.run("consumer demand cannot prove implementation Copy strengthening",
            [] {
              refuses(check(R"(use zkc::transport::{NativeMessage}
interface Duplicate:
    protocol copy<T: Type> roles(P)(x: T @P) -> (T @P, T @P) effects() where NativeMessage(T)
module Impl: Duplicate:
    protocol copy<U: Type + Copy> roles(A)(x: U @A) -> (U @A, U @A) where NativeMessage(U):
        return (x, x)
)"),
                      "source.conformance");
            });
  cases.run("consumer demand cannot prove implementation Drop strengthening",
            [] {
              refuses(check(R"(use zkc::transport::{NativeMessage}
interface Dispose:
    protocol discard<T: Type> roles(P)(x: T @P) -> bool @P effects() where NativeMessage(T)
module Impl: Dispose:
    protocol discard<U: Type + Drop> roles(A)(x: U @A) -> bool @A where NativeMessage(U):
        return true
)"),
                      "source.conformance");
            });
  cases.run("braced where syntax resolves the same indexed installed demand",
            [] {
              auto captured = take(capture({{"m", R"(module m;
use zkc::transport::{NativeMessage};
pub protocol Demo<T:Type> roles(P)(x:bool@P)->(result:bool@P) where NativeMessage(T){return x;}
)",
                                             "consumer.zkc"}}));
              auto project = take(analyze(captured).checkedProject());
              closes(project, "m::Demo", {Type(Type::Kind::Boolean)});
              refuses(closeNativeRun(project, "m::Demo", {},
                                     {Type(Type::Kind::Unit)}),
                      "source.message-payload");
            });
  cases.run(
      "written source retains the existing requirement shape and owner", [] {
        auto project = take(check(relay));
        auto inventory = take(json::parse(take(inspectDeclarations(project))));
        bool indexed = false;
        for (const auto &value : *inventory.getAsArray()) {
          const auto &decl = *value.getAsObject();
          if (decl.getString("name") != "m::Forward")
            continue;
          const auto &requirements = *decl.getArray("requirements");
          require(requirements.size() == 1,
                  "consumer demand omitted from diagnostic contract");
          const auto &bound = *requirements.front().getAsObject();
          require(bound.getString("kind") == "consumer" &&
                      bound.getString("identity") ==
                          "consumer.native-message" &&
                      bound.getString("export") ==
                          "zkc::transport::NativeMessage" &&
                      *bound.getArray("arguments") == json::Array{"T"},
                  "diagnostic consumer identity or index changed");
          indexed = true;
        }
        require(indexed, "diagnostic contract omitted forwarding declaration");
        auto source = take(inspectWrittenSource(project));
        auto view = take(json::parse(source));
        unsigned requirements = 0;
        for (const auto &row : *view.getAsObject()->getArray("declarations")) {
          const auto &decl = *row.getAsObject();
          require(decl.getString("owner") != "zkc::transport::NativeMessage",
                  "installation acquired authored source syntax");
          for (const auto &value : *decl.getArray("nodes")) {
            const auto &node = *value.getAsObject();
            if (node.getString("kind") != "requirement")
              continue;
            ++requirements;
            require(node.getString("capability") == "NativeMessage" &&
                        node.getArray("arguments")->size() == 1 &&
                        node.size() == 9,
                    "consumer requirement changed the exact source node shape");
          }
        }
        require(requirements == 3,
                "written requirements lost their source owners");
        named(project, "m::Relay::keep")
            .consumerRequirements.front()
            .arguments[0] = Type(Type::Kind::Boolean);
        require(take(inspectWrittenSource(project)) == source,
                "mutable checked contract replaced immutable written source");
      });
  return cases.result();
}
