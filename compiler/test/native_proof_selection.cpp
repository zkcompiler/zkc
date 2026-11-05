#include "../lib/Compiler/NativeConstructionPreparation.h"
#include "../lib/Compiler/NativeProofVerification.h"
#include "../lib/Compiler/NativeRequest.h"
#include "../lib/Transforms/RealizedProtocol.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/NativeCompilation.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Printing.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace mlir;
using namespace zkc;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
std::string bytes(ModuleOp module) {
  std::string text;
  raw_string_ostream out(text);
  module->print(out, canonicalPrintingFlags());
  return text;
}
NativeProofPolicy selection() {
  NativeProofPolicy policy;
  policy.entry = "main";
  policy.producer = "Alice";
  policy.validator = "Bob";
  policy.suite = "merlin3.bls12-381.fr64be/0";
  policy.services = {4};
  policy.publicInputs = {0, 2};
  return policy;
}
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "fixture directory argument");
  zkc::test::Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto read = [&](StringRef name) {
    auto buffer = MemoryBuffer::getFile(Twine(argv[1]) + "/" + name + ".mlir");
    require(bool(buffer), "cannot read fixture");
    return (*buffer)->getBuffer().str();
  };
  auto parse = [&](StringRef text) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "invalid test source");
    return module;
  };
  auto schnorr = read("schnorr-services");
  cases.run("native compilation consumes the checked endpoint closure", [&] {
    for (auto operation :
         {NativeProofOperation::Prove, NativeProofOperation::Verify}) {
      NativeProofOptions options{NativeProofSelection{selection()}};
      options.operation = operation;
      auto compiled =
          take(compileNativeProof(schnorr, "endpoint.mlir", options, registry));
      auto root = *compiled.compilation.module()
                       .getOps<protocol_ir::ProtocolModuleOp>()
                       .begin();
      auto participants =
          root.getBody().front().getOps<protocol_ir::ParticipantOp>();
      require(hasSingleElement(participants),
              "native operation retained both roles");
      require((*participants.begin()).getRole() ==
                  (operation == NativeProofOperation::Verify ? "Bob" : "Alice"),
              "native operation retained the wrong role");
      require(
          root.getBody().front().getOps<protocol_ir::ProjectionOp>().empty(),
          "correspondence records entered executable publication");
      auto malformed = schnorr;
      auto position = malformed.find("%challenge = protocol.exchange %c");
      require(position != std::string::npos, "missing delivery");
      malformed.replace(
          position, StringRef("%challenge = protocol.exchange %c").size(),
          "%altered = algebra.field_add %c, %c : "
          "(!algebra.field<\"bls12-381.fr\">, "
          "!algebra.field<\"bls12-381.fr\">) "
          "-> !algebra.field<\"bls12-381.fr\">\n%challenge = protocol.exchange "
          "%altered");
      refuses(compileNativeProof(malformed, "endpoint.mlir", options, registry),
              "native-proof-reverse-message");
    }
  });
  for (StringRef suite : {"merlin3.bls12-381.fr64be/0",
                          "spongefish0.8.0.keccak.bls12-381.fr64be/0"})
    for (StringRef fixture :
         {"schnorr-services", "iterated-sumcheck", "nested-schnorr"})
      cases.run(fixture + ": " + suite, [&] {
        auto module = parse(read(fixture));
        auto original = bytes(*module);
        auto policy = selection();
        policy.suite = suite.str();
        std::vector<std::pair<std::string, std::string>> expected;
        if (fixture == "schnorr-services")
          expected = {{"draw_challenge", "challenge"}};
        else {
          policy.producer = "P";
          policy.validator = "V";
          if (fixture == "iterated-sumcheck") {
            policy.publicInputs = {1, 2, 3};
            expected = {{"draw", "challenge"}};
          } else {
            policy.services = {5};
            policy.publicInputs = {0, 1, 3};
            for (StringRef call : {"first", "second"}) {
              auto prefix =
                  mathematical::expandedApplicationSite("segment", call);
              expected.emplace_back(
                  mathematical::expandedApplicationSite(prefix,
                                                        "draw_challenge"),
                  mathematical::expandedApplicationSite(prefix, "challenge"));
            }
          }
        }
        auto resolved = take(selectNativeProofDraws(*module, policy));
        require(resolved.draws == expected,
                "derived query/delivery order differs");
        policy.draws = expected;
        require(encodeNativeProofPolicy(resolved) ==
                    encodeNativeProofPolicy(policy),
                "selection changed an explicit policy choice");
        auto selected = take(constructNativeProof(*module, resolved));
        auto explicitProof = take(constructNativeProof(*module, policy));
        require(selected.descriptor == explicitProof.descriptor &&
                    bytes(*selected.module) == bytes(*explicitProof.module),
                "resolved policy changed proof construction");
        require(bytes(*module) == original, "selection mutated original");
      });
  for (bool withRequest : {false, true})
    cases.run(
        withRequest
            ? "polynomial request discharge shares one terminal ledger"
            : "polynomial preparation retains bodies and one terminal ledger",
        [&] {
          auto text = read("iterated-sumcheck");
          if (withRequest) {
            StringRef ownership = "input_roles=[[\"P\"],[\"P\",\"V\"],[\"P\","
                                  "\"V\"],[\"V\"],[\"V\"]]";
            auto roles = text.find(ownership.str());
            require(roles != std::string::npos,
                    "missing recipe input ownership");
            text.replace(roles, ownership.size(),
                         "input_roles=[[\"P\"],[\"P\",\"V\"],[\"P\",\"V\"],["
                         "\"P\",\"V\"],[\"V\"]]");
            auto start = text.find("%count = protocol.exchange %n");
            require(start != std::string::npos, "missing recipe transport");
            text.insert(
                start, "%request = protocol.exchange %claim "
                       "{sender=\"V\",receiver=\"P\",site=\"request\"} : !f\n");
          }
          auto module = parse(text);
          require(succeeded(admitStage(*module)), "recipe source admission");
          auto original = bytes(*module);
          auto unit = *module->getOps<protocol_ir::ProtocolModuleOp>().begin();
          auto entry =
              SymbolTable(unit).lookup<protocol_ir::MathematicalOp>("main");
          auto execution = take(protocol::readSourceExecutionClosure(unit));
          auto policy = selection();
          policy.producer = "P";
          policy.validator = "V";
          policy.publicInputs = {1, 2, 3};
          policy.draws = {{"draw", "challenge"}};
          auto prepare = [&](uint64_t budget = 1000000) {
            return zkc::detail::prepareNativeConstruction(
                *module, entry, execution, policy, nullptr, {}, budget);
          };
          auto joint = take(prepare());
          require(joint.needsRealization() && !joint.complete(),
                  "declarative recipe supplied an execution body");
          auto rows = joint.dependencies();
          size_t initialRows = rows.size();
          unsigned calls = 0;
          for (auto [index, row] : enumerate(rows)) {
            auto call = dyn_cast_or_null<protocol_ir::LocalCallOp>(row.source);
            if (row.kind !=
                    zkc::detail::ConstructionDependencyKind::Realization ||
                !call)
              continue;
            ++calls;
            llvm::DenseSet<unsigned> visited;
            llvm::DenseSet<Operation *> operations;
            llvm::DenseSet<Value> values;
            SmallVector<unsigned> pending{static_cast<unsigned>(index)};
            while (!pending.empty()) {
              unsigned id = pending.pop_back_val();
              require(id < rows.size(), "invalid dependency index");
              if (!visited.insert(id).second)
                continue;
              operations.insert(rows[id].source);
              if (rows[id].value)
                values.insert(rows[id].value);
              for (unsigned predecessor : rows[id].predecessors) {
                require(predecessor < id, "recipe dependency order");
                pending.push_back(predecessor);
              }
            }
            auto realization =
                SymbolTable(unit).lookup<poly::RealizeOp>(call.getCallee());
            auto recipe = SymbolTable(unit).lookup<poly::RecipeOp>(
                realization.getRecipe());
            require(operations.contains(realization),
                    "lost actual realization");
            for (Operation &op : recipe.getBody().front())
              require(operations.contains(&op), "lost actual recipe operation");
            for (Value input : call.getInputs())
              require(values.contains(input), "lost actual recipe call input");
            for (Value formal : recipe.getBody().front().getArguments())
              require(values.contains(formal), "lost actual recipe slot");
          }
          require(calls == 5,
                  "all five used declarative calls must be retained");
          auto prepared = mathematical::PreparedProtocol::prepare(*module);
          require(bool(prepared),
                  "independently checked polynomial preparation");
          auto realized = take(
              mathematical::RealizedProtocol::realize(std::move(*prepared)));
          auto actual = realized.candidateSnapshot();
          auto actualUnit =
              *actual->getOps<protocol_ir::ProtocolModuleOp>().begin();
          auto actualEntry = SymbolTable(actualUnit)
                                 .lookup<protocol_ir::MathematicalOp>("main");
          auto actualExecution =
              take(protocol::readSourceExecutionClosure(actualUnit));
          auto resolve =
              [&](zkc::detail::NativeConstructionPreparation &analysis) {
                return analysis.resolveRealization(
                    *actual, actualEntry, actualExecution, policy, nullptr, {});
              };
          auto succeed = [](Error error) {
            if (error)
              throw std::runtime_error(toString(std::move(error)));
          };
          auto capacity = [](Error error) {
            require(bool(error), "one-less allowance supplied a result");
            require(namesIdentifier(toString(std::move(error)),
                                    "native-construction-preparation-capacity"),
                    "lost terminal capacity refusal");
          };
          succeed(resolve(joint));
          require(joint.complete() == !withRequest &&
                      !joint.needsRealization() &&
                      joint.dependencies().size() > initialRows,
                  "actual checked realization did not extend original "
                  "dependencies");
          uint64_t realizationWork = joint.workUsed();
          OwningOpRef<ModuleOp> projection;
          std::optional<zkc::detail::NativeRequestPlan> requests;
          if (withRequest) {
            projection = realized.project(false);
            require(bool(projection), "actual checked request projection");
            auto projectedUnit =
                *projection->getOps<protocol_ir::ProtocolModuleOp>().begin();
            zkc::detail::NativeTranscriptEvent event{
                "request", "", entry.getFunctionType().getInput(3),
                false,     0,  std::nullopt};
            event.reconstructed = true;
            requests.emplace(take(zkc::detail::planNativeRequests(
                projectedUnit, policy, {event}, &realized)));
            require(
                requests->root && requests->root->requests.size() == 1,
                "actual request plan did not read the source reverse message");
            succeed(joint.dischargeRequests(*requests));
            require(
                joint.complete() && joint.workUsed() > realizationWork,
                "successful request discharge did not consume the same ledger");
          }
          uint64_t exactWork = joint.workUsed();
          auto exact = take(prepare(exactWork));
          succeed(resolve(exact));
          if (withRequest)
            succeed(exact.dischargeRequests(*requests));
          require(exact.complete() && exact.workUsed() == exactWork,
                  "combined-stage exact allowance changed");
          auto shortBudget = take(prepare(realizationWork - 1));
          size_t originalRows = shortBudget.dependencies().size();
          capacity(resolve(shortBudget));
          capacity(resolve(shortBudget));
          zkc::detail::NativeRequestPlan missing;
          capacity(shortBudget.dischargeRequests(missing));
          require(
              !shortBudget.complete() && shortBudget.needsRealization() &&
                  shortBudget.workUsed() == realizationWork - 1 &&
                  shortBudget.dependencies().size() == originalRows,
              "exhausted realization published rows or renewed its allowance");
          if (withRequest) {
            auto shortRequest = take(prepare(exactWork - 1));
            succeed(resolve(shortRequest));
            size_t realizedRows = shortRequest.dependencies().size();
            capacity(shortRequest.dischargeRequests(*requests));
            capacity(shortRequest.dischargeRequests(*requests));
            capacity(resolve(shortRequest));
            require(!shortRequest.complete() &&
                        !shortRequest.needsRealization() &&
                        shortRequest.workUsed() == exactWork - 1 &&
                        shortRequest.dependencies().size() == realizedRows,
                    "request discharge renewed its allowance or published "
                    "completion");
          }
          require(bytes(*module) == original && joint.source() == *module &&
                      &joint.execution() == &execution,
                  "recipe preparation changed its original owner");
          auto incomplete = take(prepare());
          auto error = incomplete.dischargeRequests(missing);
          require(bool(error) && namesIdentifier(
                                     toString(std::move(error)),
                                     "native-construction-preparation-closure"),
                  "request discharge bypassed a declarative recipe obligation");
          protocol_ir::LocalCallOp initialize;
          module->walk([&](protocol_ir::LocalCallOp call) {
            if (call.getCallee() == "init")
              initialize = call;
          });
          require(bool(initialize), "missing actual declarative call");
          initialize.setCalleeAttr(FlatSymbolRefAttr::get(&context, "missing"));
          refuses(prepare(), "native-construction-preparation-closure");
        });
  for (bool selected : {false, true})
    cases.run(
        selected ? "declarative recipes in both selected application arms"
                 : "declarative recipes through a nested application",
        [&] {
          auto text = read("iterated-sumcheck");
          auto name = text.find("sym_name=\"main\"");
          require(name != std::string::npos, "missing recipe entry");
          text.replace(name, StringRef("sym_name=\"main\"").size(),
                       "sym_name=\"inner\"");
          std::string body;
          auto apply = [](StringRef site, StringRef terminator,
                          StringRef prefix = "") {
            auto result = (Twine("%") + prefix + "result").str();
            auto args = (Twine("%") + prefix + "n,%" + prefix + "T,%" + prefix +
                         "U,%" + prefix + "claim,%" + prefix + "coins")
                            .str();
            return (Twine(result) + ":3 = \"protocol.apply\"(" + args + ") " +
                    "{callee=@inner,roles=[\"P\",\"V\"],site=\"" + site +
                    "\"} : (ui64,!t,!t,!f,!rng)->(i1,!p,!f)\n\"" + terminator +
                    "\"(" + result + "#0," + result + "#1," + result +
                    "#2) : (i1,!p,!f)->()\n")
                .str();
          };
          if (selected) {
            // A false selector still requires the actual recipe dependencies in
            // both arms. No native execution of the dormant arm is claimed.
            body =
                "%choice = arith.constant false\n%joined:3 = "
                "\"protocol.branch\""
                "(%choice,%n,%T,%U,%claim,%coins) ({\n"
                "^then(%then_n:ui64,%then_T:!t,%then_U:!t,%then_claim:!f,"
                "%then_coins:!rng):\n" +
                apply("then_recipe", "protocol.yield", "then_") +
                "}, {^else(%else_n:ui64,%else_T:!t,%else_U:!t,%else_claim:!f,"
                "%else_coins:!rng):\n" +
                apply("else_recipe", "protocol.yield", "else_") +
                "}) {site=\"choose_recipe\",roles=[\"P\",\"V\"],"
                "alternatives=[\"then\",\"else\"],"
                "output_roles=[[\"V\"],[\"P\"],[\"P\"]]} : "
                "(i1,ui64,!t,!t,!f,!rng)->(i1,!p,!f)\n"
                "\"protocol.return\"(%joined#0,%joined#1,%joined#2) : "
                "(i1,!p,!f)->()";
          } else {
            body = apply("nested_recipe", "protocol.return");
          }
          std::string wrapper =
              "\"protocol.func\"() "
              "({^entry(%n:ui64,%T:!t,%U:!t,%claim:!f,%coins:!rng):\n" +
              body +
              "\n}) "
              "{sym_name=\"main\",function_type=(ui64,!t,!t,!f,!rng)->(i1,!p,!"
              "f),"
              "roles=[\"P\",\"V\"],input_roles=[[\"P\"],[\"P\",\"V\"],[\"P\","
              "\"V\"],"
              "[\"V\"],[\"V\"]],output_roles=[[\"V\"],[\"P\"],[\"P\"]]} : "
              "()->()\n";
          auto end = text.rfind("}) {profile=");
          require(end != std::string::npos, "missing common module end");
          text.insert(end, wrapper);
          auto module = parse(text);
          require(succeeded(admitStage(*module)),
                  "nested recipe source admission");
          auto original = bytes(*module);
          auto policy = selection();
          policy.producer = "P";
          policy.validator = "V";
          policy.publicInputs = {1, 2, 3};
          auto resolved = take(selectNativeProofDraws(*module, policy));
          require(resolved.draws.size() == (selected ? 2u : 1u),
                  "nested recipe occurrence inventory lost an arm");
          auto built = take(constructNativeProof(*module, resolved));
          if (auto error = checkNativeProof(*module, *built.module, resolved))
            throw std::runtime_error(toString(std::move(error)));
          require(bytes(*module) == original, "nested recipe source changed");
        });
  cases.run(
      "explicit public, role, service and acceptance choices remain mandatory",
      [&] {
        auto module = parse(schnorr);
        auto policy = selection();
        policy.publicInputs.pop_back();
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-public-bindings");
        policy = selection();
        policy.services = {3};
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-verifier-service");
        policy = selection();
        policy.validator = "Nobody";
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-interface");
        policy = selection();
        policy.acceptance = 1;
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-interface");
        policy = selection();
        policy.suite = "uninstalled";
        refuses(selectNativeProofDraws(*module, policy), "native-proof-policy");
        policy = selection();
        policy.draws = {{"draw_challenge", "challenge"}};
        refuses(selectNativeProofDraws(*module, policy), "native-proof-policy");
      });
  cases.run(
      "strict policies still require exact selected occurrence names", [&] {
        auto module = parse(schnorr);
        auto policy = selection();
        refuses(constructNativeProof(*module, policy), "native-proof-policy");
        policy.draws = {{"draw_challenge", "wrong_delivery"}};
        refuses(constructNativeProof(*module, policy),
                "native-proof-reverse-message");
      });
  cases.run("derived delivery must carry the actual query result", [&] {
    auto text = schnorr;
    auto position = text.find("%challenge = protocol.exchange %c");
    require(position != std::string::npos, "missing delivery");
    text.replace(
        position, StringRef("%challenge = protocol.exchange %c").size(),
        "%altered = algebra.field_add %c, %c : "
        "(!algebra.field<\"bls12-381.fr\">, !algebra.field<\"bls12-381.fr\">) "
        "-> !algebra.field<\"bls12-381.fr\">\n%challenge = protocol.exchange "
        "%altered");
    auto module = parse(text);
    refuses(selectNativeProofDraws(*module, selection()),
            "native-proof-reverse-message");
  });
  cases.run("producer messages cannot split query and delivery", [&] {
    auto module = parse(schnorr);
    protocol_ir::ExchangeOp commitment;
    protocol_ir::QueryOp challenge;
    module->walk([&](protocol_ir::ExchangeOp op) {
      if (op.getSite() == "commitment")
        commitment = op;
    });
    module->walk([&](protocol_ir::QueryOp op) {
      if (op.getSite() == "draw_challenge")
        challenge = op;
    });
    require(bool(commitment) && bool(challenge), "missing events");
    commitment->moveAfter(challenge);
    require(succeeded(verify(*module)), "reordered source is ill formed");
    refuses(selectNativeProofDraws(*module, selection()),
            "native-proof-prefix");
  });
  for (bool altered : {false, true})
    cases.run(
        altered ? "nested producer prefix precedes malformed delivery"
                : "nested producer communication splits selected delivery",
        [&] {
          auto text = schnorr;
          auto position = text.find("%challenge = protocol.exchange %c");
          require(position != std::string::npos, "missing selected delivery");
          std::string prefix = "\"protocol.apply\"(%r) "
                               "{callee=@intervening,roles=[\"Alice\",\"Bob\"],"
                               "site=\"intervening_call\"} : "
                               "(!algebra.group<\"bls12-381.g1\">)->()\n";
          if (altered) {
            prefix += "%altered = algebra.field_add %c, %c : "
                      "(!algebra.field<\"bls12-381.fr\">,!algebra.field<"
                      "\"bls12-381.fr\">)"
                      "->!algebra.field<\"bls12-381.fr\">\n";
            text.replace(position,
                         StringRef("%challenge = protocol.exchange %c").size(),
                         "%challenge = protocol.exchange %altered");
          }
          text.insert(position, prefix);
          auto end = text.rfind("}) {profile=");
          require(end != std::string::npos, "missing common source end");
          text.insert(end, R"mlir(
        "protocol.func"() ({^entry(%value:!algebra.group<"bls12-381.g1">):
          %sent = protocol.exchange %value {sender="Sender",receiver="Receiver",site="nested_message"} : !algebra.group<"bls12-381.g1">
          "protocol.return"() : ()->()
        }) {sym_name="intervening",function_type=(!algebra.group<"bls12-381.g1">)->(),
            roles=["Sender","Receiver"],input_roles=[["Sender"]],output_roles=[]} : ()->()
      )mlir");
          auto module = parse(text);
          require(succeeded(admitStage(*module)),
                  "nested prefix source admission");
          refuses(selectNativeProofDraws(*module, selection()),
                  "native-proof-prefix");
        });
  for (StringRef placement :
       {"returned-query", "nested-delivery", "forwarded-query"})
    for (bool altered : {false, true})
      cases.run(
          placement + (altered ? ": actual mutation refuses"
                               : ": actual forwarding is retained"),
          [&] {
            auto text = schnorr;
            std::string helper;
            StringRef addition = R"mlir(
                    %changed = algebra.field_add %value, %value : (!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)->!algebra.field<"bls12-381.fr">
                  )mlir";
            if (placement == "returned-query") {
              auto start = text.find("%c = \"protocol.query\"");
              auto end = text.find('\n', start);
              require(start != std::string::npos && end != std::string::npos,
                      "missing actual selected query");
              text.replace(start, end - start, R"mlir(
                      %c = "protocol.apply"(%challenge_service) {callee=@draw_helper,roles=["Alice","Bob"],site="draw_call"} : (!protocol.service_ref<"random.bls12-381.fr/0">)->!algebra.field<"bls12-381.fr">
                    )mlir");
              helper = R"mlir(
                      "protocol.func"() ({^entry(%service:!protocol.service_ref<"random.bls12-381.fr/0">):
                        %value = "protocol.query"(%service) {method="draw",owner="Receiver",site="draw_challenge"} : (!protocol.service_ref<"random.bls12-381.fr/0">)->!algebra.field<"bls12-381.fr">
                    )mlir";
              if (altered)
                helper += addition;
              helper += altered ? "\"protocol.return\"(%changed)"
                                : "\"protocol.return\"(%value)";
              helper += R"mlir( : (!algebra.field<"bls12-381.fr">)->()
                      }) {sym_name="draw_helper",function_type=(!protocol.service_ref<"random.bls12-381.fr/0">)->!algebra.field<"bls12-381.fr">,
                          roles=["Sender","Receiver"],input_roles=[["Receiver"]],output_roles=[["Receiver"]]} : ()->()
                    )mlir";
            } else {
              auto start = text.find("%challenge = protocol.exchange");
              require(start != std::string::npos,
                      "missing actual query delivery");
              std::string apply = R"mlir(
                      %forwarded = "protocol.apply"(%c) {callee=@delivery_helper,roles=["Alice","Bob"],site="delivery_call"} : (!algebra.field<"bls12-381.fr">)->!algebra.field<"bls12-381.fr">
                    )mlir";
              if (placement == "nested-delivery") {
                auto end = text.find('\n', start);
                require(end != std::string::npos,
                        "missing delivery terminator");
                apply.replace(apply.find("%forwarded"),
                              StringRef("%forwarded").size(), "%challenge");
                text.replace(start, end - start, apply);
              } else {
                text.replace(
                    start,
                    StringRef("%challenge = protocol.exchange %c").size(),
                    "%challenge = protocol.exchange %forwarded");
                text.insert(start, apply);
              }
              helper = R"mlir(
                      "protocol.func"() ({^entry(%value:!algebra.field<"bls12-381.fr">):
                    )mlir";
              if (altered)
                helper += addition;
              if (placement == "nested-delivery") {
                helper += altered ? "%sent = protocol.exchange %changed"
                                  : "%sent = protocol.exchange %value";
                helper +=
                    R"mlir( {sender="Receiver",receiver="Sender",site="challenge"} : !algebra.field<"bls12-381.fr">
                        "protocol.return"(%sent) : (!algebra.field<"bls12-381.fr">)->()
                      )mlir";
              } else {
                helper += altered ? "\"protocol.return\"(%changed)"
                                  : "\"protocol.return\"(%value)";
                helper += " : (!algebra.field<\"bls12-381.fr\">)->()\n";
              }
              helper += R"mlir(
                      }) {sym_name="delivery_helper",function_type=(!algebra.field<"bls12-381.fr">)->!algebra.field<"bls12-381.fr">,
                          roles=["Sender","Receiver"],input_roles=[["Receiver"]],output_roles=[[")mlir";
              helper += placement == "nested-delivery" ? "Sender\",\"Receiver"
                                                       : "Receiver";
              helper += "\"]]} : ()->()\n";
            }
            auto end = text.rfind("}) {profile=");
            require(end != std::string::npos, "missing source module");
            text.insert(end, helper);
            auto module = parse(text);
            require(succeeded(admitStage(*module)),
                    "nested query source admission");
            auto original = bytes(*module);
            if (altered) {
              refuses(selectNativeProofDraws(*module, selection()),
                      "native-proof-reverse-message");
            } else {
              auto policy = take(selectNativeProofDraws(*module, selection()));
              auto proof = take(constructNativeProof(*module, policy));
              if (auto error = checkNativeProof(*module, *proof.module, policy))
                throw std::runtime_error(toString(std::move(error)));
            }
            require(bytes(*module) == original,
                    "nested query preparation mutated original");
          });
  cases.run(
      "owned selection captures preparation diagnostics and locations", [&] {
        // Builtin module attributes pass MLIR formation, but protocol
        // preparation must refuse every attribute it does not own.
        StringRef text =
            R"(module attributes {test.unowned = true} {
          "protocol.module"() ({
            "protocol.func"() ({^entry(%ok:i1):
              "protocol.return"(%ok):(i1)->()
            }) {sym_name="main0",function_type=(i1)->i1,roles=["P","V"],
                input_roles=[["V"]],output_roles=[["V"]]}:()->()
          }) {profile=#protocol.profile<protocol>}:()->()
        })";
        NativeProofPolicy policy;
        policy.entry = "main0";
        policy.producer = "P";
        policy.validator = "V";
        policy.publicInputs = {0};
        NativeProofOptions options{NativeProofSelection{policy}};
        auto result =
            compileNativeProof(text, "selection.mlir", options, registry);
        require(!result, "unowned module metadata reached construction");
        bool captured = false;
        std::string diagnostic;
        auto remaining =
            handleErrors(result.takeError(), [&](const CompilationError &e) {
              diagnostic = e.message;
              captured =
                  namesIdentifier(e.message, "native-proof-preparation") &&
                  namesIdentifier(e.message, "mathematical-module") &&
                  any_of(e.locations, [](const DiagnosticLocation &location) {
                    return location.filename == "selection.mlir" &&
                           location.line;
                  });
            });
        if (remaining)
          throw std::runtime_error(toString(std::move(remaining)));
        require(captured,
                "selection lost owned preparation diagnostics or location: " +
                    diagnostic);
      });
  cases.run("authored selection retains an empty construction explicitly", [&] {
    auto module = parse(R"(module { "protocol.module"() ({
      "protocol.func"() ({^entry(%ok:i1): "protocol.return"(%ok):(i1)->()
      }) {sym_name="main",function_type=(i1)->i1,roles=["P","V"],
          input_roles=[["V"]],output_roles=[["V"]]}:()->()
    }) {profile=#protocol.profile<protocol>}:()->() })");
    NativeProofPolicy policy;
    policy.entry = "main";
    policy.producer = "P";
    policy.validator = "V";
    policy.publicInputs = {0};
    auto resolved = take(selectNativeProofDraws(*module, policy));
    require(resolved.draws.empty() && resolved.suite.empty(),
            "authored policy changed");
    take(constructNativeProof(*module, resolved));
  });
  return cases.result();
}
