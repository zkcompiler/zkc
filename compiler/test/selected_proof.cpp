#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
constexpr StringLiteral sourceText = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!Rng = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%choice:i1,%secret:!F,%coins:!Rng,%go:i1,%rounds:ui64):
  %accepted = "protocol.branch"(%choice,%secret,%coins,%go,%rounds) ({
  ^then(%x:!F,%random:!Rng,%enabled:i1,%count:ui64):
   %commitment = protocol.exchange %x {site="commitment",sender="P",receiver="V"} : !F
   GUARD
   %challenge = "protocol.query"(%random) {site="draw",owner="V",method="draw"} : (!Rng)->!F
   %delivered = protocol.exchange %challenge {site="delivery",sender="V",receiver="P"} : !F
   %answer = "algebra.field_add"(%x,%delivered) : (!F,!F)->!F
   %response = protocol.exchange %answer {site="response",sender="P",receiver="V"} : !F
   %expected = "algebra.field_add"(%commitment,%challenge) : (!F,!F)->!F
   %same = "algebra.field_equal"(%response,%expected) : (!F,!F)->i1
   COMPLETION
   "protocol.yield"(%same) : (i1)->()
  }, {
  ^else(%unused:!F,%unreached:!Rng,%continuing:i1,%trips:ui64):
   %yes = arith.constant true
   "protocol.yield"(%yes) : (i1)->()
  }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["then","else"]} : (i1,!F,!Rng,i1,ui64)->i1
  "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(i1,!F,!Rng,i1,ui64)->i1,roles=["P","V"],input_roles=[["P","V"],["P"],["V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
std::string text(bool guard, bool completion) {
  std::string result = sourceText.str();
  result.replace(result.find("GUARD"), 5,
                 guard ? "protocol.guard %enabled {site=\"guard\",owner=\"V\"}"
                       : "");
  result.replace(result.find("COMPLETION"), 10,
                 completion ? R"mlir(
       "protocol.finish_if"(%enabled) {site="complete_P",owner="P"} : (i1)->()
       "protocol.finish_if"(%enabled,%same) {site="complete_V",owner="V"} : (i1,i1)->()
      )mlir"
                            : "");
  return result;
}
std::string printed(ModuleOp module) {
  std::string value;
  raw_string_ostream stream(value);
  module.print(stream);
  return value;
}
NativeProofPolicy selection(StringRef suite = "merlin3.bls12-381.fr64be/0") {
  NativeProofPolicy policy;
  policy.entry = "main";
  policy.producer = "P";
  policy.validator = "V";
  policy.acceptance = 0;
  policy.suite = suite.str();
  policy.services = {2};
  policy.publicInputs = {0, 3, 4};
  return policy;
}
OwningOpRef<ModuleOp> source(MLIRContext &context, bool guard = false,
                             bool completion = false) {
  auto module = parseSourceString<ModuleOp>(text(guard, completion), &context);
  require(bool(module) && succeeded(admitStage(*module)), "source admission");
  return module;
}
void checkOrigins(const NativeProofConstruction &built) {
  auto descriptor = built.descriptor.getAsArray();
  require(descriptor && descriptor->size() == 9, "descriptor shape");
  auto events = (*descriptor)[3].getAsArray();
  require(events && events->size() == 4, "all-arm static inventory");
  for (auto &row : *events) {
    auto event = row.getAsArray();
    auto origin =
        take(protocol::decodeNativeOriginTemplate(*(*event)[1].getAsString()));
    require(origin.path.size() == 1 &&
                origin.path[0].kind ==
                    protocol::NativeOriginStep::Kind::Branch &&
                origin.path[0].site == "choose" &&
                origin.path[0].alternative == "then",
            "branch origin does not match actual selected arm");
  }
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (StringRef suite : {"merlin3.bls12-381.fr64be/0",
                          "hash-chain.keccak256.bls12-381.fr64be/0"})
    for (bool guard : {false, true})
      for (bool completion : {false, true})
        cases.run(
            Twine("selected native construction suite=") + suite +
                " guard=" + Twine(guard) + " completion=" + Twine(completion),
            [&] {
              auto original = source(context, guard, completion);
              auto before = printed(*original);
              auto policy =
                  take(selectNativeProofDraws(*original, selection(suite)));
              require(policy.draws ==
                          std::vector<std::pair<std::string, std::string>>{
                              {"draw", "delivery"}},
                      "wrong selected challenge pair");
              auto built = take(constructNativeProof(*original, policy));
              require(succeeded(admitStage(*built.module)),
                      "candidate admission");
              if (auto error =
                      checkNativeProof(*original, *built.module, policy))
                throw std::runtime_error(toString(std::move(error)));
              checkOrigins(built);
              require(printed(*original) == before,
                      "source changed during construction");
            });
  for (StringRef role : {"P", "V"})
    for (StringRef mutation :
         {"selector", "label", "state capture", "state successor"})
      cases.run(Twine(role) + " candidate mutation " + mutation, [&] {
        auto original = source(context);
        auto policy = take(selectNativeProofDraws(*original, selection()));
        auto built = take(constructNativeProof(*original, policy));
        pir::ParticipantBranchOp branch;
        built.module->walk([&](pir::ParticipantOp participant) {
          if (participant.getRole() == role)
            participant.walk(
                [&](pir::ParticipantBranchOp selected) { branch = selected; });
        });
        require(bool(branch), "missing actual selected branch");
        if (mutation == "selector") {
          Value alternate;
          for (Value input : branch.getInputs().drop_front())
            if (input.getType().isInteger(1))
              alternate = input;
          require(bool(alternate), "missing distinct Boolean capture");
          branch->setOperand(0, alternate);
        } else if (mutation == "label") {
          branch.setAlternativesAttr(
              ArrayAttr::get(&context, {StringAttr::get(&context, "else"),
                                        StringAttr::get(&context, "then")}));
        } else if (mutation == "state capture") {
          // A peer's managed root has the same type but is not this
          // participant's source capture and does not dominate its region.
          auto input = branch.getInputs().back();
          Value other;
          built.module->walk([&](pir::ParticipantOp participant) {
            if (participant.getRole() != role)
              for (Value argument :
                   participant.getBody().front().getArguments())
                if (argument.getType() == input.getType())
                  other = argument;
          });
          require(other && other != input, "missing distinct peer state");
          branch->setOperand(branch.getNumOperands() - 1, other);
        } else {
          auto &arm = branch.getArms()[0].front();
          arm.back().setOperand(arm.back().getNumOperands() - 1,
                                arm.getArguments().back());
        }
        auto error = checkNativeProof(*original, *built.module, policy);
        require(bool(error), "changed selected candidate accepted");
        consumeError(std::move(error));
      });
  return cases.result();
}
