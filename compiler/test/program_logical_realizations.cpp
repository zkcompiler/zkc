#include "../lib/Program/Structure.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::test;

namespace {
const std::string field = "field:bls12-381.fr";
const std::string transcript = "transcript:merlin3.bls12-381.fr64be/0";

void accept(Error result) {
  if (result)
    throw std::runtime_error(toString(std::move(result)));
}
void refuse(Error result, StringRef code) {
  require(bool(result), Twine("expected refusal: ") + code);
  auto message = toString(std::move(result));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
protocol::LocalRealization realization() {
  return {"kernel_entry", {field}, {field}};
}
program::Instruction apply(std::string site, std::string input,
                           std::string output) {
  return {std::move(site), program::LocalApply{"kernel_entry",
                                               {std::move(input)},
                                               {std::move(output)}}};
}
program::Participants fixture() {
  program::Participants model;
  program::Function function;
  function.name = "compute";
  function.origin = program::LogicalOrigin{"compute", {}};
  function.arguments = {{"x", field}, {"condition", "bool"}};
  function.results = {field};
  function.body = {apply("invoke", "x", "result"),
                   {"", program::Return{{"result"}}}};
  model.functions.push_back(std::move(function));
  program::Participant participant;
  participant.name = "prover";
  participant.instance = "main";
  participant.role = "P";
  participant.arguments = {{"x", field}, {"condition", "bool"}};
  participant.results = {field};
  participant.body = {
      {"compute",
       program::LocalCall{"compute", {"x", "condition"}, {"result"}}},
      {"", program::Return{{"result"}}}};
  model.participants.push_back(std::move(participant));
  model.entries.push_back({"entry", {{"P", "prover"}}});
  return model;
}
program::Participants conditionalFixture() {
  auto model = fixture();
  model.functions[0].body = {
      {"choose",
       program::Conditional{
           "condition",
           {"x"},
           {apply("left", "x", "a"), {"", program::Yield{{"a"}}}},
           {apply("right", "x", "b"), {"", program::Yield{{"b"}}}},
           {"result"}}},
      {"", program::Return{{"result"}}}};
  return model;
}
program::Participants loopFixture() {
  auto model = fixture();
  // Bounds are local-only test inputs; this dormant local still must admit.
  model.functions[0].name = "iterate";
  model.functions[0].arguments = {
      {"x", field}, {"lower", "index"}, {"upper", "index"}};
  model.functions[0].body = {
      {"iterate", program::For{"i",
                               "lower",
                               "upper",
                               {{"state", "x"}},
                               {},
                               {apply("step", "state", "next"),
                                {"", program::Yield{{"next"}}}},
                               {"result"}}},
      {"", program::Return{{"result"}}}};
  auto compute = fixture().functions.front();
  model.functions.push_back(std::move(compute));
  return model;
}
program::Participants matchFixture() {
  auto model = fixture();
  auto variant = protocol::encodeVariant(
      {"Choice", {{"Left", {field}}, {"Right", {field}}}});
  require(bool(variant), "variant fixture refused");
  model.functions[0].body = {
      {"pack", program::VariantConstruct{*variant, "Left", {"x"}, "choice"}},
      {"match",
       program::Match{
           "choice",
           {},
           {{"Left",
             {"x"},
             {apply("left", "x", "a"), {"", program::Yield{{"a"}}}}},
            {"Right",
             {"x"},
             {apply("right", "x", "b"), {"", program::Yield{{"b"}}}}}},
           {"result"}}},
      {"", program::Return{{"result"}}}};
  return model;
}
} // namespace

int main() {
  Cases cases;
  const auto signature = realization();
  cases.run("explicit Total realization in a logical local function",
            [&] { accept(protocol::admit(fixture(), {signature})); });
  cases.run("unused Total signature needs no fake function body", [&] {
    auto model = fixture();
    model.functions[0].body = {{"", program::Return{{"x"}}}};
    accept(protocol::admit(model));
    accept(protocol::admit(model, {}));
    accept(protocol::admit(model, {signature}));
  });
  cases.run("default logical admission still refuses LocalApply", [&] {
    refuse(protocol::admit(fixture()), "algorithm-call-context");
  });
  cases.run("empty internal signatures do not resolve calls", [&] {
    refuse(protocol::admit(fixture(), {}), "algorithm-call-symbol");
  });
  cases.run("missing realization refuses", [&] {
    auto model = fixture();
    model.functions[0].body[0].get<program::LocalApply>()->callee = "missing";
    refuse(protocol::admit(model, {signature}), "algorithm-call-symbol");
  });
  cases.run("ordinary local applications stay forbidden in logical Exec", [&] {
    auto model = fixture();
    auto helper = model.functions.front();
    helper.name = "helper";
    helper.body = {{"", program::Return{{"x"}}}};
    model.functions.push_back(std::move(helper));
    model.functions[0].body[0].value =
        program::LocalApply{"helper", {"x", "condition"}, {"result"}};
    refuse(protocol::admit(model, {signature}), "algorithm-call-context");
  });
  cases.run("participant cannot apply a realization directly", [&] {
    auto model = fixture();
    model.participants[0].body[0] = apply("invoke", "x", "result");
    refuse(protocol::admit(model, {signature}), "algorithm-call-context");
  });
  cases.run("participant LocalCall cannot resolve a realization", [&] {
    auto model = fixture();
    model.participants[0].body[0].value =
        program::LocalCall{"kernel_entry", {"x"}, {"result"}};
    refuse(protocol::admit(model, {signature}), "interactive-local-symbol");
  });
  cases.run("internal overload refuses physical even without signatures", [&] {
    auto model = fixture();
    model.stage = program::Participants::Stage::Physical;
    refuse(protocol::admit(model, {signature}), "local-realization-context");
    refuse(protocol::admit(model, {}), "local-realization-context");
    refuse(protocol::admit(model), "algorithm-call-context");
  });
  cases.run("structure opt-in is internal and logical only", [&] {
    auto model = fixture();
    accept(program::detail::checkNativeIRStructure(model, true));
    refuse(program::detail::checkNativeIRStructure(model),
           "algorithm-call-context");
    refuse(program::checkStructure(model), "native-physical-required");
    model.stage = program::Participants::Stage::Physical;
    refuse(program::detail::checkNativeIRStructure(model, true),
           "algorithm-call-context");
    refuse(program::checkStructure(model), "algorithm-call-context");
  });
  cases.run("decoder still has no apply opcode", [&] {
    auto model = fixture();
    model.stage = program::Participants::Stage::Physical;
    model.functions[0].body = {{"", program::Return{{"x"}}}};
    accept(program::checkStructure(model));
    auto encoded = program::encode(model);
    auto &function =
        *(*encoded.getAsArray())[2].getAsArray()->front().getAsArray();
    (*function[4].getAsArray())[0] =
        json::Array{"apply", "invoke", "kernel_entry", json::Array{"x"},
                    json::Array{"result"}};
    refuses(program::decode(encoded), "interactive-instruction");
  });
  for (auto kind : {protocol::LocalRealization::Kind::FiniteFold,
                    protocol::LocalRealization::Kind::FiniteCollect})
    cases.run(
        kind == protocol::LocalRealization::Kind::FiniteFold
            ? "finite fold realization requires actual callback bodies"
            : "finite collect realization requires actual callback bodies",
        [&] {
          auto finite = signature;
          finite.kind = kind;
          refuse(protocol::admit(fixture(), {finite}),
                 "local-realization-callback");
          finite.callbacks = {"callback"};
          refuse(protocol::admit(fixture(), {finite}),
                 "local-realization-callback");
          auto model = fixture();
          program::Function callback;
          callback.name = "callback";
          callback.origin = program::LogicalOrigin{"callback", {}};
          callback.arguments = {{"x", field}};
          callback.results = {field};
          callback.body = {{"", program::Return{{"x"}}}};
          model.functions.push_back(std::move(callback));
          accept(protocol::admit(model, {finite}));
          auto cyclic = model;
          cyclic.functions.back().body = {
              {"recursive", program::LocalApply{finite.name, {"x"}, {"next"}}},
              {"", program::Return{{"next"}}}};
          refuse(protocol::admit(cyclic, {finite}), "interactive-call-cycle");
          finite.callbacks = {"prover"};
          refuse(protocol::admit(model, {finite}),
                 "local-realization-callback");
          finite.callbacks = {"total"};
          auto total = signature;
          total.name = "total";
          refuse(protocol::admit(model, {finite, total}),
                 "local-realization-callback");
        });
  for (const auto &port : {std::string("polynomial:bls12-381.fr"), transcript,
                           std::string("bool@native.bool/0")})
    cases.run("non-total, affine or physical signature refuses: " + port, [&] {
      auto invalid = signature;
      invalid.inputs = {port};
      // Both APIs must retain exactly the existing Total port refusal.
      auto prior = protocol::admitNativeLocalDefinitions({}, {invalid});
      require(bool(prior), "native-local Total port unexpectedly admitted");
      auto code = toString(std::move(prior));
      refuse(protocol::admit(fixture(), {invalid}), code);
    });
  cases.run("non-total output also refuses", [&] {
    auto invalid = signature;
    invalid.outputs = {transcript};
    refuse(protocol::admit(fixture(), {invalid}),
           "local-realization-signature");
  });
  cases.run("invalid realization domain count refuses", [&] {
    auto invalid = signature;
    invalid.domainArguments = 2;
    refuse(protocol::admit(fixture(), {invalid}),
           "local-realization-signature");
  });
  cases.run("duplicate realization names refuse", [&] {
    refuse(protocol::admit(fixture(), {signature, signature}),
           "local-realization-symbol");
  });
  for (const auto &name : {"compute", "prover", "entry"})
    cases.run(Twine("realization cannot shadow symbol: ") + name, [&] {
      auto invalid = signature;
      invalid.name = name;
      auto model = fixture();
      model.functions[0].body[0].get<program::LocalApply>()->callee = name;
      refuse(protocol::admit(model, {invalid}),
             StringRef(name) == "entry" ? "interactive-entry-name"
                                        : "interactive-duplicate-symbol");
    });
  cases.run("wrong nominal call input refuses", [&] {
    auto model = fixture();
    model.functions[0].body[0].get<program::LocalApply>()->inputs = {
        "condition"};
    refuse(protocol::admit(model, {signature}), "algorithm-call-signature");
  });
  cases.run("wrong call input arity refuses", [&] {
    auto model = fixture();
    model.functions[0].body[0].get<program::LocalApply>()->inputs = {"x", "x"};
    refuse(protocol::admit(model, {signature}), "algorithm-call-signature");
  });
  cases.run("wrong call output arity refuses", [&] {
    auto model = fixture();
    model.functions[0].body[0].get<program::LocalApply>()->outputs.clear();
    refuse(protocol::admit(model, {signature}), "interactive-shape");
  });
  cases.run("call results must satisfy the declared return types", [&] {
    auto invalid = signature;
    invalid.outputs = {"bool"};
    refuse(protocol::admit(fixture(), {invalid}), "function-return-types");
  });
  cases.run("call operands obey SSA availability", [&] {
    auto model = fixture();
    model.functions[0].body[0].get<program::LocalApply>()->inputs = {"missing"};
    refuse(protocol::admit(model, {signature}), "interactive-unavailable");
  });
  cases.run("call results cannot rebind an SSA input", [&] {
    auto model = fixture();
    model.functions[0].body[0].get<program::LocalApply>()->outputs = {"x"};
    refuse(protocol::admit(model, {signature}), "interactive-ssa");
  });
  cases.run("realization calls retain affine accounting in the caller", [&] {
    auto model = fixture();
    auto affine = model.functions.front();
    affine.name = "with_state";
    affine.arguments.push_back({"state", transcript});
    affine.results.push_back(transcript);
    affine.body.back().value = program::Return{{"result", "state"}};
    model.functions.push_back(std::move(affine));
    accept(protocol::admit(model, {signature}));
    model.functions.back().body.back().value =
        program::Return{{"result", "state", "state"}};
    refuse(protocol::admit(model, {signature}), "interactive-resource-reuse");
  });
  cases.run("realization calls are admitted in both conditional arms", [&] {
    accept(protocol::admit(conditionalFixture(), {signature}));
  });
  cases.run("conditional calls cannot access uncaptured values", [&] {
    auto model = conditionalFixture();
    model.functions[0].body[0].get<program::Conditional>()->captures.clear();
    refuse(protocol::admit(model, {signature}), "interactive-unavailable");
  });
  cases.run("conditional calls share the enclosing site namespace", [&] {
    auto model = conditionalFixture();
    auto &branch = *model.functions[0].body[0].get<program::Conditional>();
    branch.elseBody[0].site = "left";
    refuse(protocol::admit(model, {signature}), "interactive-site");
  });
  cases.run("realization calls are admitted in local finite loops",
            [&] { accept(protocol::admit(loopFixture(), {signature})); });
  cases.run("local loop yield types remain exact", [&] {
    auto model = loopFixture();
    auto &loop = *model.functions[0].body[0].get<program::For>();
    loop.body.back().value = program::Yield{{"i"}};
    refuse(protocol::admit(model, {signature}), "local-yield-types");
  });
  cases.run("realization calls are admitted in every match arm",
            [&] { accept(protocol::admit(matchFixture(), {signature})); });
  cases.run("even an unselected match arm must resolve its call", [&] {
    auto model = matchFixture();
    auto &match = *model.functions[0].body[1].get<program::Match>();
    match.arms[1].body[0].get<program::LocalApply>()->callee = "missing";
    refuse(protocol::admit(model, {signature}), "algorithm-call-symbol");
  });
  cases.run("logical operation contracts are still checked", [&] {
    auto model = fixture();
    model.functions[0].body.insert(
        model.functions[0].body.begin(),
        {"operation", program::Operation{"missing", {}, {}, {}}});
    refuse(protocol::admit(model, {signature}), "binding-reference");
  });
  cases.run("signature count shares the definition bound", [&] {
    std::vector<protocol::LocalRealization> signatures;
    for (unsigned i = 0; i < 4095; ++i)
      signatures.push_back({"kernel_" + std::to_string(i), {}, {}});
    refuse(protocol::admit(fixture(), signatures),
           "interactive-definition-limit");
  });
  cases.run("native-local ordinary application and cycle checks survive", [&] {
    auto model = fixture();
    program::LocalDefinitions locals{{}, model.functions};
    accept(protocol::admitNativeLocalDefinitions(locals, {signature}));
    auto &call = *locals.functions[0].body[0].get<program::LocalApply>();
    call.callee = "compute";
    call.inputs = {"x", "condition"};
    refuse(protocol::admitNativeLocalDefinitions(locals, {signature}),
           "interactive-call-cycle");
  });
  cases.run(
      "native-local finite realizations retain actual callback bodies", [&] {
        program::Function callback;
        callback.name = "callback";
        callback.origin = program::LogicalOrigin{"callback", {}};
        callback.arguments = {{"state", transcript}};
        callback.results = {transcript};
        callback.body = {{"", program::Return{{"state"}}}};
        program::LocalDefinitions locals{{}, {callback}};
        auto fold = signature;
        fold.kind = protocol::LocalRealization::Kind::FiniteFold;
        fold.inputs = fold.outputs = {transcript};
        fold.callbacks = {"callback"};
        accept(protocol::admitNativeLocalDefinitions(locals, {fold}));
        auto collect = signature;
        collect.kind = protocol::LocalRealization::Kind::FiniteCollect;
        collect.callbacks = {"callback"};
        accept(protocol::admitNativeLocalDefinitions(locals, {collect}));
        refuse(protocol::admitNativeLocalDefinitions({}, {fold}),
               "local-realization-callback");
        fold.callbacks.clear();
        refuse(protocol::admitNativeLocalDefinitions(locals, {fold}),
               "local-realization-callback");
        fold.callbacks = {"callback"};
        locals.functions[0].body = {
            {"recursive", program::LocalApply{fold.name, {"state"}, {"next"}}},
            {"", program::Return{{"next"}}}};
        refuse(protocol::admitNativeLocalDefinitions(locals, {fold}),
               "interactive-call-cycle");
      });
  cases.run("finite callback edges cannot point to another signature", [&] {
    auto fold = signature;
    fold.kind = protocol::LocalRealization::Kind::FiniteFold;
    fold.callbacks = {"total"};
    auto total = signature;
    total.name = "total";
    refuse(protocol::admitNativeLocalDefinitions({}, {fold, total}),
           "local-realization-callback");
    total.callbacks = {"callback"};
    refuse(protocol::admitNativeLocalDefinitions({}, {total}),
           "local-realization-callback");
  });
  cases.run("match cannot hide history behind a finite callback chain", [&] {
    program::Function draw;
    draw.name = "draw";
    draw.origin = program::LogicalOrigin{"draw", {}};
    draw.arguments = {{"state", transcript}, {"label", "bytes"}};
    draw.results = {transcript};
    draw.body = {{"challenge",
                  program::Operation{
                      "challenge", {}, {"state", "label"}, {"next", "sample"}}},
                 {"", program::Return{{"next"}}}};
    auto step = draw;
    step.name = "step";
    step.origin = program::LogicalOrigin{"step", {}};
    step.body = {
        {"helper", program::LocalApply{"draw", {"state", "label"}, {"next"}}},
        {"", program::Return{{"next"}}}};
    auto fold = signature;
    fold.kind = protocol::LocalRealization::Kind::FiniteFold;
    fold.domainArguments = 1;
    fold.inputs = {"bytes", transcript};
    fold.outputs = {transcript};
    fold.callbacks = {"step"};
    auto caller = draw;
    caller.name = "caller";
    caller.origin = program::LogicalOrigin{"caller", {}};
    caller.body = {
        {"finite",
         program::LocalApply{fold.name, {"label", "state"}, {"next"}}},
        {"", program::Return{{"next"}}}};
    program::LocalDefinitions locals{
        {{"challenge",
          {"transcript.challenge", {"merlin3.bls12-381.fr64be/0"}, ""}}},
        {caller, step, draw}};
    accept(protocol::admitNativeLocalDefinitions(locals, {fold}));
    auto variant =
        protocol::encodeVariant({"Choice", {{"Left", {}}, {"Right", {}}}});
    require(bool(variant), "finite match variant refused");
    program::Body arm = {
        {"finite",
         program::LocalApply{fold.name, {"label", "state"}, {"next"}}},
        {"", program::Yield{{"next"}}}};
    locals.functions[0].body = {
        {"choice", program::VariantConstruct{*variant, "Left", {}, "choice"}},
        {"match", program::Match{"choice",
                                 {"state", "label"},
                                 {{"Left", {}, arm}, {"Right", {}, arm}},
                                 {"next"}}},
        {"", program::Return{{"next"}}}};
    refuse(protocol::admitNativeLocalDefinitions(locals, {fold}),
           "local-match-challenge");
  });
  return cases.result();
}
