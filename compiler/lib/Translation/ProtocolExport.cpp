#include "../Dialect/Verification.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Builders.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Relations.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
class Exporter {
  Operation *root;
  StringRef stage;
  bool common, physical;
  std::string problem;
  unsigned next = 0;
  std::map<std::string, std::map<std::string, std::string>> argumentRenamings;
  using Env = llvm::DenseMap<mlir::Value, std::string>;
  void fail(StringRef why) {
    if (problem.empty())
      problem = why.str();
  }
  bool attributes(Operation *op, ArrayRef<StringRef> allowed) {
    for (auto a : op->getAttrs())
      if (!is_contained(allowed, a.getName().getValue())) {
        fail("interactive-unknown-attribute");
        return false;
      }
    return true;
  }
  source::Names strings(ArrayAttr attrs,
                        StringRef code = "interactive-attribute") {
    if (!attrs) {
      fail(code);
      return {};
    }
    source::Names out;
    for (auto a : attrs) {
      auto s = dyn_cast<StringAttr>(a);
      if (!s) {
        fail(code);
        return {};
      }
      out.push_back(s.getValue().str());
    }
    return out;
  }
  source::ParameterBindings parameterBindings(ArrayAttr attrs) {
    source::ParameterBindings out;
    if (!attrs) {
      fail("interactive-family-binding");
      return out;
    }
    for (auto a : attrs) {
      auto p = dyn_cast<ArrayAttr>(a);
      if (!p || p.size() != 2 || !isa<StringAttr>(p[0])) {
        fail("interactive-family-binding");
        return {};
      }
      source::ParameterBinding value;
      if (auto constant = dyn_cast<StringAttr>(p[1]))
        value = constant.str();
      else {
        auto ingress = dyn_cast<ArrayAttr>(p[1]);
        if (!ingress || ingress.size() != 3 ||
            ingress[0] != StringAttr::get(root->getContext(), "ingress") ||
            !isa<StringAttr>(ingress[1]) || !isa<ArrayAttr>(ingress[2])) {
          fail("interactive-family-binding");
          return {};
        }
        source::FamilyIngress family{cast<StringAttr>(ingress[1]).str(), {}};
        for (auto a : cast<ArrayAttr>(ingress[2])) {
          auto s = dyn_cast<ArrayAttr>(a);
          if (!s || s.size() != 3 || !isa<StringAttr>(s[0]) ||
              !isa<FlatSymbolRefAttr>(s[1]) || !isa<ArrayAttr>(s[2])) {
            fail("interactive-family-binding");
            return {};
          }
          family.selectors.push_back(
              {cast<StringAttr>(s[0]).str(),
               cast<FlatSymbolRefAttr>(s[1]).getValue().str(),
               strings(cast<ArrayAttr>(s[2]))});
        }
        value = std::move(family);
      }
      out.emplace_back(cast<StringAttr>(p[0]).str(), std::move(value));
    }
    return out;
  }
  source::Assignments pairs(ArrayAttr attrs, bool symbols = false) {
    if (!attrs) {
      fail("interactive-attribute");
      return {};
    }
    source::Assignments out;
    for (auto a : attrs) {
      auto p = dyn_cast<ArrayAttr>(a);
      if (!p || p.size() != 2 || !isa<StringAttr>(p[0]) ||
          (symbols ? !isa<FlatSymbolRefAttr>(p[1]) : !isa<StringAttr>(p[1]))) {
        fail("interactive-binding-attribute");
        return {};
      }
      out.emplace_back(cast<StringAttr>(p[0]).getValue().str(),
                       (symbols ? cast<FlatSymbolRefAttr>(p[1]).getValue()
                                : cast<StringAttr>(p[1]).getValue())
                           .str());
    }
    return out;
  }
  std::string fresh() { return "v" + std::to_string(next++); }
  std::vector<source::Dependency> dependencies(ArrayAttr attrs) {
    if (!attrs) {
      fail("interactive-attribute");
      return {};
    }
    std::vector<source::Dependency> out;
    for (auto a : attrs) {
      auto p = dyn_cast<ArrayAttr>(a);
      if (!p || p.size() != 3 || !isa<StringAttr>(p[0]) ||
          !isa<FlatSymbolRefAttr>(p[1]) || !isa<ArrayAttr>(p[2])) {
        fail("interactive-dependency-attribute");
        return {};
      }
      source::Dependency dependency;
      dependency.name = cast<StringAttr>(p[0]).getValue().str();
      dependency.protocol = cast<FlatSymbolRefAttr>(p[1]).getValue().str();
      dependency.agreements = pairs(cast<ArrayAttr>(p[2]));
      out.push_back(std::move(dependency));
    }
    return out;
  }
  std::string type(Type t) {
    auto value = encodeBoundType(t, physical);
    if (!value) {
      consumeError(value.takeError());
      fail("binding-type");
      return "invalid";
    }
    return value->spelling();
  }
  source::Names names(ValueRange values, const Env &env) {
    source::Names out;
    for (auto v : values) {
      auto p = env.find(v);
      if (p == env.end()) {
        fail("interactive-ssa");
        return {};
      }
      out.push_back(p->second);
    }
    return out;
  }
  std::string name(mlir::Value v, const Env &env) {
    auto p = env.find(v);
    if (p == env.end()) {
      fail("interactive-ssa");
      return "invalid";
    }
    return p->second;
  }
  source::Names results(Operation *op, Env &env) {
    source::Names out;
    for (auto v : op->getResults()) {
      std::string n = fresh();
      env[v] = n;
      out.push_back(n);
    }
    return out;
  }
  FunctionType signature(Operation *op) {
    auto a = op ? op->getAttrOfType<TypeAttr>("function_type") : TypeAttr();
    auto t = a ? dyn_cast<FunctionType>(a.getValue()) : FunctionType();
    if (!t)
      fail("interactive-callable-type");
    return t;
  }
  bool callTypes(Operation *op, StringRef callee) {
    Operation *definition = SymbolTable::lookupSymbolIn(root, callee);
    FunctionType ft = signature(definition);
    return (ft && op->getOperandTypes() == ft.getInputs() &&
            op->getResultTypes() == ft.getResults()) ||
           (fail("interactive-call-type"), false);
  }
  source::Body body(Block &block, Env env, TypeRange outputs,
                    Operation *definition, bool local,
                    bool localRegion = false) {
    source::Body out;
    if (block.empty()) {
      fail("interactive-empty-body");
      return {};
    }
    for (auto &operation : block) {
      Operation *op = &operation;
      std::string site = attr(op, "site").str();
      if (isa<LocalYieldOp>(op)) {
        auto *parent = op->getParentOp();
        unsigned forwarded = isa<LocalForOp>(parent)
                                 ? block.getNumArguments() - 1 - outputs.size()
                                 : 0;
        if (!localRegion || !attributes(op, {}) || op != &block.back() ||
            op->getNumOperands() != outputs.size() + forwarded ||
            op->getOperands().take_front(outputs.size()).getTypes() !=
                outputs) {
          fail("local-control-yield");
          return {};
        }
        for (unsigned i = 0; i < forwarded; ++i)
          if (op->getOperand(outputs.size() + i) !=
              block.getArgument(block.getNumArguments() - forwarded + i)) {
            fail("local-control-capture-forwarding");
            return {};
          }
        out.push_back(
            {{},
             "",
             source::Yield{
                 names(op->getOperands().take_front(outputs.size()), env)}});
      } else if (isa<func::ReturnOp, FinishOp, ProtocolYieldOp>(op)) {
        if (localRegion || !attributes(op, {}) || op != &block.back() ||
            op->getOperandTypes() != outputs ||
            (local != isa<func::ReturnOp>(op))) {
          fail("interactive-return-type");
          return {};
        }
        source::Instruction instruction;
        if (isa<ProtocolYieldOp>(op))
          instruction.value = source::Yield{names(op->getOperands(), env)};
        else
          instruction.value = source::Return{names(op->getOperands(), env)};
        out.push_back(std::move(instruction));
      } else if (isa<ReleaseOp>(op)) {
        if (!physical || !local || !attributes(op, {})) {
          fail("interactive-release-context");
          return {};
        }
        out.push_back({{}, "", source::Release{names(op->getOperands(), env)}});
      } else if (isa<IncompleteOp>(op)) {
        if (common || local || !attributes(op, {"site"}) ||
            op != &block.back()) {
          fail("interactive-incomplete");
          return {};
        }
        out.push_back({{}, site, source::Incomplete{}});
      } else if (isa<HaltOp>(op)) {
        if (!attributes(op, {"site", "reason", "role"}) ||
            op != &block.back()) {
          fail("interactive-halt");
          return {};
        }
        if (!common && op->hasAttr("role")) {
          fail("interactive-foreign-role-attribute");
          return {};
        }
        out.push_back({{},
                       site,
                       source::Stop{common ? attr(op, "role").str() : "",
                                    attr(op, "reason").str()}});
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        if (!common || !local || !attributes(op, {"site", "callee"}) ||
            !callTypes(op, call.getCallee())) {
          fail("algorithm-call-context");
          return {};
        }
        out.push_back({{},
                       site,
                       source::AlgorithmCall{call.getCallee().str(),
                                             names(op->getOperands(), env),
                                             results(op, env)}});
      } else if (isa<LocalCallOp, ParticipantCallOp, ProtocolCallOp>(op)) {
        if (!attributes(op, {"site", "role", "callee", "dependency"}))
          return {};
        bool isLocal = isa<LocalCallOp>(op),
             isDependency = isa<ProtocolCallOp>(op);
        StringRef callee;
        if (isDependency) {
          if (!common) {
            fail("interactive-unprojected-call");
            return {};
          }
          auto deps = definition->getAttrOfType<ArrayAttr>("dependencies");
          if (!deps) {
            fail("interactive-dependency");
            return {};
          }
          for (auto v : deps) {
            auto p = dyn_cast<ArrayAttr>(v);
            if (p && p.size() == 3 && isa<StringAttr>(p[0]) &&
                isa<FlatSymbolRefAttr>(p[1]) &&
                cast<StringAttr>(p[0]).getValue() == attr(op, "dependency"))
              callee = cast<FlatSymbolRefAttr>(p[1]).getValue();
          }
        } else if (auto ref = op->getAttrOfType<FlatSymbolRefAttr>("callee"))
          callee = ref.getValue();
        if (callee.empty() || !callTypes(op, callee)) {
          fail("interactive-call-symbol");
          return {};
        }
        if ((!isLocal || !common) && op->hasAttr("role")) {
          fail("interactive-role-attribute");
          return {};
        }
        auto args = names(op->getOperands(), env), result = results(op, env);
        if (isLocal)
          out.push_back({{},
                         site,
                         source::LocalCall{common ? attr(op, "role").str() : "",
                                           callee.str(), std::move(args),
                                           std::move(result)}});
        else
          out.push_back(
              {{},
               site,
               source::ProtocolCall{
                   (isDependency ? attr(op, "dependency") : callee).str(),
                   std::move(args), std::move(result)}});
      } else if (isa<MessageOp>(op)) {
        if (!common ||
            !attributes(op, {"site", "schema", "sender", "receiver"}) ||
            op->getNumOperands() != 1 || op->getNumResults() != 1 ||
            op->getOperand(0).getType() != op->getResult(0).getType()) {
          fail("interactive-message-type");
          return {};
        }
        std::string n = fresh();
        out.push_back(
            {{},
             site,
             source::Message{attr(op, "schema").str(), attr(op, "sender").str(),
                             attr(op, "receiver").str(),
                             name(op->getOperand(0), env), n}});
        env[op->getResult(0)] = n;
      } else if (isa<EmitOp, AwaitOp>(op)) {
        if (common || !attributes(op, {"site", "schema", "peer"})) {
          fail("interactive-stage");
          return {};
        }
        if (isa<EmitOp>(op))
          out.push_back(
              {{},
               site,
               source::Send{attr(op, "schema").str(), attr(op, "peer").str(),
                            name(op->getOperand(0), env)}});
        else {
          std::string n = fresh();
          env[op->getResult(0)] = n;
          out.push_back(
              {{},
               site,
               source::Receive{attr(op, "schema").str(), attr(op, "peer").str(),
                               n, type(op->getResult(0).getType())}});
        }
      } else if (auto pack = dyn_cast<VariantInjectOp>(op)) {
        if (!local || !attributes(op, {"site", "alternative"}) ||
            failed(pack.verify())) {
          fail("variant-payload");
          return {};
        }
        auto payload = names(op->getOperands(), env);
        auto outputs = results(op, env);
        out.push_back(
            {{},
             site,
             source::VariantConstruct{type(pack.getOutput().getType()),
                                      pack.getAlternative().str(),
                                      std::move(payload), outputs[0]}});
      } else if (auto match = dyn_cast<LocalMatchOp>(op)) {
        if (!local || !attributes(op, {"site", "alternatives"}) ||
            failed(match.verifyRegions())) {
          fail("local-match-shape");
          return {};
        }
        source::Match result;
        result.input = name(op->getOperand(0), env);
        result.captures = names(op->getOperands().drop_front(), env);
        for (auto [i, region] : enumerate(match.getArms())) {
          auto &inner = region.front();
          Env nested;
          source::MatchArm arm;
          arm.alternative = cast<StringAttr>(match.getAlternatives()[i]).str();
          unsigned payload = inner.getNumArguments() - result.captures.size();
          for (auto arg : inner.getArguments().take_front(payload)) {
            auto n = fresh();
            nested[arg] = n;
            arm.payload.push_back(n);
          }
          for (auto [arg, capture] :
               zip(inner.getArguments().drop_front(payload), result.captures))
            nested[arg] = capture;
          arm.body = body(inner, std::move(nested), op->getResultTypes(),
                          definition, true, true);
          result.arms.push_back(std::move(arm));
        }
        result.outputs = results(op, env);
        out.push_back({{}, site, std::move(result)});
      } else if (auto branch = dyn_cast<LocalIfOp>(op)) {
        if (!local || !attributes(op, {"site"}) ||
            failed(branch.verifyRegions())) {
          fail("local-control-shape");
          return {};
        }
        auto captures = names(op->getOperands().drop_front(), env);
        source::Body bodies[2];
        for (unsigned i = 0; i < 2; ++i) {
          auto &inner = op->getRegion(i).front();
          Env nested;
          for (auto [arg, capture] : zip(inner.getArguments(), captures))
            nested[arg] = capture;
          bodies[i] = body(inner, std::move(nested), op->getResultTypes(),
                           definition, true, true);
        }
        out.push_back(
            {{},
             site,
             source::Conditional{name(op->getOperand(0), env),
                                 std::move(captures), std::move(bodies[0]),
                                 std::move(bodies[1]), results(op, env)}});
      } else if (auto loop = dyn_cast<LocalForOp>(op)) {
        if (!local || !attributes(op, {"site"}) ||
            failed(loop.verifyRegions())) {
          fail("local-control-shape");
          return {};
        }
        auto &inner = loop.getBody().front();
        Env nested;
        std::string induction = fresh();
        nested[inner.getArgument(0)] = induction;
        source::Assignments carried;
        source::Names captures;
        for (unsigned i = 2; i < op->getNumOperands(); ++i) {
          auto input = name(op->getOperand(i), env);
          if (i - 2 < op->getNumResults()) {
            auto n = fresh();
            nested[inner.getArgument(i - 1)] = n;
            carried.emplace_back(n, input);
          } else {
            nested[inner.getArgument(i - 1)] = input;
            captures.push_back(input);
          }
        }
        auto content = body(inner, std::move(nested), op->getResultTypes(),
                            definition, true, true);
        out.push_back({{},
                       site,
                       source::For{induction, name(op->getOperand(0), env),
                                   name(op->getOperand(1), env),
                                   std::move(carried), std::move(captures),
                                   std::move(content), results(op, env)}});
      } else if (auto loop = dyn_cast<ProtocolLoopOp>(op)) {
        if (!attributes(op, {"site", "carried", "count", "parameter"}) ||
            !llvm::hasSingleElement(loop.getBody())) {
          fail("interactive-loop-body");
          return {};
        }
        auto count = loop.getCarried();
        Block &inner = loop.getBody().front();
        if (loop.getCarriedAttr().getInt() < 0 ||
            static_cast<size_t>(count) != op->getNumResults() ||
            op->getNumOperands() < static_cast<size_t>(count) ||
            inner.getArgumentTypes() != op->getOperandTypes() ||
            op->getResultTypes() !=
                op->getOperands().take_front(count).getTypes()) {
          fail("interactive-loop-type");
          return {};
        }
        Env innerEnv;
        source::Assignments initial;
        source::Names captures;
        for (size_t i = 0; i < op->getNumOperands(); ++i) {
          std::string input = name(op->getOperand(i), env);
          if (i < static_cast<size_t>(count)) {
            std::string n = fresh();
            innerEnv[inner.getArgument(i)] = n;
            initial.emplace_back(n, input);
          } else {
            innerEnv[inner.getArgument(i)] = input;
            captures.push_back(input);
          }
        }
        source::LoopCount n{loop.getParameter()
                                ? source::LoopCount::Kind::Parameter
                                : source::LoopCount::Kind::Constant,
                            loop.getCount().str()};
        auto content = body(inner, std::move(innerEnv), op->getResultTypes(),
                            definition, false);
        out.push_back(
            {{},
             site,
             source::Loop{std::move(n), std::move(initial), std::move(captures),
                          std::move(content), results(op, env)}});
      } else {
        if (!local ||
            !attributes(op, physical
                                ? ArrayRef<StringRef>{"site", "binding",
                                                      "kernel", "parameters"}
                                : ArrayRef<StringRef>{"site", "binding",
                                                      "parameters"}) ||
            failed(verifyBoundOperation(op, physical))) {
          fail("binding-operation");
          return {};
        }
        auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
        out.push_back({{},
                       site,
                       source::Operation{
                           reference.getValue().str(),
                           {},
                           strings(op->getAttrOfType<ArrayAttr>("parameters")),
                           names(op->getOperands(), env),
                           results(op, env)}});
      }
      if (!problem.empty())
        return {};
    }
    return out;
  }
  using Definition =
      std::variant<source::Function, source::Protocol, source::Participant>;
  Definition definition(Operation *op, bool local) {
    bool participant = isa<ParticipantOp>(op);
    if (!attributes(
            op,
            local ? ArrayRef<StringRef>{"sym_name", "function_type",
                                        "sym_visibility", "logical_origin",
                                        "relation", "relation_view"}
            : participant
                ? ArrayRef<StringRef>{"sym_name", "function_type", "instance",
                                      "role", "parameters", "argument_names"}
                : ArrayRef<StringRef>{"sym_name", "function_type",
                                      "input_roles", "output_roles", "roles",
                                      "parameters", "dependencies", "external",
                                      "argument_names"}))
      return {};
    FunctionType ft = signature(op);
    if (!ft || op->getNumRegions() != 1) {
      fail("interactive-definition");
      return {};
    }
    bool external =
        common &&
        (local ? op->getRegion(0).empty()
               : op->getAttrOfType<BoolAttr>("external") &&
                     op->getAttrOfType<BoolAttr>("external").getValue());
    if (local && op->hasAttr("sym_visibility") &&
        (!external || attr(op, "sym_visibility") != "private")) {
      fail("interactive-local-visibility");
      return {};
    }
    if (external ? !op->getRegion(0).empty()
                 : !llvm::hasSingleElement(op->getRegion(0))) {
      fail("interactive-definition-body");
      return {};
    }
    ArrayAttr inputRoles, outputRoles;
    if (!local && common) {
      inputRoles = op->getAttrOfType<ArrayAttr>("input_roles");
      outputRoles = op->getAttrOfType<ArrayAttr>("output_roles");
      if (!inputRoles || !outputRoles ||
          inputRoles.size() != ft.getNumInputs() ||
          outputRoles.size() != ft.getNumResults()) {
        fail("interactive-roles");
        return {};
      }
    }
    Env env;
    source::Function function;
    source::Protocol protocol;
    source::Participant projected;
    if (!external &&
        op->getRegion(0).front().getArgumentTypes() != ft.getInputs()) {
      fail("interactive-block-arguments");
      return {};
    }
    for (size_t i = 0; i < ft.getNumInputs(); ++i) {
      std::string n = fresh();
      if (!local) {
        if (auto named = op->getAttrOfType<ArrayAttr>("argument_names")) {
          if (named.size() != ft.getNumInputs() || !isa<StringAttr>(named[i]) ||
              !argumentRenamings[attr(op, "sym_name").str()]
                   .emplace(cast<StringAttr>(named[i]).str(), n)
                   .second) {
            fail("interactive-family-argument-names");
            return {};
          }
        }
      }
      if (!external)
        env[op->getRegion(0).front().getArgument(i)] = n;
      if (inputRoles) {
        if (!isa<StringAttr>(inputRoles[i])) {
          fail("interactive-role");
          return {};
        }
        protocol.arguments.push_back(
            {n, cast<StringAttr>(inputRoles[i]).getValue().str(),
             type(ft.getInput(i))});
      } else
        (local ? function.arguments : projected.arguments)
            .push_back({n, type(ft.getInput(i))});
    }
    for (size_t i = 0; i < ft.getNumResults(); ++i) {
      if (outputRoles) {
        if (!isa<StringAttr>(outputRoles[i])) {
          fail("interactive-role");
          return {};
        }
        protocol.results.push_back(
            {cast<StringAttr>(outputRoles[i]).getValue().str(),
             type(ft.getResult(i))});
      } else
        (local ? function.results : projected.results)
            .push_back(type(ft.getResult(i)));
    }
    std::optional<source::Body> content;
    if (!external)
      content = body(op->getRegion(0).front(), std::move(env), ft.getResults(),
                     op, local);
    if (local) {
      function.name = attr(op, "sym_name").str();
      function.body = std::move(content);
      {
        auto origin = op->getAttrOfType<ArrayAttr>("logical_origin");
        if (!origin || origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
            !isa<ArrayAttr>(origin[1])) {
          fail("binding-logical-origin");
          return {};
        }
        function.origin =
            source::LogicalOrigin{cast<StringAttr>(origin[0]).getValue().str(),
                                  pairs(cast<ArrayAttr>(origin[1]))};
      }
      return function;
    }
    if (participant) {
      projected.name = attr(op, "sym_name").str();
      projected.instance = attr(op, "instance").str();
      projected.role = attr(op, "role").str();
      projected.parameters =
          parameterBindings(op->getAttrOfType<ArrayAttr>("parameters"));
      projected.body = std::move(*content);
      return projected;
    }
    protocol.name = attr(op, "sym_name").str();
    protocol.roles = strings(op->getAttrOfType<ArrayAttr>("roles"));
    protocol.parameters = strings(op->getAttrOfType<ArrayAttr>("parameters"));
    protocol.dependencies =
        dependencies(op->getAttrOfType<ArrayAttr>("dependencies"));
    protocol.body = std::move(content);
    return protocol;
  }

public:
  explicit Exporter(Operation *root)
      : root(root), stage(attr(root, "stage")), common(stage == "common"),
        physical(stage == "physical") {}
  Expected<source::Content> run() {
    if (!isa<ProtocolModuleOp>(root) ||
        !attributes(root, {"stage", "relation_views"}) ||
        (!common && !physical && stage != "logical") ||
        !llvm::hasSingleElement(root->getRegion(0)))
      return error("interactive-module");
    source::Module module;
    if (auto views = root->getAttr("relation_views")) {
      auto array = dyn_cast<ArrayAttr>(views);
      if (!common || !array || array.size() > relation::DependencyLimits::count)
        return error("relation-view-attribute");
      for (auto item : array) {
        auto row = dyn_cast<ArrayAttr>(item);
        if (!row || row.size() != 5 || !isa<StringAttr>(row[0]) ||
            !isa<FlatSymbolRefAttr>(row[1]) || !isa<StringAttr>(row[2]) ||
            !isa<StringAttr>(row[3]) || !isa<IntegerAttr>(row[4]))
          return error("relation-view-attribute");
        auto height = cast<IntegerAttr>(row[4]);
        if (!height.getType().isInteger(64) || height.getValue().isNegative() ||
            height.getValue().ugt(relation::AIRLimits::height))
          return error("relation-view-height");
        source::RelationView v;
        v.name = cast<StringAttr>(row[0]).str();
        v.relation = cast<FlatSymbolRefAttr>(row[1]).getValue().str();
        v.kind = cast<StringAttr>(row[2]).str();
        v.staging = cast<StringAttr>(row[3]).str();
        v.height = height.getValue().getZExtValue();
        module.relationViews.push_back(std::move(v));
      }
    }
    std::map<std::string, std::pair<std::string, std::string>> owners;
    source::Participants participants;
    participants.stage = physical ? source::Participants::Stage::Physical
                                  : source::Participants::Stage::Logical;
    auto &bindings = common ? module.bindings : participants.bindings;
    auto &functions = common ? module.functions : participants.functions;
    for (auto &op : root->getRegion(0).front()) {
      if (isa<R1CSRelationOp, AIRRelationOp>(op)) {
        if (!common)
          return error("relation-stage");
        source::RelationDeclaration r;
        r.name = attr(&op, "sym_name").str();
        if (isa<R1CSRelationOp>(op)) {
          auto value = relation::readR1CSOperation(&op);
          if (!value)
            return value.takeError();
          r.value = std::make_shared<const relation::R1CS>(std::move(*value));
        } else {
          auto value = relation::readAIROperation(&op);
          if (!value)
            return value.takeError();
          r.value = std::make_shared<const relation::AIR>(std::move(*value));
        }
        module.relations.push_back(std::move(r));
      } else if (isa<OperationBindingOp>(op)) {
        if (!attributes(
                &op, {"sym_name", "contract", "arguments", "implementation"}))
          return error("binding-attribute");
        auto name = op.getAttrOfType<StringAttr>("sym_name");
        auto contract = op.getAttrOfType<StringAttr>("contract");
        auto implementation = op.getAttrOfType<StringAttr>("implementation");
        auto arguments = op.getAttrOfType<ArrayAttr>("arguments");
        if (!name || !contract || !implementation || !arguments)
          return error("binding-declaration");
        source::OperationBinding declaration;
        declaration.name = name.getValue().str();
        declaration.application.contract = contract.getValue().str();
        declaration.application.arguments =
            strings(arguments, "binding-static-identity");
        declaration.application.implementation =
            implementation.getValue().str();
        bindings.push_back(std::move(declaration));
      } else if (isa<func::FuncOp>(op)) {
        if (op.hasAttr("relation") || op.hasAttr("relation_view")) {
          auto relation = op.getAttrOfType<FlatSymbolRefAttr>("relation");
          auto view = op.getAttrOfType<StringAttr>("relation_view");
          if (!common || !relation || !view ||
              !owners
                   .emplace(
                       attr(&op, "sym_name").str(),
                       std::make_pair(relation.getValue().str(), view.str()))
                   .second)
            return error("relation-function-association");
        }
        auto value = definition(&op, true);
        if (!problem.empty())
          return error(problem);
        functions.push_back(std::get<source::Function>(std::move(value)));
      } else if ((common && isa<ProtocolOp>(op)) ||
                 (!common && isa<ParticipantOp>(op))) {
        auto value = definition(&op, false);
        if (!problem.empty())
          return error(problem);
        if (common)
          module.protocols.push_back(
              std::get<source::Protocol>(std::move(value)));
        else
          participants.participants.push_back(
              std::get<source::Participant>(std::move(value)));
      } else if (auto instance = dyn_cast<InstanceOp>(op)) {
        if (!common || !attributes(&op, {"sym_name", "protocol", "parameters",
                                         "dependencies", "roles"}))
          return error("interactive-instance-stage");
        source::Instance value;
        value.name = instance.getSymName().str();
        value.protocol = instance.getProtocol().str();
        value.parameters = parameterBindings(instance.getParameters());
        value.dependencies = pairs(instance.getDependencies(), true);
        value.roles = pairs(instance.getRoles());
        module.instances.push_back(std::move(value));
      } else if (auto entry = dyn_cast<ProtocolEntryOp>(op)) {
        if (!attributes(&op, {"sym_name", "targets"}))
          return error("interactive-entry-attribute");
        if (common) {
          auto targets = entry.getTargets();
          if (targets.size() != 1 || !isa<FlatSymbolRefAttr>(targets[0]))
            return error("interactive-entry-target");
          source::Entry value;
          value.name = entry.getSymName().str();
          value.instance = cast<FlatSymbolRefAttr>(targets[0]).getValue().str();
          module.entries.push_back(std::move(value));
        } else {
          source::ParticipantEntry value;
          value.name = entry.getSymName().str();
          value.participants = pairs(entry.getTargets(), true);
          participants.entries.push_back(std::move(value));
        }
      } else
        return error("interactive-top-operation");
    }
    if (!problem.empty())
      return error(problem);
    if (common) {
      auto expected = relation::associations(module);
      if (!expected)
        return expected.takeError();
      if (*expected != owners)
        return error("relation-function-association");
    }
    auto renameSelectors =
        [&](source::ParameterBindings &parameters,
            const std::map<std::string, std::string> &owners) {
          for (auto &[name, binding] : parameters)
            if (auto *family = std::get_if<source::FamilyIngress>(&binding))
              for (auto &selector : family->selectors) {
                auto owner = owners.find(selector.role);
                if (owner == owners.end()) {
                  fail("interactive-family-roles");
                  return;
                }
                const auto &mapping = argumentRenamings[owner->second];
                for (auto &arg : selector.arguments) {
                  auto found = mapping.find(arg);
                  if (found == mapping.end()) {
                    fail("interactive-family-argument");
                    return;
                  }
                  arg = found->second;
                }
              }
        };
    if (common) {
      for (auto &instance : module.instances) {
        std::map<std::string, std::string> owners;
        for (const auto &[formal, actual] : instance.roles)
          owners.emplace(actual, instance.protocol);
        renameSelectors(instance.parameters, owners);
      }
    } else {
      for (auto &p : participants.participants) {
        std::map<std::string, std::string> owners;
        for (const auto &q : participants.participants)
          if (p.instance == q.instance)
            owners.emplace(q.role, q.name);
        renameSelectors(p.parameters, owners);
      }
    }
    if (!problem.empty())
      return error(problem);
    source::Content value = common ? source::Content(std::move(module))
                                   : source::Content(std::move(participants));
    if (auto e = admit(value, false))
      return e;
    return value;
  }
};
} // namespace
Expected<source::Content> exportSource(Operation *root) {
  // Check each operation's local invariants before accessing typed operands,
  // results, regions or properties. Full recursive verification would call this
  // exporter again through ProtocolModuleOp::verifyRegions.
  if (!root || root->walk<WalkOrder::PreOrder>([](Operation *op) {
                     return failed(op->getName().verifyInvariants(op))
                                ? WalkResult::interrupt()
                                : WalkResult::advance();
                   })
                   .wasInterrupted())
    return error("interactive-malformed-ir");
  if (auto module = dyn_cast<ModuleOp>(root)) {
    if (!llvm::hasSingleElement(*module.getBody()))
      return error("interactive-module-count");
    root = &module.getBody()->front();
  }
  return Exporter(root).run();
}
Expected<json::Value> exportModule(Operation *root) {
  auto value = exportSource(root);
  if (!value)
    return value.takeError();
  return source::encode(*value);
}
LogicalResult verifyModule(Operation *root) {
  auto v = exportSource(root);
  if (!v)
    return diagnostics::emit(root->emitOpError(), v.takeError());
  return success();
}
} // namespace zkc::protocol
