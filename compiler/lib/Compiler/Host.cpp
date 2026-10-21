#include "zkc/Compiler/Host.h"
#include "LanguageInterface.h"
#include "LanguagePackageReader.h"
#include "NativeDeployment.h"
#include "Run.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Kernel.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Entry.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
Expected<std::string> numerical(mlir::ModuleOp original, StringRef root,
                                const EntryOptions &options) {
  auto prepared = mathematical::prepareProtocol(original, options.simplify,
                                                options.mathematicalSelection);
  if (!prepared)
    return error("entry.numeric", "numerical helper preparation failed");
  auto owner = *prepared->getOps<protocol_ir::ProtocolModuleOp>().begin();
  auto source = mlir::OwningOpRef<mlir::ModuleOp>(
      mlir::cast<mlir::ModuleOp>(prepared->getOperation()->clone()));
  auto sourceOwner = *source->getOps<protocol_ir::ProtocolModuleOp>().begin();
  SmallVector<local::FuncOp> calculations;
  for (auto f : owner.getBody().front().getOps<local::FuncOp>()) {
    bool total = true, hasMath = false;
    for (auto &op : f.getBody().front().without_terminator()) {
      bool math =
          mathematical::isTotal(&op) || mlir::isa<mlir::func::CallOp>(op);
      hasMath |= math;
      total &= math || mlir::isa<local::GuardOp>(op);
    }
    if (total && hasMath)
      calculations.push_back(f);
  }
  for (auto f : calculations)
    if (mlir::failed(kernel::formCalculation(f, sourceOwner,
                                             options.mathematicalSelection)))
      return error("entry.numeric", "numerical Kernel formation failed");
  llvm::DenseSet<mlir::Operation *> mapHelpers;
  if (mlir::failed(algebra::collectMapHelpers(owner, mapHelpers)))
    return error("entry.numeric", "map closure failed");
  for (auto &op : make_early_inc_range(owner.getBody().front()))
    if (mlir::isa<mlir::func::FuncOp, data::DomainOp>(op) &&
        !mapHelpers.contains(&op))
      op.erase();
  owner.setProfile(protocol_ir::Profile::Exec);
  if (mlir::failed(
          kernel::lowerKernels(*prepared, options.mathematicalSelection)) ||
      mlir::failed(protocol::lowerPhysical(*prepared, {}, false, nullptr,
                                           options.releaseStorage)))
    return error("entry.numeric", "numerical physical lowering failed");
  auto result = protocol::exportModule(*prepared);
  if (!result)
    return result.takeError();
  auto bytes = printJson(*result);
  auto checked = protocol::verifyProgramArtifact(*prepared, bytes);
  if (!checked)
    return checked.takeError();
  if (!checked->participants.empty() || !checked->entries.empty() ||
      none_of(checked->functions,
              [&](const auto &f) { return f.name == root; }))
    return error("entry.numeric", "numerical Program root differs");
  return bytes;
}
json::Array schemas(ArrayRef<Port> ports, Layouts &layouts, Error &failure) {
  json::Array out;
  for (const auto &p : ports) {
    auto layout = layouts.get(p.type);
    if (!layout) {
      failure = layout.takeError();
      return {};
    }
    out.push_back(encodeEntrySchema(**layout));
  }
  return out;
}
Error references(
    const json::Value &block,
    std::map<std::string, std::pair<json::Array, json::Array>> &deployments,
    StringRef kind = "invoke") {
  auto &b = *block.getAsObject();
  std::map<int64_t, json::Value> values;
  for (const auto &v : *b.getArray("arguments"))
    values.emplace(*v.getAsObject()->getInteger("id"),
                   *v.getAsObject()->get("schema"));
  for (const auto &v : *b.getArray("operations")) {
    auto &op = *v.getAsObject();
    if (op.getString("op") == kind) {
      json::Array inputs, outputs;
      auto target =
          op.getString(kind == "numeric" ? "calculation" : "deployment");
      if (!target)
        return error("entry.reference", "static boundary target is absent");
      for (const auto &id : *op.getArray("operands")) {
        auto found = values.find(*id.getAsInteger());
        if (found == values.end())
          return error("entry.scope",
                       "static boundary operand is out of scope");
        inputs.push_back(found->second);
      }
      for (const auto &r : *op.getArray("results"))
        outputs.push_back(*r.getAsObject()->get("schema"));
      deployments.emplace(
          target->str(), std::make_pair(std::move(inputs), std::move(outputs)));
    }
    // SSAReader has checked regions only for structured control. Metadata on
    // other operations is rejected by body admission, never traversed here.
    if (op.getString("op") == "if" || op.getString("op") == "for" ||
        op.getString("op") == "match")
      for (const auto &region : *op.getArray("regions"))
        if (auto e = references(region, deployments, kind))
          return e;
    for (const auto &r : *op.getArray("results"))
      values.emplace(*r.getAsObject()->getInteger("id"),
                     *r.getAsObject()->get("schema"));
  }
  return Error::success();
}
} // namespace
Expected<CompiledHost> compileHost(const CheckedOriginal &original,
                                   const EntryOptions &options) {
  const auto &entry = original.entry();
  const auto &limits = original.admissionLimits();
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry, mlir::MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
  if (!module)
    return error("entry.original", "admitted Host original no longer parses");
  auto analysis = analyzeHostOriginal(entry, *module, limits);
  if (!analysis)
    return analysis.takeError();
  json::Array calculations, deployments;
  Layouts layouts(entry, limits);
  Error failure = Error::success();
  for (const auto &fragment : analysis->calculations) {
    mlir::ModuleOp nested;
    for (auto child : module->getOps<mlir::ModuleOp>())
      if (child->getAttrOfType<mlir::StringAttr>("entry.calculation")
              .getValue() == fragment.id)
        nested = child;
    if (!nested)
      return error("entry.closure", "missing numerical original");
    auto copy = mlir::OwningOpRef<mlir::ModuleOp>(
        mlir::cast<mlir::ModuleOp>(nested->clone()));
    copy->getOperation()->removeAttr("entry.calculation");
    auto program = numerical(*copy, fragment.id, options);
    if (!program)
      return program.takeError();
    auto inputs = schemas(fragment.definition.inputs, layouts, failure);
    if (failure)
      return std::move(failure);
    auto outputs = schemas(fragment.definition.outputs, layouts, failure);
    if (failure)
      return std::move(failure);
    calculations.push_back(json::Object{{"id", fragment.id},
                                        {"parameters", std::move(inputs)},
                                        {"results", std::move(outputs)},
                                        {"function", fragment.id},
                                        {"program", std::move(*program)}});
  }
  std::map<std::string, std::pair<json::Array, json::Array>> required;
  for (const auto &f : analysis->functions)
    if (auto e = references(*f.getAsObject()->get("body"), required))
      return e;
  for (const auto &invocation : entry.invocations()) {
    auto operation = invocation.kind == HostInvocation::Kind::Run ? "run"
                     : invocation.kind == HostInvocation::Kind::Prove
                         ? "prove"
                         : "verify";
    const auto &target =
        entry.project().declarations()[invocation.target.index];
    auto id =
        entryDeploymentId(invocation.kind, target.symbol, invocation.arguments);
    auto signature = required.find(id);
    if (signature == required.end() || !invocation.deployment)
      return error("entry.closure", "child deployment reference differs");
    auto source = prepareOriginal(*invocation.deployment, limits);
    if (!source)
      return source.takeError();
    auto compiled = compileEntry(*source, options);
    if (!compiled)
      return compiled.takeError();
    auto package = packageEntry(*compiled);
    if (!package)
      return package.takeError();
    deployments.push_back(
        json::Object{{"id", id},
                     {"operation", operation},
                     {"parameters", std::move(signature->second.first)},
                     {"results", std::move(signature->second.second)},
                     {"package", package->bytes().str()}});
    required.erase(signature);
  }
  if (!required.empty())
    return error("entry.closure", "missing child deployment");
  auto artifact =
      printJson(json::Object{{"format", "zkc.host/0"},
                             {"original", original.identity().str()},
                             {"entry", entry.root().symbol},
                             {"functions", std::move(analysis->functions)},
                             {"calculations", std::move(calculations)},
                             {"deployments", std::move(deployments)}});
  if (auto e = checkHostArtifact(artifact, original.interface(), limits))
    return std::move(e);
  return CompiledHost{std::move(artifact)};
}
namespace {
class Admission {
  const LanguageInterface &interface;
  const Limits &limits;
  std::map<std::string, const json::Object *> functions, calculations,
      deployments;
  std::map<std::string, std::set<std::string>> calls;
  std::set<std::string> usedCalculations, usedDeployments;
  std::map<std::string, json::Value> schemas;
  std::map<std::string, std::string> families;
  Error failure = Error::success();
  uint64_t operations = 0;
  using Types = std::vector<const json::Value *>;
  using Scope = std::map<int64_t, const json::Value *>;
  bool fail(StringRef code, StringRef message) {
    if (!failure)
      failure = error(code, message);
    return false;
  }
  bool fields(const json::Object &o, ArrayRef<StringRef> extra) {
    if (o.size() != extra.size() + 3 || !o.getString("op") ||
        !o.getArray("operands") || !o.getArray("results"))
      return fail("entry.operation", "invalid operation fields");
    for (auto name : extra)
      if (!o.get(name))
        return fail("entry.operation", "missing operation field");
    return true;
  }
  bool schema(const json::Value &value, unsigned depth = 0) {
    if (depth > limits.typeDepth)
      return fail("source.limit", "Host schema depth limit");
    auto *s = value.getAsObject();
    if (!s || s->size() != 9 || !s->getString("kind") ||
        !s->getString("identity") || !s->getString("type") ||
        !s->getBoolean("custody") || !s->getBoolean("constructible") ||
        !s->getArray("permissions") || !s->getArray("fields") ||
        !s->getArray("alternatives") || !s->getArray("leaves"))
      return fail("entry.schema", "invalid logical schema");
    auto id = s->getString("identity")->str();
    if (id.size() != 64 ||
        !all_of(id,
                [](char c) { return isDigit(c) || (c >= 'a' && c <= 'f'); }) ||
        *s->getBoolean("custody") ||
        s->getArray("leaves")->size() > limits.aggregateLeaves ||
        !is_contained(*s->getArray("permissions"), json::Value("Copy")))
      return fail("entry.schema", "Host schema is not ordinary copyable data");
    auto found = schemas.find(id);
    if (found != schemas.end())
      return found->second == value ||
             fail("entry.schema",
                  "nominal schema identity has conflicting definitions");
    // Use the same decoder as the interface, including native permissions,
    // variant identities, product offsets and exact constructor policy.
    auto admitted = detail::decodeHostSchema(value, limits);
    if (!admitted) {
      consumeError(admitted.takeError());
      return fail("entry.schema",
                  "logical schema failed independent admission");
    }
    auto children = [&](const json::Array &fs) {
      for (const auto &f : fs) {
        auto *o = f.getAsObject();
        if (!o || o->size() != 3 || !o->getString("name") ||
            !o->getInteger("offset") || !o->get("schema") ||
            !schema(*o->get("schema"), depth + 1))
          return false;
      }
      return true;
    };
    if (!children(*s->getArray("fields")))
      return fail("entry.schema", "invalid product fields");
    for (const auto &a : *s->getArray("alternatives")) {
      auto *o = a.getAsObject();
      if (!o || o->size() != 2 || !o->getString("name") ||
          !o->getArray("fields") || !children(*o->getArray("fields")))
        return fail("entry.schema", "invalid variant alternatives");
    }
    schemas.emplace(std::move(id), value);
    return true;
  }
  bool bind(const json::Array &definitions, Scope &scope,
            std::set<int64_t> &ids, Types &types) {
    for (const auto &d : definitions) {
      auto *o = d.getAsObject();
      auto id = o ? o->getInteger("id") : std::nullopt;
      if (!o || o->size() != 2 || !id || *id < 0 || !ids.insert(*id).second ||
          !o->get("schema") || !schema(*o->get("schema")))
        return fail("entry.scope", "invalid or duplicate SSA definition");
      scope.emplace(*id, o->get("schema"));
      types.push_back(o->get("schema"));
    }
    return true;
  }
  bool same(const Types &a, const Types &b) {
    return a.size() == b.size() &&
           llvm::equal(a, b, [](auto *x, auto *y) { return *x == *y; });
  }
  Types parameterTypes(const json::Object &f, bool signature) {
    Types out;
    for (const auto &v : *f.getArray("parameters"))
      out.push_back(signature ? v.getAsObject()->get("schema") : &v);
    return out;
  }
  Types resultTypes(const json::Object &f, bool signature) {
    if (signature)
      return {f.get("result")};
    Types out;
    for (const auto &v : *f.getArray("results"))
      out.push_back(&v);
    return out;
  }
  bool deploymentContract(const json::Object &deployment,
                          const LanguageInterface &child) {
    auto parameters = parameterTypes(deployment, false),
         results = resultTypes(deployment, false);
    auto operation = *deployment.getString("operation");
    auto family = StringRef(child.entry);
    std::string arguments;
    if (operation == "run") {
      auto split = family.rsplit("::");
      family = split.first;
      auto resultType = results.size() == 1
                            ? results[0]->getAsObject()->getString("type")
                            : std::nullopt;
      if (!resultType ||
          !resultType->consume_front(family.str() + "::RunResult"))
        return fail("entry.signature", "joint child family differs");
      arguments = resultType->str();
      auto expected = family.str() + "::run";
      if (!arguments.empty())
        expected +=
            "_" +
            toHex(SHA256::hash(arrayRefFromStringRef(family.str() + arguments)),
                  true);
      if (child.entry != expected)
        return fail("entry.signature", "joint child specialization differs");
    }
    auto nominal = [&](const json::Value &value, StringRef member,
                       bool constructible) {
      const auto &s = *value.getAsObject();
      auto expected = family.str() + "::" + member.str();
      auto actual = *s.getString("type");
      if (!actual.consume_front(expected) ||
          (!actual.empty() && !actual.starts_with("<")) ||
          *s.getBoolean("constructible") != constructible)
        return fail("entry.deployment",
                    "generated nominal schema differs from child family");
      if (arguments != actual)
        return fail("entry.deployment", "generated static arguments differ");
      return true;
    };
    for (auto *s : concat<const json::Value *>(parameters, results)) {
      auto pin = child.original + ":" + family.str();
      auto [old, inserted] =
          families.emplace(s->getAsObject()->getString("identity")->str(), pin);
      if (!inserted && old->second != pin)
        return fail("entry.deployment",
                    "one generated family was rebound to a different child");
    }
    const auto &protocol = child.selectedProtocol();
    auto ordinary = [&](unsigned index) {
      const auto &port = protocol.inputs[index];
      for (const auto &setup : child.setups)
        for (const auto &input : setup.inputs)
          if (input.port == index)
            return false;
      for (const auto &leaf : port.schema->leaves) {
        auto type = protocol::parseBoundType(leaf, false);
        if (!type) {
          consumeError(type.takeError());
          return false;
        }
        if (type->kind == "prover_key" || type->kind == "verifier_key")
          return false;
      }
      return true;
    };
    auto record = [&](const json::Value &value,
                      ArrayRef<const InterfacePort *> ports) {
      const auto &s = *value.getAsObject();
      const auto &fields = *s.getArray("fields");
      if (s.getString("kind") != "record" || fields.size() != ports.size())
        return fail("entry.signature",
                    "generated record fields differ from child ports");
      for (auto [i, p] : enumerate(ports)) {
        const auto &f = *fields[i].getAsObject();
        if (f.getString("name") != p->name ||
            *f.get("schema") != detail::encodeInterfaceSchema(*p->schema))
          return fail("entry.signature", "generated child port schema differs");
      }
      return true;
    };
    auto inputs = [&](std::optional<unsigned> role, bool publicOnly,
                      bool privateOnly) {
      SmallVector<const InterfacePort *> ports;
      for (auto [i, p] : enumerate(protocol.inputs)) {
        bool isPublic =
            child.proof && is_contained(child.proof->publicInputs, i);
        if (ordinary(i) && (!role || is_contained(p.roles, *role)) &&
            (!publicOnly || isPublic) && (!privateOnly || !isPublic))
          ports.push_back(&p);
      }
      return ports;
    };
    auto outputs = [&](unsigned role) {
      SmallVector<const InterfacePort *> ports;
      for (const auto &p : protocol.outputs)
        if (is_contained(p.roles, role))
          ports.push_back(&p);
      return ports;
    };
    auto candidate = [&](const json::Value &s) {
      const auto &o = *s.getAsObject();
      const auto &f = *o.getArray("fields");
      return nominal(s, "Proof", true) && o.getString("kind") == "record" &&
             f.size() == 1 &&
             f[0].getAsObject()->getString("name") == "bytes" &&
             f[0].getAsObject()->getObject("schema")->getString("kind") ==
                 "builtin" &&
             *f[0].getAsObject()->getObject("schema")->getArray("leaves") ==
                 json::Array{"bytes"};
    };
    if (results.size() != 1)
      return fail("entry.signature",
                  "generated operation result arity differs");
    const auto &r = *results.front();
    if (operation == "run") {
      if (parameters.size() != 1 || !nominal(*parameters[0], "Inputs", true) ||
          !nominal(r, "RunResult", false))
        return fail("entry.signature", "joint child signature differs");
      const auto &in = *parameters[0]->getAsObject()->getArray("fields"),
                 &out = *r.getAsObject()->getArray("fields");
      if (in.size() != protocol.roles.size() ||
          out.size() != protocol.roles.size())
        return fail("entry.signature", "joint generated role roster differs");
      for (auto [i, role] : enumerate(protocol.roles)) {
        const auto &a = *in[i].getAsObject(), &b = *out[i].getAsObject();
        if (a.getString("name") != role || b.getString("name") != role ||
            !nominal(*a.get("schema"), "Inputs::" + role, true) ||
            !nominal(*b.get("schema"), "RunResult::" + role, false) ||
            !record(*a.get("schema"), inputs(i, false, false)) ||
            !record(*b.get("schema"), outputs(i)))
          return fail("entry.signature", "joint role contract differs");
      }
    } else {
      if (!child.proof || parameters.size() != 2 ||
          !nominal(*parameters[0], "Public", true) ||
          !record(*parameters[0], inputs({}, true, false)))
        return fail("entry.signature", "proof public contract differs");
      if (operation == "prove") {
        const auto &fs = *r.getAsObject()->getArray("fields");
        if (!nominal(*parameters[1], "Witness", true) ||
            !record(*parameters[1], inputs(child.proof->prover, false, true)) ||
            !nominal(r, "ProveResult", false) || fs.size() != 2 ||
            fs[0].getAsObject()->getString("name") != "proof" ||
            fs[1].getAsObject()->getString("name") != "outputs" ||
            !candidate(*fs[0].getAsObject()->get("schema")) ||
            !nominal(*fs[1].getAsObject()->get("schema"), "ProverOutputs",
                     false) ||
            !record(*fs[1].getAsObject()->get("schema"),
                    outputs(child.proof->prover)))
          return fail("entry.signature", "proof producer contract differs");
      } else {
        const auto &arms = *r.getAsObject()->getArray("alternatives");
        if (!candidate(*parameters[1]) || !nominal(r, "VerifyResult", false) ||
            r.getAsObject()->getString("kind") != "variant" || arms.size() != 2)
          return fail("entry.signature", "proof verifier contract differs");
        const auto &accepted = *arms[0].getAsObject(),
                   &rejected = *arms[1].getAsObject();
        const auto &fs = *accepted.getArray("fields");
        if (accepted.getString("name") != "Accepted" ||
            rejected.getString("name") != "Rejected" ||
            !rejected.getArray("fields")->empty() || fs.size() != 1 ||
            fs[0].getAsObject()->getString("name") != "outputs" ||
            !nominal(*fs[0].getAsObject()->get("schema"), "VerifierOutputs",
                     false) ||
            !record(*fs[0].getAsObject()->get("schema"),
                    outputs(child.proof->verifier)))
          return fail("entry.signature",
                      "verification acceptance/rejection contract differs");
      }
    }
    return true;
  }
  bool nativeSignature(const json::Object &c) {
    auto program = program::parse(*c.getString("program"));
    if (!program) {
      consumeError(program.takeError());
      return fail("entry.numeric", "invalid numerical Program");
    }
    if (auto e = protocol::admit(*program)) {
      consumeError(std::move(e));
      return fail("entry.numeric", "numerical Program failed native admission");
    }
    if (!program->participants.empty() || !program->entries.empty())
      return fail("entry.numeric",
                  "numerical Program has participant authority");
    auto root = find_if(program->functions, [&](const auto &f) {
      return f.name == c.getString("function");
    });
    if (root == program->functions.end())
      return fail("entry.reference", "numerical root is absent");
    std::vector<std::string> inputs, outputs;
    for (const auto &arg : root->arguments)
      inputs.push_back(arg.type);
    outputs = root->results;
    for (bool in : {true, false}) {
      const auto &native = in ? inputs : outputs;
      unsigned at = 0;
      for (auto *s : in ? parameterTypes(c, false) : resultTypes(c, false))
        for (const auto &leaf : *s->getAsObject()->getArray("leaves")) {
          if (at == native.size())
            return fail("entry.signature",
                        "numerical native signature is too short");
          auto type = protocol::parseBoundType(native[at++], true);
          if (!type) {
            consumeError(type.takeError());
            return fail("entry.signature", "invalid numerical physical type");
          }
          type->representation.clear();
          if (type->spelling() != leaf.getAsString())
            return fail("entry.signature",
                        "numerical native signature differs");
        }
      if (at != native.size())
        return fail("entry.signature",
                    "numerical native signature is too long");
    }
    return true;
  }
  bool block(const json::Value &value, const Types &arguments,
             const Types &returns, const std::string &function,
             std::set<int64_t> &ids, unsigned depth = 0) {
    auto *b = value.getAsObject();
    if (depth > limits.callDepth || !b || b->size() != 3 ||
        !b->getArray("arguments") || !b->getArray("operations") ||
        !b->getArray("returns"))
      return fail("entry.scope", "invalid Host block");
    Scope scope;
    Types actualArguments;
    if (!bind(*b->getArray("arguments"), scope, ids, actualArguments) ||
        !same(arguments, actualArguments))
      return fail("entry.signature", "Host block arguments differ");
    bool stopped = false;
    for (const auto &v : *b->getArray("operations")) {
      if (stopped || ++operations > limits.operations)
        return fail("entry.operation",
                    "operation after stop or operation limit");
      auto *o = v.getAsObject();
      if (!o || !o->getString("op") || !o->getArray("operands") ||
          !o->getArray("results"))
        return fail("entry.operation", "invalid Host operation");
      Types in, out;
      for (const auto &operand : *o->getArray("operands")) {
        auto id = operand.getAsInteger();
        if (!id || !scope.count(*id))
          return fail("entry.scope",
                      "operand is undefined or outside its scope");
        in.push_back(scope.at(*id));
      }
      // Results enter scope only after all regions have been checked.
      Scope produced;
      if (!bind(*o->getArray("results"), produced, ids, out))
        return false;
      auto op = *o->getString("op");
      if (op == "call" || op == "numeric" || op == "invoke") {
        auto key = op == "call"      ? "callee"
                   : op == "numeric" ? "calculation"
                                     : "deployment";
        if (!fields(*o, {key}) || !o->getString(key))
          return fail("entry.reference", "invalid static reference");
        auto &inventory = op == "call"      ? functions
                          : op == "numeric" ? calculations
                                            : deployments;
        auto name = o->getString(key)->str();
        auto target = inventory.find(name);
        if (target == inventory.end())
          return fail("entry.reference", "static target is absent");
        auto &contract = op == "call" ? *target->second->getObject("signature")
                                      : *target->second;
        if (!same(in, parameterTypes(contract, op == "call")) ||
            !same(out, resultTypes(contract, op == "call")))
          return fail("entry.signature", "static call signature differs");
        if (op == "call")
          calls[function].insert(name);
        else if (op == "numeric")
          usedCalculations.insert(name);
        else
          usedDeployments.insert(name);
      } else if (op == "construct" || op == "unpack") {
        if (!fields(*o, op == "construct" ? ArrayRef<StringRef>{"alternative"}
                                          : ArrayRef<StringRef>{}) ||
            (op == "construct" &&
             (out.size() != 1 || !o->getString("alternative"))) ||
            (op == "unpack" && in.size() != 1))
          return fail("entry.construct", "invalid construction");
        auto *s = (op == "construct" ? out[0] : in[0])->getAsObject();
        auto *fs = s->getArray("fields");
        auto kind = s->getString("kind");
        if (kind != "record" && kind != "tuple" && kind != "array" &&
            kind != "unit" && !(op == "construct" && kind == "variant"))
          return fail("entry.construct",
                      "operation requires an explicit product or variant");
        if (op == "construct") {
          if (!*s->getBoolean("constructible"))
            return fail("entry.construct",
                        "native result constructor is forbidden");
          auto alternative = *o->getString("alternative");
          if (!alternative.empty()) {
            fs = nullptr;
            for (const auto &a : *s->getArray("alternatives"))
              if (a.getAsObject()->getString("name") == alternative)
                fs = a.getAsObject()->getArray("fields");
          } else if (!s->getArray("alternatives")->empty())
            fs = nullptr;
        }
        if (!fs)
          return fail("entry.construct", "constructor alternative is absent");
        Types fields;
        for (const auto &f : *fs)
          fields.push_back(f.getAsObject()->get("schema"));
        if (!same(fields, op == "construct" ? in : out))
          return fail("entry.signature", "constructor fields differ");
      } else if (op == "project") {
        if (!fields(*o, {"path"}) || in.size() != 1 || out.size() != 1 ||
            !o->getArray("path") ||
            o->getArray("path")->size() > limits.typeDepth)
          return fail("entry.project", "invalid projection");
        auto *selected = in[0];
        for (const auto &v : *o->getArray("path")) {
          auto index = v.getAsInteger();
          auto *fs = selected->getAsObject()->getArray("fields");
          if (!index || *index < 0 || uint64_t(*index) >= fs->size())
            return fail("entry.project", "projection path is absent");
          selected = (*fs)[*index].getAsObject()->get("schema");
        }
        if (*selected != *out[0])
          return fail("entry.signature", "projection result differs");
      } else if (op == "if" || op == "for" || op == "match") {
        if (!fields(*o, op == "if" ? ArrayRef<StringRef>{"regions"}
                        : op == "for"
                            ? ArrayRef<StringRef>{"regions", "carried"}
                            : ArrayRef<StringRef>{"regions", "alternatives"}) ||
            in.empty() || !o->getArray("regions"))
          return fail("entry.control", "invalid structured control");
        const auto &regions = *o->getArray("regions");
        if ((op == "if" &&
             (regions.size() != 2 ||
              in[0]->getAsObject()->getString("kind") != "boolean")) ||
            (op == "for" &&
             (regions.size() != 1 || in.size() < 2 ||
              !o->getInteger("carried") ||
              *o->getInteger("carried") != int64_t(out.size()) ||
              in.size() < 2 + out.size() ||
              in[0]->getAsObject()->getString("kind") != "index" ||
              *in[0] != *in[1])))
          return fail("entry.control", "control signature differs");
        if (op == "match" &&
            (!o->getArray("alternatives") ||
             o->getArray("alternatives")->size() != regions.size() ||
             in[0]->getAsObject()->getArray("alternatives")->size() !=
                 regions.size()))
          return fail("entry.control", "match coverage differs");
        std::set<std::string> alternatives;
        for (auto [i, r] : enumerate(regions)) {
          Types params;
          if (op == "if")
            append_range(params, ArrayRef(in).drop_front());
          else if (op == "for") {
            params.push_back(in[0]);
            append_range(params, ArrayRef(in).drop_front(2));
            Types initial(ArrayRef(in).slice(2, out.size()).begin(),
                          ArrayRef(in).slice(2, out.size()).end());
            if (!same(initial, out))
              return fail("entry.signature", "loop initial values differ");
          } else {
            auto name = (*o->getArray("alternatives"))[i].getAsString();
            if (!name || !alternatives.insert(name->str()).second)
              return fail("entry.control", "duplicate match alternative");
            const json::Array *payload = nullptr;
            for (const auto &a :
                 *in[0]->getAsObject()->getArray("alternatives"))
              if (a.getAsObject()->getString("name") == name)
                payload = a.getAsObject()->getArray("fields");
            if (!payload)
              return fail("entry.control", "unknown match alternative");
            for (const auto &f : *payload)
              params.push_back(f.getAsObject()->get("schema"));
            append_range(params, ArrayRef(in).drop_front());
          }
          if (!block(r, params, out, function, ids, depth + 1))
            return false;
        }
      } else if (op == "require" || op == "drop") {
        if (!fields(*o, {}) || in.size() != 1 || !out.empty() ||
            (op == "require" &&
             in[0]->getAsObject()->getString("kind") != "boolean") ||
            (op == "drop" &&
             !is_contained(*in[0]->getAsObject()->getArray("permissions"),
                           json::Value("Drop"))))
          return fail("entry.operation", "invalid require/drop");
      } else if (op == "stop") {
        if (!fields(*o, {"reason"}) || !o->getString("reason") || !in.empty() ||
            !out.empty())
          return fail("entry.operation", "invalid stop");
        stopped = true;
      } else
        return fail("entry.operation", "unknown Host operation");
      if (op == "drop")
        scope.erase(*o->getArray("operands")->front().getAsInteger());
      scope.insert(produced.begin(), produced.end());
    }
    Types result;
    for (const auto &v : *b->getArray("returns")) {
      auto id = v.getAsInteger();
      if (!id || !scope.count(*id))
        return fail("entry.scope", "return is undefined");
      result.push_back(scope.at(*id));
    }
    return (stopped ? result.empty() : same(result, returns)) ||
           fail("entry.signature", "Host return signature differs");
  }
  bool visit(const std::string &f, std::set<std::string> &active,
             std::map<std::string, unsigned> &heights, unsigned depth = 0) {
    if (depth > limits.callDepth || active.count(f))
      return fail("entry.cycle",
                  "recursive or excessively deep Entry call graph");
    // A shared callee may first be reached along a shorter path. Retain its
    // longest suffix so later callers still satisfy the full depth bound.
    if (auto found = heights.find(f); found != heights.end())
      return uint64_t(depth) + found->second <= limits.callDepth ||
             fail("entry.cycle", "excessively deep Entry call graph");
    active.insert(f);
    unsigned height = 0;
    for (const auto &child : calls[f]) {
      if (!visit(child, active, heights, depth + 1))
        return false;
      height = std::max(height, heights.at(child) + 1);
    }
    active.erase(f);
    heights.emplace(f, height);
    return true;
  }

  Error signatures(const json::Array &definitions) {
    for (const auto &v : definitions) {
      auto *f = v.getAsObject();
      auto *s = f ? f->getObject("signature") : nullptr;
      if (!f || f->size() != 2 || !f->get("body") || !s || s->size() != 3 ||
          !s->getString("symbol") || !s->getArray("parameters") ||
          !s->get("result") ||
          !functions.emplace(s->getString("symbol")->str(), f).second)
        return error("entry.closure", "invalid or duplicate Host function");
      if (!schema(*s->get("result")))
        return std::move(failure);
      std::set<std::string> names;
      for (const auto &p : *s->getArray("parameters")) {
        auto *o = p.getAsObject();
        if (!o || o->size() != 2 || !o->getString("name") ||
            !names.insert(o->getString("name")->str()).second ||
            !o->get("schema") || !schema(*o->get("schema")))
          return failure ? std::move(failure)
                         : error("entry.signature", "invalid Host parameter");
      }
    }
    if (functions.size() != interface.host->functions.size() ||
        functions.size() > limits.instances)
      return error("entry.closure",
                   "Host interface function inventory differs");
    for (const auto &f : interface.host->functions) {
      auto found = functions.find(f.symbol);
      if (found == functions.end())
        return error("entry.closure", "interface function absent");
      auto &s = *found->second->getObject("signature");
      auto ps = parameterTypes(s, true);
      if (ps.size() != f.parameters.size() ||
          *s.get("result") != detail::encodeInterfaceSchema(*f.result))
        return error("entry.signature", "Host interface result differs");
      for (auto [i, p] : enumerate(f.parameters))
        if (*ps[i] != detail::encodeInterfaceSchema(*p.schema) ||
            (*s.getArray("parameters"))[i].getAsObject()->getString("name") !=
                p.name)
          return error("entry.signature", "Host interface parameter differs");
    }
    return Error::success();
  }
  Error bodies() {
    for (const auto &[name, f] : functions) {
      std::set<int64_t> ids;
      auto &s = *f->getObject("signature");
      if (!block(*f->get("body"), parameterTypes(s, true), resultTypes(s, true),
                 name, ids))
        return std::move(failure);
    }
    std::set<std::string> active;
    std::map<std::string, unsigned> heights;
    if (!visit(interface.host->function, active, heights))
      return std::move(failure);
    if (heights.size() != functions.size() ||
        usedCalculations.size() != calculations.size() ||
        usedDeployments.size() != deployments.size())
      return error("entry.closure",
                   "Host artifact has an unreferenced static dependency");
    return Error::success();
  }

public:
  Admission(const LanguageInterface &interface, const Limits &limits)
      : interface(interface), limits(limits) {
    (void)!!failure;
  }
  Error original(const json::Array &definitions, mlir::ModuleOp module) {
    if (auto e = signatures(definitions))
      return e;
    // Original SSA names native boundaries but has not lowered them yet. Reuse
    // body/graph admission with their reconstructed call signatures; native
    // installation and child authority are checked during executable admission.
    std::map<std::string, json::Object> numericContracts, deploymentContracts;
    for (bool numeric : {true, false}) {
      std::map<std::string, std::pair<json::Array, json::Array>> contracts;
      for (const auto &f : definitions)
        if (auto e = references(*f.getAsObject()->get("body"), contracts,
                                numeric ? "numeric" : "invoke"))
          return e;
      auto &storage = numeric ? numericContracts : deploymentContracts;
      auto &inventory = numeric ? calculations : deployments;
      for (auto &[id, signature] : contracts) {
        auto [it, inserted] = storage.emplace(
            id, json::Object{{"parameters", std::move(signature.first)},
                             {"results", std::move(signature.second)}});
        inventory.emplace(id, &it->second);
      }
    }
    if (auto e = bodies())
      return e;
    std::set<std::string> actual;
    for (auto &op : *module.getBody()) {
      if (mlir::isa<mlir::func::FuncOp>(op))
        continue;
      auto nested = mlir::dyn_cast<mlir::ModuleOp>(op);
      auto id = op.getAttrOfType<mlir::StringAttr>("entry.calculation");
      if (!nested || !id || nested->getAttrs().size() != 1 ||
          !actual.insert(id.getValue().str()).second)
        return error("entry.closure", "unexpected numerical original");
    }
    if (actual != usedCalculations)
      return error("entry.reference", "numerical original inventory differs");
    return Error::success();
  }
  Error run(const json::Value &value) {
    auto *root = value.getAsObject();
    if (!interface.host || !root || root->size() != 6 ||
        root->getString("format") != "zkc.host/0" ||
        root->getString("original") != interface.original ||
        root->getString("entry") != interface.host->function ||
        !root->getArray("functions") || !root->getArray("calculations") ||
        !root->getArray("deployments"))
      return error("entry.artifact",
                   "invalid Host artifact identity or fields");
    if (auto e = signatures(*root->getArray("functions")))
      return e;
    for (bool numerical : {true, false}) {
      auto &inventory = numerical ? calculations : deployments;
      for (const auto &v :
           *root->getArray(numerical ? "calculations" : "deployments")) {
        auto *o = v.getAsObject();
        if (!o || o->size() != 5 || !o->getString("id") ||
            !o->getArray("parameters") || !o->getArray("results") ||
            !o->getString(numerical ? "function" : "operation") ||
            !o->getString(numerical ? "program" : "package") ||
            !inventory.emplace(o->getString("id")->str(), o).second)
          return error("entry.closure", "invalid or duplicate static boundary");
        for (StringRef side : {"parameters", "results"})
          for (const auto &s : *o->getArray(side))
            if (!schema(s))
              return std::move(failure);
        if (numerical) {
          if (!nativeSignature(*o))
            return std::move(failure);
        } else {
          auto operation = *o->getString("operation");
          if (operation != "run" && operation != "prove" &&
              operation != "verify")
            return error("entry.deployment", "unknown deployment operation");
          auto package =
              detail::readPackagedEntry(*o->getString("package"), limits);
          if (!package)
            return package.takeError();
          auto *child = &package->interface;
          if (child->host || (operation == "run") != !bool(child->proof))
            return error("entry.deployment", "child operation kind differs");
          if (!deploymentContract(*o, *child))
            return std::move(failure);
          if (operation == "run") {
            auto program = zkc::detail::readRunProgram(package->artifact);
            if (!program)
              return program.takeError();
            const auto &protocol = child->selectedProtocol();
            auto root = find_if(program->entries, [&](const auto &entry) {
              return entry.name == protocol.symbol;
            });
            if (root == program->entries.end() ||
                root->participants.size() != protocol.roles.size())
              return error("entry.closure",
                           "joint child root participant roster differs");
            for (auto [index, binding] : enumerate(root->participants)) {
              const auto &participantName = binding.second;
              auto participant =
                  find_if(program->participants,
                          [&participantName](const auto &definition) {
                            return definition.name == participantName;
                          });
              if (binding.first != nativeRoleName(index) ||
                  participant == program->participants.end() ||
                  participant->role != binding.first)
                return error("entry.closure",
                             "joint child root participant binding differs");
            }
          } else {
            auto role =
                nativeRoleName(operation == "verify" ? child->proof->verifier
                                                     : child->proof->prover);
            if (auto e = zkc::detail::checkNativeOperationArtifact(
                    package->artifact, child->original, role))
              return e;
          }
        }
      }
      if (inventory.size() > limits.instances)
        return error("source.limit", "static boundary inventory limit");
    }
    return bodies();
  }
};
} // namespace
Error checkHostFunctions(const json::Array &functions,
                         const LanguageInterface &interface,
                         mlir::ModuleOp module, const Limits &limits) {
  return Admission(interface, limits).original(functions, module);
}
Error checkHostArtifact(StringRef bytes, const LanguageInterface &interface,
                        const Limits &limits) {
  auto parsed = parseNaturalJson(bytes, limits.irBytes, 256, "entry.artifact",
                                 "source.limit");
  if (!parsed)
    return parsed.takeError();
  return Admission(interface, limits).run(*parsed);
}
} // namespace zkc::language
