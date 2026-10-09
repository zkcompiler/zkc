#include "zkc/Compiler/PolynomialReduction.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Relations.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <set>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
namespace pir = protocol_ir;
using Indices = SmallVector<unsigned>;
struct Requirement {
  std::string id, reduction, terminal, recipe, verifier, terminalRole;
  Indices subjects, residualSubjects, residualPoint, terminalSubjects,
      terminalPoint;
  unsigned claim, service, residualScalar, terminalScalar, decision;
  std::string composition, reductionSite, terminalSite;
  std::optional<relation::R1CS> externalRelation;
};
bool keys(const json::Object &object, ArrayRef<StringRef> names,
          unsigned extra = 0) {
  return object.size() == names.size() + extra &&
         all_of(names, [&](StringRef name) { return object.get(name); });
}
bool index(const json::Object &object, StringRef key, unsigned &value) {
  auto number = object.getInteger(key);
  if (!number || *number < 0 || *number >= 4096)
    return false;
  value = *number;
  return true;
}
bool indices(const json::Object &object, StringRef key, Indices &values) {
  auto *array = object.getArray(key);
  if (!array || array->empty() || array->size() > 32)
    return false;
  std::set<unsigned> unique;
  for (auto &item : *array) {
    auto number = item.getAsInteger();
    if (!number || *number < 0 || *number >= 4096 ||
        !unique.insert(*number).second)
      return false;
    values.push_back(*number);
  }
  return true;
}
bool name(const json::Object &object, StringRef key, std::string &value) {
  auto string = object.getString(key);
  if (!string || string->empty() || string->size() > 4096 ||
      string->contains('\0'))
    return false;
  value = string->str();
  return true;
}
Expected<SmallVector<Requirement, 1>> parse(StringRef text) {
  auto value =
      parseNaturalJson(text, 1024 * 1024, 64, "polynomial-requirement-format",
                       "polynomial-requirement-limit");
  if (!value)
    return value.takeError();
  auto *object = value->getAsObject();
  if (!object || !keys(*object, {"format", "requirements"}) ||
      object->getString("format") != "zkc.polynomial-requirements/1")
    return error("polynomial-requirement-format");
  auto *array = object->getArray("requirements");
  if (!array || array->empty() || array->size() > 64)
    return error("polynomial-requirement-count");
  SmallVector<Requirement, 1> requirements;
  std::set<std::string> ids, terminals;
  for (auto &value : *array) {
    auto *o = value.getAsObject();
    Requirement r;
    if (!o ||
        !keys(*o,
              {"id", "family", "reduction", "terminal", "recipe", "verifier",
               "terminal_role", "subjects", "claim", "service",
               "residual_subjects", "residual_point", "residual_scalar",
               "terminal_subjects", "terminal_point", "terminal_scalar",
               "decision"},
              unsigned(o->get("composition") != nullptr) +
                  unsigned(o->get("relation") != nullptr)) ||
        (o->getString("family") != "boolean-sum-to-point/1" &&
         o->getString("family") != "r1cs-sum-to-point/1") ||
        !name(*o, "id", r.id) || !name(*o, "reduction", r.reduction) ||
        !name(*o, "terminal", r.terminal) || !name(*o, "recipe", r.recipe) ||
        !name(*o, "verifier", r.verifier) ||
        !name(*o, "terminal_role", r.terminalRole) ||
        !indices(*o, "subjects", r.subjects) || !index(*o, "claim", r.claim) ||
        !index(*o, "service", r.service) ||
        !indices(*o, "residual_subjects", r.residualSubjects) ||
        !indices(*o, "residual_point", r.residualPoint) ||
        !index(*o, "residual_scalar", r.residualScalar) ||
        !indices(*o, "terminal_subjects", r.terminalSubjects) ||
        !indices(*o, "terminal_point", r.terminalPoint) ||
        !index(*o, "terminal_scalar", r.terminalScalar) ||
        !index(*o, "decision", r.decision))
      return error("polynomial-requirement-format");
    if (auto *value = o->get("composition")) {
      auto *c = value->getAsObject();
      if (!c || !keys(*c, {"entry", "reduction_site", "terminal_site"}) ||
          !name(*c, "entry", r.composition) ||
          !name(*c, "reduction_site", r.reductionSite) ||
          !name(*c, "terminal_site", r.terminalSite) ||
          r.reductionSite == r.terminalSite)
        return error("polynomial-requirement-format");
    }
    if (o->getString("family") == "r1cs-sum-to-point/1") {
      auto *asset = o->get("relation");
      if (!asset || r.composition.empty())
        return error("polynomial-requirement-format");
      auto relation = relation::decodeR1CS(*asset);
      if (!relation)
        return relation.takeError();
      r.externalRelation = std::move(*relation);
    } else if (o->get("relation"))
      return error("polynomial-requirement-format");
    if (!ids.insert(r.id).second || !terminals.insert(r.terminal).second ||
        r.reduction == r.terminal)
      return error("polynomial-requirement-duplicate");
    requirements.push_back(std::move(r));
  }
  return requirements;
}
json::Array numbers(ArrayRef<unsigned> values) {
  json::Array result;
  for (auto value : values)
    result.push_back(int64_t(value));
  return result;
}
bool owns(ArrayAttr roles, unsigned index, StringRef role) {
  if (index >= roles.size())
    return false;
  return is_contained(cast<ArrayAttr>(roles[index]),
                      StringAttr::get(roles.getContext(), role));
}
// Recompute all maps from the retained source. Candidate metadata is only a
// consistency check and cannot supply the meaning of a port.
struct Ports {
  pir::ParticipantOp participant;
  Indices inputs, outputs, services;
  std::string servicePort;
  Value input(unsigned original) {
    auto found = find(inputs, original);
    return found == inputs.end() ? Value()
                                 : participant.getBody().front().getArgument(
                                       found - inputs.begin());
  }
  Value output(unsigned original) {
    auto found = find(outputs, original);
    return found == outputs.end()
               ? Value()
               : participant.getBody().front().back().getOperand(
                     found - outputs.begin());
  }
  unsigned outputPosition(unsigned original) const {
    return find(outputs, original) - outputs.begin();
  }
  unsigned inputPosition(unsigned original) const {
    return find(inputs, original) - inputs.begin();
  }
};
bool sameIndices(Attribute attr, ArrayRef<unsigned> expected) {
  auto array = dyn_cast_or_null<ArrayAttr>(attr);
  if (!array || array.size() != expected.size())
    return false;
  for (auto [value, index] : zip(array, expected)) {
    auto integer = dyn_cast<IntegerAttr>(value);
    if (!integer || integer.getInt() != index)
      return false;
  }
  return true;
}
std::optional<Ports> ports(pir::MathematicalOp source,
                           pir::ProtocolModuleOp candidate, StringRef role) {
  Ports result;
  if (!is_contained(source.getRoles(),
                    StringAttr::get(source.getContext(), role)))
    return {};
  for (auto p : candidate.getBody().front().getOps<pir::ParticipantOp>())
    if (p.getInstance() == source.getSymName() && p.getRole() == role) {
      if (result.participant)
        return {};
      result.participant = p;
    }
  if (!result.participant)
    return {};
  SmallVector<Type> inputTypes, outputTypes;
  SmallVector<Attribute> servicePorts;
  Builder builder(source.getContext());
  unsigned roleIndex = 0;
  for (unsigned i = 0; i < source.getFunctionType().getNumInputs(); ++i) {
    if (!owns(source.getInputRoles(), i, role))
      continue;
    auto type = source.getFunctionType().getInput(i);
    if (auto service = dyn_cast<pir::ServiceReferenceType>(type)) {
      result.services.push_back(i);
      result.servicePort = "service_" + std::to_string(roleIndex);
      servicePorts.push_back(
          builder.getArrayAttr({builder.getStringAttr(result.servicePort),
                                builder.getStringAttr(service.getContract()),
                                builder.getI64IntegerAttr(roleIndex)}));
    } else {
      result.inputs.push_back(i);
      inputTypes.push_back(type);
    }
    ++roleIndex;
  }
  for (unsigned i = 0; i < source.getFunctionType().getNumResults(); ++i)
    if (owns(source.getOutputRoles(), i, role)) {
      result.outputs.push_back(i);
      outputTypes.push_back(source.getFunctionType().getResult(i));
    }
  if (result.participant.getFunctionType() !=
      builder.getFunctionType(inputTypes, outputTypes))
    return {};
  auto declared = result.participant->getAttrOfType<ArrayAttr>("service_ports");
  if (servicePorts.empty() ? declared && !declared.empty()
                           : declared != builder.getArrayAttr(servicePorts))
    return {};
  unsigned matches = 0;
  for (auto projection :
       candidate.getBody().front().getOps<pir::ProjectionOp>())
    for (auto item : projection.getInterfaces()) {
      auto interface = cast<DictionaryAttr>(item);
      if (interface.getAs<StringAttr>("source").getValue() !=
          source.getSymName())
        continue;
      if (interface.get("original_type") != source.getFunctionTypeAttr() ||
          interface.get("roles") != source.getRoles() ||
          interface.get("input_roles") != source.getInputRoles() ||
          interface.get("output_roles") != source.getOutputRoles())
        return {};
      for (auto item : interface.getAs<ArrayAttr>("participants")) {
        auto p = cast<DictionaryAttr>(item);
        if (p.getAs<StringAttr>("role").getValue() != role)
          continue;
        if (++matches != 1 ||
            p.getAs<FlatSymbolRefAttr>("participant").getValue() !=
                result.participant.getSymName() ||
            !sameIndices(p.get("inputs"), result.inputs) ||
            !sameIndices(p.get("outputs"), result.outputs) ||
            !sameIndices(p.get("service_inputs"), result.services))
          return {};
      }
    }
  return matches == 1 ? std::optional<Ports>(result) : std::nullopt;
}
template <typename Op> Op definition(Value value) {
  return value ? value.getDefiningOp<Op>() : Op{};
}
bool constant(Value value, StringRef literal) {
  auto op = definition<algebra::ConstantFieldOp>(value);
  return op && op.getValue() == literal;
}
bool evaluates(Value value, Value polynomial, Value point) {
  auto op = definition<poly::EvaluatePolynomialOp>(value);
  return op && op.getPolynomial() == polynomial && op.getPoint().size() == 1 &&
         op.getPoint().front() == point;
}
bool recipeOperation(Operation *op) {
  return isa<poly::MultilinearPolynomialOp, poly::AddPolynomialOp,
             poly::MultiplyPolynomialOp, poly::ConstantPolynomialOp,
             algebra::ConstantFieldOp, algebra::ArrayAtOp, algebra::FieldAddOp,
             algebra::FieldMultiplyOp, algebra::SubtractFieldOp,
             tensor::FromElementsOp>(op);
}
// Match pure DAGs without algebraic equality or location-based provenance.
// Multiple equal source nodes may share one candidate node.
bool sameRecipe(Value source, Value candidate,
                llvm::DenseMap<Value, Value> arguments) {
  SmallVector<std::pair<Value, Value>> pending{{source, candidate}};
  llvm::DenseSet<std::pair<Value, Value>> visited;
  while (!pending.empty()) {
    auto [a, b] = pending.pop_back_val();
    if (!visited.insert({a, b}).second)
      continue;
    if (visited.size() > 10000 || !b || a.getType() != b.getType())
      return false;
    auto mapped = arguments.find(a);
    if (mapped != arguments.end()) {
      if (mapped->second != b)
        return false;
      continue;
    }
    auto *x = a.getDefiningOp(), *y = b.getDefiningOp();
    if (!x || !y || !recipeOperation(x) || x->getName() != y->getName() ||
        x->getAttrDictionary() != y->getAttrDictionary() ||
        x->getNumOperands() != y->getNumOperands())
      return false;
    for (auto [left, right] : zip(x->getOperands(), y->getOperands()))
      pending.emplace_back(left, right);
  }
  return true;
}
bool distinctIndices(ArrayRef<unsigned> values) {
  return std::set<unsigned>(values.begin(), values.end()).size() ==
         values.size();
}
Expected<json::Value> check(pir::ProtocolModuleOp original,
                            pir::ProtocolModuleOp candidate,
                            const Requirement &r) {
  auto refuse = [&](StringRef detail) -> Error {
    return error("polynomial-correspondence", r.id + ": " + detail);
  };
  auto source = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(original, r.reduction));
  auto terminal = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(original, r.terminal));
  auto recipe = dyn_cast_or_null<func::FuncOp>(
      SymbolTable::lookupSymbolIn(original, r.recipe));
  if (!source || !terminal || !recipe || !recipe.isPrivate() ||
      !hasSingleElement(recipe.getBody()) ||
      recipe.getFunctionType().getNumResults() != 1 ||
      source.getRoles().size() != 2 || terminal.getRoles().size() != 1)
    return refuse("source entries or recipe");
  auto type =
      dyn_cast<poly::PolynomialType>(recipe.getFunctionType().getResult(0));
  if (!type || type.getArity() < 1 || type.getDomain() != "bls12-381.fr" ||
      recipe.getNumArguments() != r.subjects.size() ||
      r.residualSubjects.size() != r.subjects.size() ||
      r.terminalSubjects.size() != r.subjects.size() ||
      r.residualPoint.size() != type.getArity() ||
      r.terminalPoint.size() != type.getArity())
    return refuse("recipe type or arity");
  auto field = algebra::FieldType::get(original.getContext(), type.getDomain());
  unsigned count = 0;
  for (auto &op : recipe.getBody().front())
    if (++count > 10000 || (!isa<func::ReturnOp>(op) && !recipeOperation(&op)))
      return refuse("recipe vocabulary");
  poly::Degrees degrees;
  if (failed(poly::deriveDegrees(recipe.getBody().front(), degrees)))
    return refuse("recipe bounds");
  Value recipeValue = recipe.getBody().front().back().getOperand(0);
  auto bounds = degrees.bounds.find(recipeValue);
  if (bounds == degrees.bounds.end() ||
      bounds->second.size() != type.getArity() ||
      any_of(bounds->second, [](uint64_t d) { return d >= 64; }))
    return refuse("recipe bounds");
  auto verifier = ports(source, candidate, r.verifier),
       end = ports(terminal, candidate, r.terminalRole);
  if (!verifier || !end)
    return refuse("source participant ports");
  if (verifier->services != Indices{r.service} || !end->services.empty() ||
      r.service >= source.getFunctionType().getNumInputs() ||
      cast<ArrayAttr>(source.getInputRoles()[r.service]).size() != 1 ||
      cast<pir::ServiceReferenceType>(
          source.getFunctionType().getInput(r.service))
              .getContract() != "random.bls12-381.fr/1")
    return refuse("challenge service");
  Indices incoming(r.subjects), outgoing(r.residualSubjects),
      terminalInputs(r.terminalSubjects);
  incoming.push_back(r.claim);
  incoming.push_back(r.service);
  append_range(outgoing, r.residualPoint);
  outgoing.push_back(r.residualScalar);
  append_range(terminalInputs, r.terminalPoint);
  terminalInputs.push_back(r.terminalScalar);
  if (!distinctIndices(incoming) || !distinctIndices(outgoing) ||
      !distinctIndices(terminalInputs) ||
      verifier->inputs.size() != r.subjects.size() + 1 ||
      verifier->outputs.size() != outgoing.size() ||
      end->inputs.size() != terminalInputs.size() ||
      end->outputs != Indices{r.decision})
    return refuse("boundary map");
  for (auto [i, originalIndex] : enumerate(r.subjects)) {
    auto input = verifier->input(originalIndex),
         output = verifier->output(r.residualSubjects[i]);
    auto ti = end->input(r.terminalSubjects[i]);
    if (!input || !ti || input != output || input.getType() != ti.getType() ||
        input.getType() != recipe.getArgument(i).getType())
      return refuse("residual subject");
    auto array = dyn_cast<RankedTensorType>(input.getType());
    if (input.getType() != field && (!array || !algebra::isFieldArray(array) ||
                                     array.getElementType() != field))
      return refuse("subject domain");
  }
  for (unsigned index : outgoing)
    if (!owns(source.getOutputRoles(), index, r.verifier) ||
        cast<ArrayAttr>(source.getOutputRoles()[index]).size() != 1)
      return refuse("residual must belong only to verifier");
  if (!json::isUTF8(verifier->participant.getSymName()) ||
      !json::isUTF8(end->participant.getSymName()))
    return refuse("report symbols must be UTF-8");
  auto previous = verifier->input(r.claim),
       terminalScalar = end->input(r.terminalScalar);
  if (!previous || previous.getType() != field || !terminalScalar ||
      terminalScalar.getType() != field)
    return refuse("claim type");
  SmallVector<Value> terminalPoints;
  for (auto i : r.terminalPoint) {
    auto point = end->input(i);
    if (!point || point.getType() != field)
      return refuse("terminal point");
    terminalPoints.push_back(point);
  }
  // Original terminal must resolve the same owned recipe once, using the
  // named original entry inputs. Projection matching below checks its uses.
  SmallVector<func::CallOp> calls;
  terminal.walk([&](func::CallOp call) { calls.push_back(call); });
  if (calls.size() != 1 ||
      SymbolTable::lookupNearestSymbolFrom(
          calls[0], calls[0].getCalleeAttr()) != recipe.getOperation() ||
      calls[0].getNumOperands() != r.terminalSubjects.size())
    return refuse("terminal recipe identity");
  for (auto [i, index] : enumerate(r.terminalSubjects))
    if (calls[0].getOperand(i) != terminal.getBody().front().getArgument(index))
      return refuse("terminal recipe subjects");
  auto originalDecision =
      terminal.getBody().front().back().getOperand(r.decision);
  auto originalEq = definition<algebra::FieldEqualOp>(originalDecision);
  auto originalEvaluation = definition<poly::EvaluatePolynomialOp>(
      originalEq ? originalEq.getLhs() : Value{});
  if (!originalEvaluation ||
      originalEvaluation.getPolynomial() != calls[0].getResult(0) ||
      originalEvaluation.getPoint().size() != type.getArity())
    return refuse("terminal recipe use");
  if (originalEq.getRhs() !=
      terminal.getBody().front().getArgument(r.terminalScalar))
    return refuse("original terminal scalar");
  for (auto [point, index] :
       zip(originalEvaluation.getPoint(), r.terminalPoint))
    if (point != terminal.getBody().front().getArgument(index))
      return refuse("original terminal point");
  std::string prover;
  for (auto role : source.getRoles())
    if (cast<StringAttr>(role).getValue() != r.verifier)
      prover = cast<StringAttr>(role).getValue().str();
  SmallVector<Operation *> actions;
  for (auto &op : verifier->participant.getBody().front())
    if (isa<pir::AwaitOp, pir::EmitOp, pir::ParticipantQueryOp, local::GuardOp>(
            op))
      actions.push_back(&op);
    else if (!isa<pir::FinishOp>(op) && !mathematical::isTotal(&op))
      return refuse("extra verifier action");
  if (actions.size() != type.getArity() * 4)
    return refuse("round actions");
  json::Array rounds;
  std::set<std::string> sites;
  for (unsigned k = 0; k < type.getArity(); ++k) {
    auto receive = dyn_cast<pir::AwaitOp>(actions[4 * k]);
    auto guard = dyn_cast<local::GuardOp>(actions[4 * k + 1]);
    auto query = dyn_cast<pir::ParticipantQueryOp>(actions[4 * k + 2]);
    auto send = dyn_cast<pir::EmitOp>(actions[4 * k + 3]);
    auto payload =
        RankedTensorType::get({int64_t(bounds->second[k] + 1)}, field);
    if (!receive || !guard || !query || !send || receive.getPeer() != prover ||
        send.getPeer() != prover || receive.getOutput().getType() != payload ||
        query.getPort() != verifier->servicePort ||
        query.getMethod() != "draw" || query->getNumOperands() != 0 ||
        query->getNumResults() != 1 || query->getResult(0).getType() != field ||
        send.getInput() != query->getResult(0))
      return refuse("round receive/query/emit");
    auto eq = definition<algebra::FieldEqualOp>(guard->getOperand(0));
    auto sum = definition<algebra::FieldAddOp>(eq ? eq.getLhs() : Value{});
    auto zero =
        definition<poly::EvaluatePolynomialOp>(sum ? sum.getLhs() : Value{});
    auto one =
        definition<poly::EvaluatePolynomialOp>(sum ? sum.getRhs() : Value{});
    auto q = definition<poly::CoefficientPolynomialOp>(
        zero ? zero.getPolynomial() : Value{});
    if (!q || !one || q.getCoefficients() != receive.getOutput() ||
        one.getPolynomial() != q.getPolynomial() ||
        zero.getPoint().size() != 1 || one.getPoint().size() != 1 ||
        !constant(zero.getPoint().front(), "0") ||
        !constant(one.getPoint().front(), "1"))
      return refuse("round guard polynomial");
    if (k == 0 ? eq.getRhs() != previous
               : !evaluates(eq.getRhs(), previous,
                            actions[4 * (k - 1) + 2]->getResult(0)))
      return refuse("round scalar chain");
    previous = q.getPolynomial();
    if (verifier->output(r.residualPoint[k]) != query->getResult(0))
      return refuse("residual challenge order");
    for (auto site :
         {receive.getSite(), guard.getSite(), query.getSite(), send.getSite()})
      if (!json::isUTF8(site) || !sites.insert(site.str()).second)
        return refuse("round sites must be distinct UTF-8 identifiers");
    rounds.push_back(json::Object{{"degree", int64_t(bounds->second[k])},
                                  {"receive", receive.getSite().str()},
                                  {"guard", guard.getSite().str()},
                                  {"query", query.getSite().str()},
                                  {"send", send.getSite().str()}});
  }
  if (!evaluates(verifier->output(r.residualScalar), previous,
                 actions[actions.size() - 2]->getResult(0)))
    return refuse("residual scalar");
  for (auto &op : end->participant.getBody().front())
    if (!isa<pir::FinishOp>(op) && !mathematical::isTotal(&op))
      return refuse("terminal actions");
  auto decision = end->output(r.decision);
  auto eq = definition<algebra::FieldEqualOp>(decision);
  auto evaluation =
      definition<poly::EvaluatePolynomialOp>(eq ? eq.getLhs() : Value{});
  if (!evaluation || eq.getRhs() != terminalScalar ||
      !equal(evaluation.getPoint(), terminalPoints))
    return refuse("terminal decision");
  llvm::DenseMap<Value, Value> argumentMap;
  for (auto [i, arg] : enumerate(recipe.getArguments()))
    argumentMap[arg] = end->input(r.terminalSubjects[i]);
  if (!sameRecipe(recipeValue, evaluation.getPolynomial(),
                  std::move(argumentMap)))
    return refuse("terminal recipe expression");
  json::Array connector;
  for (auto [output, input] : zip(outgoing, terminalInputs)) {
    auto a = verifier->output(output), b = end->input(input);
    if (!a || !b || a.getType() != b.getType())
      return refuse("connector type");
    connector.push_back(json::Array{int64_t(verifier->outputPosition(output)),
                                    int64_t(end->inputPosition(input))});
  }
  return json::Object{
      {"id", r.id},
      {"reduction", r.reduction},
      {"terminal", r.terminal},
      {"verifier", verifier->participant.getSymName().str()},
      {"verifier_role", r.verifier},
      {"terminal_role", r.terminalRole},
      {"terminal_participant", end->participant.getSymName().str()},
      {"field", type.getDomain().str()},
      {"arity", int64_t(type.getArity())},
      {"recipe", r.recipe},
      {"original_inputs", numbers(verifier->inputs)},
      {"original_service_inputs", numbers(verifier->services)},
      {"original_outputs", numbers(verifier->outputs)},
      {"service_port", verifier->servicePort},
      {"rounds", std::move(rounds)},
      {"connector", std::move(connector)},
      {"decision_output", int64_t(end->outputPosition(r.decision))},
      {"decision_operation", "algebra.field_equal"}};
}
} // namespace
namespace {
Expected<json::Value> checkComposition(pir::ProtocolModuleOp source,
                                       pir::ProtocolModuleOp expected,
                                       pir::ProtocolModuleOp candidate,
                                       const Requirement &r) {
  auto refuse = [&](StringRef detail) -> Error {
    return error("polynomial-composition", r.id + ": " + detail);
  };
  auto function = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(source, r.composition));
  if (!function || function.getFunctionType().getNumResults() != 1 ||
      !function.getFunctionType().getResult(0).isSignlessInteger(1))
    return refuse("expected a single-decision wrapper");
  SmallVector<pir::ApplyOp> calls;
  for (auto &op : function.getBody().front()) {
    if (auto call = dyn_cast<pir::ApplyOp>(op))
      calls.push_back(call);
    else if (!calls.empty() && !isa<pir::MathematicalReturnOp>(op))
      return refuse("wrapper suffix must be reduction, terminal, return");
  }
  if (calls.size() != 2 || calls[0].getCallee() != r.reduction ||
      calls[1].getCallee() != r.terminal ||
      calls[0].getSite() != r.reductionSite ||
      calls[1].getSite() != r.terminalSite)
    return refuse("actual component applications");
  auto reduction = cast<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(source, r.reduction));
  auto terminal = cast<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(source, r.terminal));
  auto roleIndex =
      llvm::find(reduction.getRoles(),
                 StringAttr::get(source.getContext(), r.verifier)) -
      reduction.getRoles().begin();
  auto mappedVerifier = calls[0].getRoles()[roleIndex];
  if (calls[1].getRoles().size() != 1 ||
      calls[1].getRoles()[0] != mappedVerifier ||
      cast<ArrayAttr>(function.getOutputRoles()[0]) !=
          ArrayAttr::get(source.getContext(), {mappedVerifier}) ||
      terminal.getFunctionType().getNumResults() != 1 || r.decision != 0 ||
      function.getBody().front().back().getOperand(0) != calls[1].getResult(0))
    return refuse("actual role substitution or decision");
  Indices outputs(r.residualSubjects), inputs(r.terminalSubjects);
  append_range(outputs, r.residualPoint);
  outputs.push_back(r.residualScalar);
  append_range(inputs, r.terminalPoint);
  inputs.push_back(r.terminalScalar);
  for (auto [output, input] : zip(outputs, inputs))
    if (calls[1].getOperand(input) != calls[0].getResult(output))
      return refuse("terminal must consume the actual residual SSA values");
  // This bounded family accepts the exact unsimplified projection of the
  // wrapper. Source requirements, never candidate interface metadata, fix it.
  // The separately checked components retain the looser prover-calculation
  // policy. General equivalence/transfer certificates remain outside scope.
  for (auto role : function.getRoles()) {
    auto name = cast<StringAttr>(role).getValue();
    auto actual = ports(function, candidate, name),
         original = ports(function, expected, name);
    if (!actual || !original ||
        !OperationEquivalence::isEquivalentTo(
            original->participant, actual->participant,
            OperationEquivalence::IgnoreLocations))
      return refuse("composed participant differs from original expansion");
  }
  return json::Object{
      {"entry", r.composition},
      {"reduction_site", r.reductionSite},
      {"terminal_site", r.terminalSite},
      {"verifier_role", cast<StringAttr>(mappedVerifier).getValue().str()},
      {"decision_output", 0}};
}
} // namespace

Expected<json::Value> checkPolynomialReductions(ModuleOp original,
                                                ModuleOp candidate,
                                                StringRef text) {
  auto requirements = parse(text);
  if (!requirements)
    return requirements.takeError();
  if (original.getContext() != candidate.getContext() ||
      failed(verify(original)) || failed(verify(candidate)) ||
      !hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()))
    return error("polynomial-correspondence-module");
  auto source = dyn_cast<pir::ProtocolModuleOp>(original.getBody()->front());
  auto target = dyn_cast<pir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!source || !target || source.getProfile() != pir::Profile::Protocol ||
      target.getProfile() != pir::Profile::Participant)
    return error("polynomial-correspondence-profile");
  for (auto &r : *requirements) {
    if (!r.externalRelation)
      continue;
    auto authored = relation::authorR1CSSumcheck(*r.externalRelation,
                                                 *original.getContext());
    if (!authored)
      return authored.takeError();
    if (!OperationEquivalence::isEquivalentTo(
            (*authored).get(), original.getOperation(),
            OperationEquivalence::IgnoreLocations))
      return error("r1cs-source-correspondence",
                   "original must match the native adapter for the independent "
                   "relation");
  }
  // The public independent-candidate API also checks the actual original
  // program after unsimplified projection. A correct substitute candidate
  // cannot make an incorrect authored verifier receive this report.
  OwningOpRef<ModuleOp> projected(cast<ModuleOp>(original->clone()));
  PassManager preparation(original.getContext());
  preparation.addPass(protocol::createProjectProtocolPass(false));
  if (failed(preparation.run(*projected)))
    return error("polynomial-correspondence-source");
  auto expected = cast<pir::ProtocolModuleOp>(projected->getBody()->front());
  // Symbol-name equality in a participant is insufficient when a referenced
  // local function or relation declaration has changed. Freeze dependencies
  // and dispatch definitions against the independently projected original.
  for (auto &op : expected.getBody().front()) {
    if (isa<pir::ParticipantOp, pir::ProjectionOp>(op))
      continue;
    auto symbol = SymbolTable::getSymbolName(&op);
    auto *other =
        symbol ? SymbolTable::lookupSymbolIn(target, symbol) : nullptr;
    if (!other || !OperationEquivalence::isEquivalentTo(
                      &op, other, OperationEquivalence::IgnoreLocations))
      return error("polynomial-correspondence-declaration");
  }
  for (auto &op : target.getBody().front()) {
    if (isa<pir::ParticipantOp, pir::ProjectionOp>(op))
      continue;
    auto symbol = SymbolTable::getSymbolName(&op);
    if (!symbol || !SymbolTable::lookupSymbolIn(expected, symbol))
      return error("polynomial-correspondence-declaration");
  }
  auto sourceInterface = [](pir::ProtocolModuleOp unit,
                            StringRef name) -> DictionaryAttr {
    for (auto projection : unit.getBody().front().getOps<pir::ProjectionOp>())
      for (auto item : projection.getInterfaces()) {
        auto interface = cast<DictionaryAttr>(item);
        if (interface.getAs<StringAttr>("source").getValue() == name)
          return interface;
      }
    return {};
  };
  for (auto &r : *requirements) {
    for (StringRef name : {StringRef(r.reduction), StringRef(r.terminal),
                           StringRef(r.composition)}) {
      if (name.empty())
        continue;
      auto required = sourceInterface(expected, name);
      if (!required || required != sourceInterface(target, name))
        return error("polynomial-correspondence-interface");
    }
  }
  json::Array results, canonical;
  for (auto &r : *requirements) {
    auto sourceResult = check(source, expected, r);
    if (!sourceResult)
      return sourceResult.takeError();
    auto result = check(source, target, r);
    if (!result)
      return result.takeError();
    if (!r.composition.empty()) {
      auto composition = checkComposition(source, expected, target, r);
      if (!composition)
        return composition.takeError();
      (*result->getAsObject())["composition"] = std::move(*composition);
    }
    results.push_back(std::move(*result));
    canonical.push_back(
        json::Object{{"id", r.id},
                     {"family", r.externalRelation ? "r1cs-sum-to-point/1"
                                                   : "boolean-sum-to-point/1"},
                     {"reduction", r.reduction},
                     {"terminal", r.terminal},
                     {"recipe", r.recipe},
                     {"verifier", r.verifier},
                     {"terminal_role", r.terminalRole},
                     {"subjects", numbers(r.subjects)},
                     {"claim", int64_t(r.claim)},
                     {"service", int64_t(r.service)},
                     {"residual_subjects", numbers(r.residualSubjects)},
                     {"residual_point", numbers(r.residualPoint)},
                     {"residual_scalar", int64_t(r.residualScalar)},
                     {"terminal_subjects", numbers(r.terminalSubjects)},
                     {"terminal_point", numbers(r.terminalPoint)},
                     {"terminal_scalar", int64_t(r.terminalScalar)},
                     {"decision", int64_t(r.decision)}});
    if (r.externalRelation) {
      (*canonical.back().getAsObject())["relation"] =
          r.externalRelation->encode();
      auto &record = *results.back().getAsObject();
      record["family"] = "r1cs-sum-to-point/1";
      record["relation_identity"] = r.externalRelation->identity();
      record["relation_scope"] =
          "exact native adapter source for the independent R1CS; adapter, "
          "expansion and lowering remain trusted/tested; no cryptographic "
          "theorem";
    }
    if (!r.composition.empty())
      (*canonical.back().getAsObject())["composition"] =
          json::Object{{"entry", r.composition},
                       {"reduction_site", r.reductionSite},
                       {"terminal_site", r.terminalSite}};
  }
  std::string requirementSource, originalIR, candidateIR;
  raw_string_ostream(requirementSource)
      << json::Value(json::Object{{"format", "zkc.polynomial-requirements/1"},
                                  {"requirements", std::move(canonical)}});
  raw_string_ostream sourceStream(originalIR), candidateStream(candidateIR);
  original.print(sourceStream);
  candidate.print(candidateStream);
  auto digest = [](StringRef value) {
    return toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
  };
  return json::Object{
      {"format", "zkc.polynomial-correspondence/1"},
      {"requirements", std::move(results)},
      {"requirement_source", requirementSource},
      {"requirements_sha256", digest(requirementSource)},
      {"original_ir_sha256", digest(originalIR)},
      {"candidate_ir_sha256", digest(candidateIR)},
      {"scope", "source and candidate satisfy the listed structural "
                "requirements; this analysis is not an executable certificate; "
                "subsequent lowerings and connector execution trusted/tested"}};
}
} // namespace zkc
