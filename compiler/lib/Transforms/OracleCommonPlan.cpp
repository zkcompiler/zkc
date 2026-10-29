#include "OracleCommonPlan.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
using IDs = std::vector<unsigned>;
using Types = std::vector<Type>;
Error refuse() { return error("oracle-common-profile"); }
Expected<Type> converted(Type type) {
  if (auto handle = dyn_cast<pir::OracleHandleType>(type))
    return oracleReferenceType(handle.getKind());
  if (auto sequence = dyn_cast<pir::OracleSequenceType>(type)) {
    auto element = oracleReferenceType(sequence.getKind());
    if (!element)
      return element.takeError();
    return Type(data::SequenceType::get(type.getContext(), *element));
  }
  return type;
}
bool logical(Type type) {
  return isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
}
Expected<BindingApplication> length(pir::OracleKindAttr kind) {
  auto answer = encodeBoundType(kind.getAnswerType(), false);
  if (!answer)
    return answer.takeError();
  if (answer->kind == "index")
    return BindingApplication{"indices.length", {}, ""};
  if (answer->kind == "field" || answer->kind == "group")
    return BindingApplication{answer->kind == "field" ? "vector.length"
                                                      : "curve.length",
                              {answer->identity},
                              ""};
  return BindingApplication{"sequence.length", {answer->spelling()}, ""};
}
struct PlanBuilder {
  ModuleOp source;
  pir::MathematicalOp program;
  const OracleCommonRequirements &requirements;
  ArrayRef<OracleCommonController> controllers;
  ArrayRef<std::vector<func::FuncOp>> allocators;
  ArrayRef<OracleMerkleFunctions> merkle;
  std::map<unsigned, unsigned> inputRows;
  Builder builder;
  Type index;
  OracleCommonPlan result;
  unsigned next = 0, allowance = 100000;
  std::string occurrencePrefix;
  std::map<std::pair<unsigned, unsigned>, unsigned> store;
  llvm::DenseMap<Value, unsigned> values;
  struct DataView {
    unsigned reference;
    std::string holder;
    pir::OracleKindAttr kind;
  };
  llvm::DenseMap<Value, DataView> dataViews;
  std::vector<unsigned> coordinates;
  explicit PlanBuilder(ModuleOp source, pir::MathematicalOp program,
                       const OracleCommonRequirements &requirements,
                       ArrayRef<OracleCommonController> controllers,
                       ArrayRef<std::vector<func::FuncOp>> allocators,
                       ArrayRef<OracleMerkleFunctions> merkle)
      : source(source), program(program), requirements(requirements),
        controllers(controllers), allocators(allocators), merkle(merkle),
        builder(source.getContext()),
        index(
            IntegerType::get(source.getContext(), 64, IntegerType::Unsigned)) {
    llvm::StringSet<> used;
    program.walk([&](Operation *op) {
      if (auto site = op->getAttrOfType<StringAttr>("site")) {
        auto name = site.getValue();
        if (name.consume_front("oracle_")) {
          auto separator = name.find('_');
          if (separator != StringRef::npos)
            used.insert(name.take_front(separator));
        }
      }
    });
    for (unsigned suffix = 0;; ++suffix)
      if (!used.contains(std::to_string(suffix))) {
        occurrencePrefix = "oracle_" + std::to_string(suffix) + "_";
        break;
      }
  }
  unsigned id() { return next++; }
  Expected<IDs> make(OracleCommonBlock &block, StringRef name, TypeRange types,
                     ArrayRef<unsigned> inputs, DictionaryAttr attributes = {},
                     std::shared_ptr<OracleCommonBlock> region = {}) {
    if (!allowance || next + types.size() > 1000000)
      return error("oracle-common-limit");
    --allowance;
    OracleCommonInstruction instruction;
    instruction.name = name.str();
    instruction.attributes =
        attributes ? attributes : builder.getDictionaryAttr({});
    instruction.inputs.assign(inputs.begin(), inputs.end());
    instruction.types.assign(types.begin(), types.end());
    instruction.region = std::move(region);
    for ([[maybe_unused]] Type type : types)
      instruction.outputs.push_back(id());
    IDs outputs = instruction.outputs;
    block.instructions.push_back(std::move(instruction));
    return outputs;
  }
  DictionaryAttr attrs(std::initializer_list<NamedAttribute> values) {
    return builder.getDictionaryAttr(values);
  }
  NamedAttribute text(StringRef key, StringRef value) {
    return builder.getNamedAttr(key, builder.getStringAttr(value));
  }
  Expected<unsigned> constant(OracleCommonBlock &block, uint64_t value) {
    auto output = make(block, "data.index", index, {},
                       attrs({text("value", std::to_string(value))}));
    if (!output)
      return output.takeError();
    return output->front();
  }
  std::string site(ArrayRef<unsigned> path, StringRef label,
                   StringRef role = {}) {
    std::string name = occurrencePrefix +
                       std::to_string(result.occurrences.size()) + "_" +
                       label.str();
    result.occurrences.push_back(
        {name, label.str(), role.str(), {path.begin(), path.end()}});
    return name;
  }

  Expected<IDs> call(OracleCommonBlock &block, func::FuncOp helper,
                     StringRef role, ArrayRef<unsigned> inputs,
                     StringRef site) {
    if (!helper || helper.getNumResults() != 1)
      return error("oracle-common-helper");
    auto outcome = dyn_cast<exec::OutcomeType>(helper.getResultTypes()[0]);
    if (!outcome || helper.getNumArguments() != inputs.size() + 1)
      return error("oracle-common-helper");
    return make(
        block, "protocol.local_call", outcome.getPayload(), inputs,
        attrs({builder.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
               text("role", role), text("site", site)}));
  }
  Expected<IDs> call(OracleCommonBlock &block, const OracleLocalRecipe &local,
                     StringRef role, ArrayRef<unsigned> inputs,
                     StringRef site) {
    return make(block, "protocol.local_call", local.outputs, inputs,
                attrs({builder.getNamedAttr(
                           "callee", FlatSymbolRefAttr::get(
                                         builder.getContext(), local.name)),
                       text("role", role), text("site", site)}));
  }
  Expected<unsigned> assemble(OracleCommonBlock &block, Type type,
                              ArrayRef<unsigned> components,
                              ArrayRef<std::string> roles) {
    SmallVector<StringRef> names;
    for (const auto &role : roles)
      names.push_back(role);
    auto output = make(
        block, "protocol.assemble_roles", type, components,
        attrs({builder.getNamedAttr("roles", builder.getStrArrayAttr(names))}));
    if (!output)
      return output.takeError();
    return output->front();
  }
  Expected<unsigned> value(Value original) {
    auto found = values.find(original);
    if (found == values.end())
      return error("oracle-common-value");
    return found->second;
  }
  Error demand(OracleCommonBlock &block, Value original,
               ArrayRef<unsigned> path) {
    if (values.contains(original))
      return Error::success();
    auto found = dataViews.find(original);
    if (found == dataViews.end())
      return error("oracle-common-value");
    const auto &view = found->second;
    auto *body =
        controller(view.holder, view.kind, OracleControllerAccess::Holder);
    if (!body || !body->contents)
      return error("oracle-common-helper");
    auto captures = stores(*body);
    if (!captures)
      return captures.takeError();
    IDs arguments{view.reference};
    append_range(arguments, *captures);
    auto output = call(block, body->contents, view.holder, arguments,
                       site(path, "component_data", view.holder));
    if (!output)
      return output.takeError();
    values[original] = output->front();
    return Error::success();
  }
  Expected<IDs> inputs(ValueRange originals) {
    IDs result;
    for (Value original : originals) {
      auto mapped = value(original);
      if (!mapped)
        return mapped.takeError();
      result.push_back(*mapped);
    }
    return result;
  }
  const OracleQueryController *controller(
      StringRef role, pir::OracleKindAttr kind,
      OracleControllerAccess access = OracleControllerAccess::Available) {
    auto reference = cantFail(oracleReferenceType(kind));
    for (const auto &item : controllers)
      if (item.role == role && item.access == access &&
          cantFail(oracleReferenceType(item.kind)) == reference)
        return &item.body;
    return nullptr;
  }
  Expected<IDs> stores(const OracleQueryController &body) {
    IDs inputs;
    for (const auto &constructor : body.constructors) {
      auto found = store.find({constructor.source, constructor.role});
      if (found == store.end())
        return error("oracle-common-store");
      inputs.push_back(found->second);
    }
    return inputs;
  }
  OracleLocalRecipe local(TypeRange inputs, TypeRange outputs) {
    OracleLocalRecipe recipe;
    auto unit = cast<pir::ProtocolModuleOp>(source.getBody()->front());
    unsigned ordinal = 0;
    for (auto other : unit.getBody().front().getOps<pir::MathematicalOp>()) {
      if (other == program)
        break;
      ++ordinal;
    }
    std::string prefix =
        "_oracle_common_local_" + std::to_string(ordinal) + "_";
    unsigned suffix = result.locals.size();
    do {
      recipe.name = prefix + std::to_string(suffix++);
    } while (SymbolTable::lookupSymbolIn(unit, recipe.name) ||
             any_of(result.locals, [&](const auto &other) {
               return other.name == recipe.name;
             }));
    recipe.inputs.assign(inputs.begin(), inputs.end());
    recipe.outputs.assign(outputs.begin(), outputs.end());
    return recipe;
  }
  IDs apply(OracleLocalRecipe &recipe, BindingApplication binding,
            TypeRange types, ArrayRef<unsigned> inputs,
            ArrayRef<std::string> parameters = {}) {
    unsigned next = recipe.inputs.size();
    for (const auto &instruction : recipe.instructions)
      next += instruction.outputs.size();
    OracleLocalInstruction instruction{std::move(binding),
                                       {parameters.begin(), parameters.end()},
                                       {inputs.begin(), inputs.end()},
                                       {},
                                       {types.begin(), types.end()}};
    for ([[maybe_unused]] Type type : types)
      instruction.outputs.push_back(next++);
    auto outputs = instruction.outputs;
    recipe.instructions.push_back(std::move(instruction));
    return outputs;
  }
  unsigned number(OracleLocalRecipe &recipe, uint64_t n) {
    return apply(recipe, {"index.constant", {}, ""}, index, {},
                 {std::to_string(n)})
        .front();
  }
  void require(OracleLocalRecipe &recipe, unsigned condition) {
    apply(recipe, {"control.require", {}, ""}, {}, {condition});
  }
  void same(OracleLocalRecipe &recipe, unsigned left, unsigned right) {
    require(recipe, apply(recipe, {"index.equal", {}, ""}, builder.getI1Type(),
                          {left, right})
                        .front());
  }
  Expected<OracleLocalRecipe> checkShape(pir::OracleKindAttr kind,
                                         DictionaryAttr bounds, bool data,
                                         bool inferred) {
    Types inputs;
    if (data)
      inputs.push_back(kind.getDataType());
    if (!inferred)
      inputs.push_back(index);
    auto recipe = local(inputs, index);
    unsigned rows = data && !inferred ? 1 : 0;
    if (data) {
      auto binding = length(kind);
      if (!binding)
        return binding.takeError();
      auto actual = apply(recipe, *binding, index, {0}).front();
      if (inferred)
        rows = actual;
      else
        same(recipe, rows, actual);
    }
    auto dimensions = kind.getShapeDimensions();
    if (dimensions.size() != 1 || dimensions[0].name != "rows")
      return refuse();
    if (dimensions[0].extent)
      same(recipe, rows, number(recipe, *dimensions[0].extent));
    else {
      auto bound = bounds.getAs<IntegerAttr>("rows");
      if (!bound)
        return refuse();
      unsigned maximum = number(recipe, bound.getValue().getZExtValue());
      auto tooLarge = apply(recipe, {"index.less", {}, ""}, builder.getI1Type(),
                            {maximum, rows})
                          .front();
      auto no =
          apply(recipe, {"bool.not", {}, ""}, builder.getI1Type(), {tooLarge})
              .front();
      require(recipe, no);
    }
    recipe.results = {rows};
    return recipe;
  }
  Operation *sourceOperation(ArrayRef<unsigned> path) {
    Block *body = &program.getBody().front();
    Operation *op = nullptr;
    for (auto [i, ordinal] : enumerate(path)) {
      if (ordinal >= body->getOperations().size())
        return nullptr;
      op = &*std::next(body->begin(), ordinal);
      if (i + 1 != path.size()) {
        auto repeat = dyn_cast<pir::RepeatOp>(op);
        if (!repeat)
          return nullptr;
        body = &repeat.getBody().front();
      }
    }
    return op;
  }
  std::optional<unsigned> inputAnchor(Value anchor) {
    while (auto restricted = anchor.getDefiningOp<pir::RestrictRolesOp>())
      anchor = restricted.getInput();
    auto argument = dyn_cast<BlockArgument>(anchor);
    if (!argument || argument.getOwner() != &program.getBody().front())
      return {};
    return argument.getArgNumber();
  }
  Error construct(OracleCommonBlock &block, Operation &op,
                  ArrayRef<unsigned> path, unsigned ordinal) {
    const auto &construction = requirements.storage.constructors[ordinal];
    auto kind = construction.kind;
    auto reference = oracleReferenceType(kind);
    if (!reference)
      return reference.takeError();
    IDs references;
    std::vector<std::string> roles;
    std::map<std::string, unsigned> delivered;
    if (auto send = dyn_cast<pir::OracleSendOp>(op)) {
      auto data = value(send.getData());
      if (!data)
        return data.takeError();
      delivered[construction.holder] = *data;
    }
    unsigned incoming = 0;
    IDs committed;
    if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
      auto data = value(input.getData()), anchor = value(input.getAnchor());
      if (!data)
        return data.takeError();
      if (!anchor)
        return anchor.takeError();
      delivered[construction.holder] = *data;
      incoming = *anchor;
    }
    for (auto [roleIndex, role] : enumerate(construction.roles)) {
      auto *body = controller(role.role, kind);
      if (!body)
        return error("oracle-common-helper");
      auto captures = stores(*body);
      if (!captures)
        return captures.takeError();
      auto found = find_if(body->constructors, [&](const auto &item) {
        return item.source == ordinal;
      });
      if (found == body->constructors.end())
        return error("oracle-common-helper");
      unsigned row;
      IDs payload, children;
      if (auto virtualOracle = dyn_cast<pir::OracleVirtualOp>(op)) {
        auto declaration =
            cast<pir::OracleDefinitionOp>(SymbolTable::lookupSymbolIn(
                cast<pir::ProtocolModuleOp>(source.getBody()->front()),
                virtualOracle.getCallee()));
        auto actual = inputs(virtualOracle.getInputs());
        if (!actual)
          return actual.takeError();
        payload = *actual;
        children.assign(actual->begin(),
                        actual->begin() + declaration.getNumSources());
        unsigned raw;
        auto dimension = kind.getShapeDimensions()[0];
        if (dimension.extent) {
          auto n = constant(block, *dimension.extent);
          if (!n)
            return n.takeError();
          raw = *n;
        } else {
          auto argument =
              declaration.getShapeArguments().getAs<IntegerAttr>("rows");
          if (!argument)
            return refuse();
          raw = (*actual)[argument.getValue().getZExtValue()];
        }
        auto recipe =
            checkShape(kind, declaration.getShapeBounds(), false, false);
        if (!recipe)
          return recipe.takeError();
        auto checked = call(block, *recipe, role.role, {raw},
                            site(path, "shape", role.role));
        if (!checked)
          return checked.takeError();
        row = checked->front();
        result.locals.push_back(std::move(*recipe));
      } else {
        bool authenticated = !construction.scheme.empty();
        bool holder = role.role == construction.holder;
        DictionaryAttr bounds;
        bool inferred =
            isa<pir::OracleInputOp>(op) && (!authenticated || holder);
        IDs arguments;
        if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
          bounds = input.getShapeBounds();
          if (!holder) {
            delivered[role.role] = incoming;
            if (authenticated) {
              auto dimension = kind.getShapeDimensions()[0];
              if (dimension.extent) {
                auto count = constant(block, *dimension.extent);
                if (!count)
                  return count.takeError();
                arguments.push_back(*count);
              } else {
                auto anchor = inputAnchor(input.getAnchor());
                if (!anchor || !inputRows.count(*anchor))
                  return error("oracle-common-interface");
                arguments.push_back(inputRows.at(*anchor));
              }
            }
          }
        } else {
          auto send = cast<pir::OracleSendOp>(op);
          bounds = send.getShapeBounds();
          if (!holder) {
            if (authenticated && committed.size() != 2)
              return error("oracle-common-helper");
            auto commit = merkle[ordinal].commit;
            Type deliveryType =
                authenticated
                    ? cast<exec::OutcomeType>(commit.getResultTypes()[0])
                          .getPayload()[0]
                    : kind.getDataType();
            auto exchange = make(
                block, "protocol.exchange", deliveryType,
                {authenticated ? committed[0] : delivered[construction.holder]},
                attrs({text("sender", construction.holder),
                       text("receiver", role.role),
                       text("site", site(path, "deliver", role.role))}));
            if (!exchange)
              return exchange.takeError();
            delivered[role.role] = exchange->front();
          }
          auto dimension = value(send.getShapeOperand("rows"));
          if (!dimension)
            return dimension.takeError();
          arguments.push_back(*dimension);
        }
        bool data = !authenticated || holder;
        if (data)
          arguments.insert(arguments.begin(), delivered[role.role]);
        auto recipe = checkShape(kind, bounds, data, inferred);
        if (!recipe)
          return recipe.takeError();
        auto checked = call(block, *recipe, role.role, arguments,
                            site(path, "shape", role.role));
        if (!checked)
          return checked.takeError();
        row = checked->front();
        result.locals.push_back(std::move(*recipe));
        payload = {delivered[role.role]};
        if (authenticated) {
          if (holder) {
            auto output = call(block, merkle[ordinal].commit, role.role,
                               {delivered[role.role], row},
                               site(path, "commit", role.role));
            if (!output)
              return output.takeError();
            committed = *output;
            payload.push_back(committed[1]);
          } else {
            auto zero = constant(block, 0);
            if (!zero)
              return zero.takeError();
            auto admitted = call(block, merkle[ordinal].position, role.role,
                                 {row, *zero}, site(path, "layout", role.role));
            if (!admitted)
              return admitted.takeError();
          }
        }
      }
      append_range(children, *captures);
      auto count = call(
          block, body->constructionCounts[found - body->constructors.begin()],
          role.role, children, site(path, "count", role.role));
      if (!count)
        return count.takeError();
      IDs allocation{store.at({ordinal, unsigned(roleIndex)})};
      append_range(allocation, coordinates);
      allocation.push_back(row);
      allocation.push_back(count->front());
      append_range(allocation, payload);
      auto allocated = call(block, allocators[ordinal][roleIndex], role.role,
                            allocation, site(path, "allocate", role.role));
      if (!allocated)
        return allocated.takeError();
      references.push_back((*allocated)[0]);
      store[{ordinal, unsigned(roleIndex)}] = (*allocated)[1];
      roles.push_back(role.role);
    }
    auto joined = assemble(block, *reference, references, roles);
    if (!joined)
      return joined.takeError();
    values[op.getResult(0)] = *joined;
    return Error::success();
  }
  Error sequence(OracleCommonBlock &block, Operation &op,
                 ArrayRef<unsigned> path) {
    auto actual = inputs(op.getOperands());
    if (!actual)
      return actual.takeError();
    auto output = converted(op.getResult(0).getType());
    if (!output)
      return output.takeError();
    if (isa<pir::OracleSequenceEmptyOp, pir::OracleSequenceLengthOp>(op)) {
      auto made =
          make(block,
               isa<pir::OracleSequenceEmptyOp>(op) ? "data.sequence_empty"
                                                   : "data.sequence_length",
               *output, *actual);
      if (!made)
        return made.takeError();
      values[op.getResult(0)] = made->front();
      return Error::success();
    }
    auto sequence = cast<pir::OracleSequenceType>(op.getOperand(0).getType());
    auto element = oracleReferenceType(sequence.getKind());
    if (!element)
      return element.takeError();
    auto spelling = encodeBoundType(*element, false);
    if (!spelling)
      return spelling.takeError();
    Types arguments;
    for (auto type : op.getOperandTypes()) {
      auto convertedType = converted(type);
      if (!convertedType)
        return convertedType.takeError();
      arguments.push_back(*convertedType);
    }
    auto recipe = local(arguments, *output);
    auto length = apply(recipe, {"sequence.length", {spelling->spelling()}, ""},
                        index, {0})
                      .front();
    bool append = isa<pir::OracleSequenceAppendOp>(op);
    unsigned left = append ? length : 1;
    unsigned right = append ? number(recipe, sequence.getMaximum()) : length;
    require(recipe, apply(recipe, {"index.less", {}, ""}, builder.getI1Type(),
                          {left, right})
                        .front());
    recipe.results = apply(recipe,
                           {append ? "sequence.append" : "sequence.at",
                            {spelling->spelling()},
                            ""},
                           *output, {0, 1});
    auto selected = op.getAttrOfType<ArrayAttr>("roles");
    IDs components;
    std::vector<std::string> roles;
    for (auto role : selected) {
      auto name = cast<StringAttr>(role).getValue();
      auto component =
          call(block, recipe, name, *actual, site(path, "sequence", name));
      if (!component)
        return component.takeError();
      components.push_back(component->front());
      roles.push_back(name.str());
    }
    result.locals.push_back(std::move(recipe));
    auto joined = assemble(block, *output, components, roles);
    if (!joined)
      return joined.takeError();
    values[op.getResult(0)] = *joined;
    return Error::success();
  }
  // The admitted common language gives each handle an exact role family.
  // Loop carriers declare their family; captures retain the actual operand's.
  // This is availability, never an inference from possible anchor origins.
  Expected<std::vector<std::string>> handleRoles(Value value,
                                                 unsigned depth = 64) {
    if (!depth || !allowance)
      return error("oracle-common-limit");
    --allowance;
    ArrayAttr selected;
    std::string holder;
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto *parent = argument.getOwner()->getParentOp();
      if (auto function = dyn_cast<pir::MathematicalOp>(parent))
        selected =
            cast<ArrayAttr>(function.getInputRoles()[argument.getArgNumber()]);
      else if (auto repeat = dyn_cast<pir::RepeatOp>(parent)) {
        unsigned index = argument.getArgNumber();
        if (index > 0 && index <= unsigned(repeat.getCarried()))
          selected = cast<ArrayAttr>(repeat.getCarriedRoles()[index - 1]);
        else if (index > unsigned(repeat.getCarried()))
          return handleRoles(repeat.getInputs()[index], depth - 1);
      }
    } else if (auto repeat = value.getDefiningOp<pir::RepeatOp>())
      selected = cast<ArrayAttr>(
          repeat.getCarriedRoles()[cast<OpResult>(value).getResultNumber()]);
    else if (auto restrict = value.getDefiningOp<pir::RestrictRolesOp>())
      selected = restrict.getRoles();
    else if (auto forget = value.getDefiningOp<pir::OracleForgetShapeOp>())
      return handleRoles(forget.getInput(), depth - 1);
    else if (auto components = value.getDefiningOp<pir::OracleComponentsOp>())
      selected = components.getReceivers();
    else if (auto at = value.getDefiningOp<pir::OracleSequenceAtOp>())
      selected = at.getRoles();
    else if (auto send = value.getDefiningOp<pir::OracleSendOp>()) {
      selected = send.getReceivers();
      holder = send.getSender().str();
    } else if (auto input = value.getDefiningOp<pir::OracleInputOp>()) {
      selected = input.getReceivers();
      holder = input.getHolder().str();
    } else if (auto constructed = value.getDefiningOp<pir::OracleVirtualOp>()) {
      selected = constructed.getReceivers();
      holder = constructed.getHolder().str();
    }
    if (!selected)
      return error("oracle-common-interface");
    std::vector<std::string> roles;
    for (auto attribute : program.getRoles()) {
      auto role = cast<StringAttr>(attribute);
      if (role.getValue() == holder || is_contained(selected, attribute))
        roles.push_back(role.getValue().str());
    }
    return roles;
  }
  Error repeat(OracleCommonBlock &block, pir::RepeatOp repeat,
               std::vector<unsigned> path, unsigned depth) {
    for (Value input : repeat.getInputs())
      if (auto e = demand(block, input, path))
        return e;
    auto arguments = inputs(repeat.getInputs());
    if (!arguments)
      return arguments.takeError();
    auto previousValues = values;
    auto previousViews = dataViews;
    auto previousStore = store;
    auto previousCoordinates = coordinates;
    std::vector<std::pair<unsigned, unsigned>> carriedStores;
    auto active = [&](StringRef role) {
      return is_contained(repeat.getRoles(), builder.getStringAttr(role));
    };
    IDs oldSeeds(arguments->begin() + 1,
                 arguments->begin() + 1 + repeat.getCarried());
    IDs captures(arguments->begin() + 1 + repeat.getCarried(),
                 arguments->end());
    Types seedTypes, captureTypes;
    for (Type type : repeat.getInputs()
                         .drop_front(1)
                         .take_front(repeat.getCarried())
                         .getTypes()) {
      auto result = converted(type);
      if (!result)
        return result.takeError();
      seedTypes.push_back(*result);
    }
    for (Type type :
         repeat.getInputs().drop_front(1 + repeat.getCarried()).getTypes()) {
      auto result = converted(type);
      if (!result)
        return result.takeError();
      captureTypes.push_back(*result);
    }
    SmallVector<Attribute> carriedRoles(repeat.getCarriedRoles().begin(),
                                        repeat.getCarriedRoles().end());
    for (const auto &[key, value] : previousStore) {
      const auto &owner =
          requirements.storage.constructors[key.first].roles[key.second];
      if (!active(owner.role))
        continue;
      carriedStores.push_back(key);
      oldSeeds.push_back(value);
      seedTypes.push_back(owner.sequence);
      carriedRoles.push_back(builder.getStrArrayAttr({owner.role}));
    }
    append_range(captures, coordinates);
    captureTypes.insert(captureTypes.end(), coordinates.size(), index);
    auto region = std::make_shared<OracleCommonBlock>();
    region->types = {index};
    append_range(region->types, seedTypes);
    append_range(region->types, captureTypes);
    for ([[maybe_unused]] Type type : region->types)
      region->arguments.push_back(id());
    auto &original = repeat.getBody().front();
    values[original.getArgument(0)] = region->arguments[0];
    for (unsigned i = 0; i < unsigned(repeat.getCarried()); ++i)
      values[original.getArgument(1 + i)] = region->arguments[1 + i];
    for (unsigned i = 0;
         i < original.getNumArguments() - 1 - repeat.getCarried(); ++i)
      values[original.getArgument(1 + repeat.getCarried() + i)] =
          region->arguments[1 + seedTypes.size() + i];
    store.clear();
    for (auto [i, key] : enumerate(carriedStores))
      store[key] = region->arguments[1 + repeat.getCarried() + i];
    coordinates.clear();
    auto coordinateStart =
        region->arguments.size() - previousCoordinates.size();
    for (unsigned i = 0; i < previousCoordinates.size(); ++i)
      coordinates.push_back(region->arguments[coordinateStart + i]);
    coordinates.push_back(region->arguments[0]);
    if (auto e = visit(*region, original, path, depth - 1, carriedStores))
      return e;
    IDs operands{arguments->front()};
    append_range(operands, oldSeeds);
    append_range(operands, captures);
    NamedAttrList attributes(repeat->getAttrs());
    attributes.set("carried", builder.getI64IntegerAttr(seedTypes.size()));
    attributes.set("carried_roles", builder.getArrayAttr(carriedRoles));
    auto outputs = make(block, "protocol.repeat", seedTypes, operands,
                        attributes.getDictionary(builder.getContext()), region);
    if (!outputs)
      return outputs.takeError();
    values = std::move(previousValues);
    dataViews = std::move(previousViews);
    store = std::move(previousStore);
    coordinates = std::move(previousCoordinates);
    for (auto [i, output] : enumerate(repeat.getOutputs()))
      values[output] = (*outputs)[i];
    for (auto [i, key] : enumerate(carriedStores))
      store[key] = (*outputs)[repeat.getCarried() + i];
    return Error::success();
  }
  // The counted common language has static peers. This profile has one
  // remote base constructor, possibly many instances and virtual ancestors.
  // It never broadcasts a dynamically selected request. General multi-holder
  // selection needs a checked knowledge-of-choice communication rule.
  Expected<IDs> remoteQuery(OracleCommonBlock &block, pir::OracleQueryOp query,
                            const OracleQueryController &receiver,
                            ArrayRef<unsigned> arguments,
                            ArrayRef<unsigned> path) {
    using C = OracleQueryController;
    const OracleQueryControllerConstructor *base = nullptr;
    bool hasVirtual = false;
    for (const auto &item : receiver.constructors) {
      const auto &anchor = requirements.storage.constructors[item.source];
      if (anchor.constructor == OracleAnchorConstructor::Kind::Virtual) {
        hasVirtual = true;
        continue;
      }
      if (base || anchor.scheme.empty() || anchor.holder == receiver.role)
        return error("oracle-common-communication-profile");
      base = &item;
    }
    if (!base)
      return error("oracle-common-communication-profile");
    const auto &anchor = requirements.storage.constructors[base->source];
    auto *holder =
        controller(anchor.holder, query.getHandle().getType().getKind());
    if (!holder)
      return error("oracle-common-helper");
    auto holderBase = find_if(holder->constructors, [&](const auto &item) {
      return item.source == base->source;
    });
    if (holderBase == holder->constructors.end())
      return error("oracle-common-helper");
    auto receiverStores = stores(receiver);
    if (!receiverStores)
      return receiverStores.takeError();
    auto holderStore = store.find({base->source, holderBase->role});
    if (holderStore == store.end())
      return error("oracle-common-communication-profile");
    auto initial = call(block, receiver.initialize, receiver.role, arguments,
                        site(path, "query_initialize", receiver.role));
    if (!initial)
      return initial.takeError();
    IDs advanceInputs = *initial;
    append_range(advanceInputs, *receiverStores);
    // The first domain/position check precedes any opening communication.
    auto state = call(block, receiver.advance, receiver.role, advanceInputs,
                      site(path, "query_advance", receiver.role));
    if (!state)
      return state.takeError();
    Expected<unsigned> count = constant(block, 1);
    if (!count)
      return count.takeError();
    if (hasVirtual) {
      // Each participant computes its own component from an already available
      // handle. Sending a future request count would disclose work that a
      // failed authentication or later domain check may never reach.
      auto roles = handleRoles(query.getHandle());
      if (!roles)
        return roles.takeError();
      if (!is_contained(*roles, anchor.holder))
        return error("oracle-common-communication-profile");
      IDs counts;
      std::vector<std::string> owners{receiver.role, anchor.holder};
      for (const auto *body : {&receiver, holder}) {
        auto captures = stores(*body);
        if (!captures)
          return captures.takeError();
        IDs inputs{arguments[0]};
        append_range(inputs, *captures);
        auto counted = call(block, body->leafCounts[0], body->role, inputs,
                            site(path, "query_count", body->role));
        if (!counted)
          return counted.takeError();
        counts.push_back(counted->front());
      }
      count = assemble(block, index, counts, owners);
      if (!count)
        return count.takeError();
    }
    auto request = local(receiver.state, TypeRange{index, index});
    same(request, C::Phase, number(request, C::Request));
    same(request, C::Constructor, number(request, base->source));
    same(request, C::Kind, number(request, base->kind));
    request.results = {C::Instance, C::Position};
    auto region = std::make_shared<OracleCommonBlock>();
    region->types = {index};
    append_range(region->types, receiver.state);
    append_range(region->types, receiver.stores);
    region->types.push_back(anchor.roles[holderBase->role].sequence);
    for ([[maybe_unused]] auto type : region->types)
      region->arguments.push_back(id());
    auto stateStart = region->arguments.begin() + 1;
    IDs suspended(stateStart, stateStart + receiver.state.size());
    IDs captures(stateStart + receiver.state.size(),
                 region->arguments.end() - 1);
    auto requestValues = call(*region, request, receiver.role, suspended,
                              site(path, "opening_request", receiver.role));
    if (!requestValues)
      return requestValues.takeError();
    result.locals.push_back(std::move(request));
    auto exchange = [&](unsigned input, Type type, StringRef sender,
                        StringRef recipient,
                        StringRef purpose) -> Expected<unsigned> {
      auto output =
          make(*region, "protocol.exchange", type, {input},
               attrs({text("sender", sender), text("receiver", recipient),
                      text("site", site(path, purpose, recipient))}));
      if (!output)
        return output.takeError();
      return output->front();
    };
    auto instance = exchange((*requestValues)[0], index, receiver.role,
                             anchor.holder, "opening_instance");
    if (!instance)
      return instance.takeError();
    auto position = exchange((*requestValues)[1], index, receiver.role,
                             anchor.holder, "opening_position");
    if (!position)
      return position.takeError();
    auto tag = constant(*region, base->source);
    if (!tag)
      return tag.takeError();
    auto reference = oracleReferenceType(anchor.kind);
    if (!reference)
      return reference.takeError();
    auto heldReference =
        make(*region, "data.make", *reference, {*tag, *instance},
             attrs({text("alternative", "Record")}));
    if (!heldReference)
      return heldReference.takeError();
    auto held = call(*region, holderBase->lookup, anchor.holder,
                     {heldReference->front(), region->arguments.back()},
                     site(path, "opening_anchor", anchor.holder));
    if (!held)
      return held.takeError();
    auto field = [&](unsigned role, StringRef name) -> unsigned {
      const auto &fields = anchor.roles[role].fields;
      return find_if(fields,
                     [&](const auto &item) { return item.name == name; }) -
             fields.begin();
    };
    auto opening = field(holderBase->role, "opening_state");
    auto holderRows = field(holderBase->role, "shape.rows");
    auto root = field(base->role, "root");
    auto receiverRows = field(base->role, "shape.rows");
    if (opening >= held->size() || holderRows >= held->size() ||
        root >= anchor.roles[base->role].fields.size() ||
        receiverRows >= anchor.roles[base->role].fields.size())
      return error("oracle-common-helper");
    auto functions = merkle[base->source];
    auto opened = call(*region, functions.open, anchor.holder,
                       {(*held)[opening], (*held)[holderRows], *position},
                       site(path, "opening", anchor.holder));
    if (!opened)
      return opened.takeError();
    auto payload = cast<exec::OutcomeType>(functions.open.getResultTypes()[0])
                       .getPayload();
    auto row = exchange((*opened)[0], payload[0], anchor.holder, receiver.role,
                        "opening_row");
    if (!row)
      return row.takeError();
    auto proof = exchange((*opened)[1], payload[1], anchor.holder,
                          receiver.role, "opening_proof");
    if (!proof)
      return proof.takeError();
    auto receiverSlot = base - receiver.constructors.data();
    auto receivedReference =
        make(*region, "data.make", *reference,
             {suspended[C::Constructor], suspended[C::Instance]},
             attrs({text("alternative", "Record")}));
    if (!receivedReference)
      return receivedReference.takeError();
    auto received = call(*region, base->lookup, receiver.role,
                         {receivedReference->front(), captures[receiverSlot]},
                         site(path, "authenticated_anchor", receiver.role));
    if (!received)
      return received.takeError();
    auto answer = call(*region, functions.authenticate, receiver.role,
                       {(*received)[root], (*received)[receiverRows],
                        suspended[C::Position], *row, *proof},
                       site(path, "authenticate", receiver.role));
    if (!answer)
      return answer.takeError();
    IDs resumedInputs = suspended;
    append_range(resumedInputs, ArrayRef<unsigned>(suspended).take_front(5));
    resumedInputs.push_back(answer->front());
    auto resumed =
        call(*region, receiver.resume[base->kind], receiver.role, resumedInputs,
             site(path, "query_resume", receiver.role));
    if (!resumed)
      return resumed.takeError();
    append_range(*resumed, captures);
    // Including after the last opening: trailing zero-query virtual children
    // still run their domain checks before the outer answer can be returned.
    auto advanced = call(*region, receiver.advance, receiver.role, *resumed,
                         site(path, "query_continue", receiver.role));
    if (!advanced)
      return advanced.takeError();
    auto yield = make(*region, "protocol.yield", {}, *advanced);
    if (!yield)
      return yield.takeError();
    IDs loopInputs{*count};
    append_range(loopInputs, *state);
    append_range(loopInputs, *receiverStores);
    loopInputs.push_back(holderStore->second);
    SmallVector<Attribute> carried(receiver.state.size(),
                                   builder.getStrArrayAttr({receiver.role}));
    auto final = make(
        block, "protocol.repeat", receiver.state, loopInputs,
        attrs(
            {text("site", site(path, "query_requests", receiver.role)),
             builder.getNamedAttr(
                 "carried", builder.getI64IntegerAttr(receiver.state.size())),
             builder.getNamedAttr("maximum", builder.getI64IntegerAttr(
                                                 receiver.capacity.leaves)),
             builder.getNamedAttr("roles", builder.getStrArrayAttr(
                                               {anchor.holder, receiver.role})),
             builder.getNamedAttr("carried_roles",
                                  builder.getArrayAttr(carried))}),
        region);
    if (!final)
      return final.takeError();
    return call(block, receiver.finish, receiver.role, *final,
                site(path, "query_finish", receiver.role));
  }
  Error visit(OracleCommonBlock &block, Block &original,
              std::vector<unsigned> prefix, unsigned depth,
              ArrayRef<std::pair<unsigned, unsigned>> yieldedStores = {}) {
    if (!depth)
      return error("oracle-common-limit");
    for (auto [ordinal, op] : enumerate(original)) {
      auto path = prefix;
      path.push_back(ordinal);
      // Statements select logical claims, not executable effects. The frozen
      // original and checked record retain their full binding. A candidate
      // alone cannot publish the original claim after representation changes.
      if (isa<pir::StatementOp>(op))
        continue;
      if (auto repetition = dyn_cast<pir::RepeatOp>(op)) {
        if (auto e = repeat(block, repetition, path, depth))
          return e;
        continue;
      }
      if (auto components = dyn_cast<pir::OracleComponentsOp>(op)) {
        auto anchor = value(components.getHandle());
        if (!anchor)
          return anchor.takeError();
        auto type = converted(components.getAnchor().getType());
        if (!type)
          return type.takeError();
        auto receiver = make(
            block, "protocol.restrict_roles", *type, {*anchor},
            attrs({builder.getNamedAttr("roles", components.getReceivers())}));
        if (!receiver)
          return receiver.takeError();
        values[components.getAnchor()] = receiver->front();
        dataViews[components.getData()] = {
            *anchor, components.getHolder().str(),
            components.getHandle().getType().getKind()};
        continue;
      }
      if (auto restrict = dyn_cast<pir::RestrictRolesOp>(op)) {
        if (auto found = dataViews.find(restrict.getInput());
            found != dataViews.end()) {
          // Insertion can grow the map and invalidate the input iterator.
          auto view = found->second;
          dataViews[restrict.getOutput()] = std::move(view);
          if (auto data = values.find(restrict.getInput());
              data != values.end())
            values[restrict.getOutput()] = data->second;
          continue;
        }
      }
      if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
        if (none_of(requirements.storage.constructors,
                    [&](const auto &item) { return item.path == path; })) {
          Value receiver = input.getAnchor();
          while (auto view = receiver.getDefiningOp<pir::RestrictRolesOp>()) {
            if (!allowance)
              return error("oracle-common-limit");
            --allowance;
            receiver = view.getInput();
          }
          auto components = receiver.getDefiningOp<pir::OracleComponentsOp>();
          if (!components)
            return error("oracle-common-interface");
          // Admission already checked the exact data/receiver pair. Retain the
          // actual view's dynamic reference; possible origins are insufficient.
          auto anchor = value(components.getHandle());
          auto type = converted(input.getHandle().getType());
          if (!anchor)
            return anchor.takeError();
          if (!type)
            return type.takeError();
          SmallVector<Attribute> roles{input.getHolderAttr()};
          append_range(roles, input.getReceivers());
          auto rebound =
              make(block, "protocol.restrict_roles", *type, {*anchor},
                   attrs({builder.getNamedAttr("roles",
                                               builder.getArrayAttr(roles))}));
          if (!rebound)
            return rebound.takeError();
          values[input.getHandle()] = rebound->front();
          continue;
        }
      }
      for (Value input : op.getOperands())
        if (auto e = demand(block, input, path))
          return e;
      if (isa<pir::OracleInputOp, pir::OracleSendOp, pir::OracleVirtualOp>(
              op)) {
        auto found =
            find_if(requirements.storage.constructors,
                    [&](const auto &item) { return item.path == path; });
        if (found == requirements.storage.constructors.end())
          return error("oracle-common-interface");
        if (auto e =
                construct(block, op, path,
                          found - requirements.storage.constructors.begin()))
          return e;
        continue;
      }
      if (auto query = dyn_cast<pir::OracleQueryOp>(op)) {
        auto *body = controller(*query.getOwner(),
                                query.getHandle().getType().getKind());
        if (!body)
          return error("oracle-common-helper");
        auto arguments = inputs(query->getOperands());
        auto captures = stores(*body);
        if (!arguments)
          return arguments.takeError();
        if (!captures)
          return captures.takeError();
        Expected<IDs> output = [&]() -> Expected<IDs> {
          if (!body->evaluate)
            return remoteQuery(block, query, *body, *arguments, path);
          append_range(*arguments, *captures);
          return call(block, body->evaluate, *query.getOwner(), *arguments,
                      site(path, "query", *query.getOwner()));
        }();
        if (!output)
          return output.takeError();
        values[query.getAnswer()] = output->front();
        continue;
      }
      if (auto contents = dyn_cast<pir::OracleContentsOp>(op)) {
        auto *body = controller(contents.getOwner(),
                                contents.getHandle().getType().getKind(),
                                OracleControllerAccess::Holder);
        if (!body || !body->contents)
          return error("oracle-common-helper");
        auto arguments = inputs(contents->getOperands());
        auto captures = stores(*body);
        if (!arguments)
          return arguments.takeError();
        if (!captures)
          return captures.takeError();
        append_range(*arguments, *captures);
        auto output =
            call(block, body->contents, contents.getOwner(), *arguments,
                 site(path, "contents", contents.getOwner()));
        if (!output)
          return output.takeError();
        values[contents.getData()] = output->front();
        continue;
      }
      if (auto shape = dyn_cast<pir::OracleShapeOp>(op)) {
        if (shape.getDimension() != "rows")
          return error("oracle-common-interface");
        auto roles = handleRoles(shape.getHandle());
        if (!roles)
          return roles.takeError();
        IDs components;
        for (const auto &role : *roles) {
          auto *body = controller(role, shape.getHandle().getType().getKind());
          if (!body || body->rowCounts.empty())
            return error("oracle-common-helper");
          auto arguments = inputs(shape->getOperands());
          auto captures = stores(*body);
          if (!arguments)
            return arguments.takeError();
          if (!captures)
            return captures.takeError();
          append_range(*arguments, *captures);
          auto output = call(block, body->rowCounts[0], role, *arguments,
                             site(path, "shape_view", role));
          if (!output)
            return output.takeError();
          components.push_back(output->front());
        }
        auto output = assemble(block, index, components, *roles);
        if (!output)
          return output.takeError();
        values[shape.getExtent()] = *output;
        continue;
      }
      if (auto forget = dyn_cast<pir::OracleForgetShapeOp>(op)) {
        auto original = value(forget.getInput());
        if (!original)
          return original.takeError();
        values[forget.getOutput()] = *original;
        continue;
      }
      if (isa<pir::OracleSequenceEmptyOp, pir::OracleSequenceLengthOp,
              pir::OracleSequenceAppendOp, pir::OracleSequenceAtOp>(op)) {
        if (auto e = sequence(block, op, path))
          return e;
        continue;
      }
      if (op.getName().getStringRef().starts_with("protocol.oracle_"))
        return error("oracle-common-interface");
      if (op.getNumRegions() || isa<pir::ApplyOp>(op))
        return refuse();
      if (any_of(op.getOperandTypes(), logical) &&
          !isa<pir::RestrictRolesOp, pir::ProtocolYieldOp,
               pir::MathematicalReturnOp>(op))
        return error("oracle-common-interface");
      auto arguments = inputs(op.getOperands());
      if (!arguments)
        return arguments.takeError();
      if (isa<pir::ProtocolYieldOp>(op))
        for (const auto &key : yieldedStores)
          arguments->push_back(store.at(key));
      if (isa<pir::MathematicalReturnOp>(op))
        for (const auto &support : result.resultStores)
          arguments->push_back(store.at({support.constructor, support.role}));
      Types outputs;
      for (auto type : op.getResultTypes()) {
        auto actual = converted(type);
        if (!actual)
          return actual.takeError();
        outputs.push_back(*actual);
      }
      auto output = make(block, op.getName().getStringRef(), outputs,
                         *arguments, op.getAttrDictionary());
      if (!output)
        return output.takeError();
      for (auto [original, mapped] : zip(op.getResults(), *output))
        values[original] = mapped;
    }
    return Error::success();
  }
  Expected<OracleCommonPlan> run() {
    Types inputs;
    auto &original = program.getBody().front();
    std::map<unsigned, unsigned> selectedInputs;
    for (auto [ordinal, constructor] :
         enumerate(requirements.storage.constructors)) {
      if (constructor.constructor != OracleAnchorConstructor::Kind::Input)
        continue;
      auto input = dyn_cast_or_null<pir::OracleInputOp>(
          sourceOperation(constructor.path));
      if (!input)
        return error("oracle-common-interface");
      auto anchor = inputAnchor(input.getAnchor());
      if (!anchor)
        return error("oracle-common-interface");
      // Protocol admission owns the unique binding of each raw entry anchor.
      selectedInputs.emplace(*anchor, ordinal);
    }
    for (auto [ordinal, argument] : enumerate(original.getArguments())) {
      Type type = argument.getType();
      if (auto handle = dyn_cast<pir::OracleHandleType>(type)) {
        auto selected = selectedInputs.find(ordinal);
        if (selected == selectedInputs.end())
          return error("oracle-common-interface");
        auto &constructor = requirements.storage.constructors[selected->second];
        if (constructor.scheme.empty())
          type = handle.getKind().getDataType();
        else {
          auto receiver = find_if(constructor.roles, [&](const auto &role) {
            return role.role != constructor.holder;
          });
          if (receiver == constructor.roles.end())
            return error("oracle-common-interface");
          const auto &fields = receiver->fields;
          auto field = find_if(
              fields, [](const auto &field) { return field.name == "root"; });
          if (field == fields.end())
            return error("oracle-common-interface");
          type = field->type;
        }
      } else if (logical(type))
        return error("oracle-common-interface");
      auto mapped = id();
      values[argument] = mapped;
      result.body.arguments.push_back(mapped);
      result.body.types.push_back(type);
      inputs.push_back(type);
    }
    SmallVector<Attribute> inputRoles(program.getInputRoles().begin(),
                                      program.getInputRoles().end());
    for (const auto &[anchor, ordinal] : selectedInputs) {
      const auto &constructor = requirements.storage.constructors[ordinal];
      if (constructor.scheme.empty() ||
          constructor.kind.getShapeDimensions()[0].extent)
        continue;
      result.inputShapes.push_back({anchor, unsigned(inputs.size())});
      auto mapped = id();
      inputRows[anchor] = mapped;
      result.body.arguments.push_back(mapped);
      result.body.types.push_back(index);
      inputs.push_back(index);
      inputRoles.push_back(program.getInputRoles()[anchor]);
    }
    Types outputs;
    for (Type type : program.getFunctionType().getResults()) {
      // A logical sequence is not an admitted paired result port.
      if (isa<pir::OracleSequenceType>(type))
        return error("oracle-common-interface");
      auto output = converted(type);
      if (!output)
        return output.takeError();
      outputs.push_back(*output);
    }
    SmallVector<Attribute> outputRoles(program.getOutputRoles().begin(),
                                       program.getOutputRoles().end());
    // Retain one complete immutable constructor environment per receiver role
    // with an escaping reference. This is a closed-unit result representation,
    // not permission to import arbitrary graphs at separately compiled roots.
    for (Attribute role : program.getRoles()) {
      bool needed = false;
      for (auto [type, roles] : zip(program.getFunctionType().getResults(),
                                    program.getOutputRoles()))
        needed |= isa<pir::OracleHandleType>(type) &&
                  is_contained(cast<ArrayAttr>(roles), role);
      if (!needed)
        continue;
      for (auto [constructor, item] :
           enumerate(requirements.storage.constructors))
        for (auto [index, storage] : enumerate(item.roles))
          if (storage.role == cast<StringAttr>(role).getValue()) {
            result.resultStores.push_back({unsigned(constructor),
                                           unsigned(index),
                                           unsigned(outputs.size())});
            outputs.push_back(storage.sequence);
            outputRoles.push_back(builder.getArrayAttr({role}));
          }
    }
    for (auto [index, type] : enumerate(program.getFunctionType().getResults()))
      if (isa<pir::OracleHandleType>(type))
        for (Attribute role :
             cast<ArrayAttr>(program.getOutputRoles()[index])) {
          OracleResultReference reference{
              unsigned(index), cast<StringAttr>(role).getValue().str(), {}};
          for (const auto &support : result.resultStores)
            if (requirements.storage.constructors[support.constructor]
                    .roles[support.role]
                    .role == reference.role)
              reference.storePorts.push_back(support.port);
          if (reference.storePorts.empty())
            return error("oracle-common-interface");
          result.resultReferences.push_back(std::move(reference));
        }
    NamedAttrList attributes(program->getAttrs());
    // Logical port selectors belong to the original signature. Keeping them
    // here could silently reinterpret an anchor as a native reference or store.
    // Their complete inventory remains in the checked realization edge.
    attributes.erase("contracts");
    attributes.set("function_type",
                   TypeAttr::get(builder.getFunctionType(inputs, outputs)));
    attributes.set("input_roles", builder.getArrayAttr(inputRoles));
    attributes.set("output_roles", builder.getArrayAttr(outputRoles));
    result.attributes = attributes.getDictionary(builder.getContext());
    for (auto [constructor, item] :
         enumerate(requirements.storage.constructors))
      for (auto [role, storage] : enumerate(item.roles)) {
        // Stores may contain private opening state. Their empty value is an
        // owner-local allocation, not a total mathematical sequence shared by
        // all participants. Use the same scoped route for every store layout.
        auto element = encodeBoundType(storage.record, false);
        if (!element)
          return element.takeError();
        auto recipe = local({}, storage.sequence);
        recipe.results =
            apply(recipe, {"sequence.empty", {element->spelling()}, ""},
                  storage.sequence, {});
        auto empty = call(result.body, recipe, storage.role, {},
                          site(item.path, "empty_store", storage.role));
        if (!empty)
          return empty.takeError();
        store[{constructor, role}] = empty->front();
        result.locals.push_back(std::move(recipe));
      }
    if (auto e = visit(result.body, original, {}, 64))
      return std::move(e);
    return std::move(result);
  }
};
} // namespace
Expected<std::vector<std::string>> oracleEntries(ModuleOp source) {
  if (!source || !hasSingleElement(source.getBody()->getOperations()) ||
      failed(verify(source)))
    return refuse();
  auto unit = dyn_cast<pir::ProtocolModuleOp>(source.getBody()->front());
  if (!unit || unit.getProfile() != pir::Profile::Protocol)
    return refuse();
  std::vector<std::string> entries;
  for (auto program : unit.getBody().front().getOps<pir::MathematicalOp>()) {
    bool needed = any_of(program.getFunctionType().getInputs(), logical) ||
                  any_of(program.getFunctionType().getResults(), logical);
    program.walk([&](Operation *op) {
      needed |= op->getName().getStringRef().starts_with("protocol.oracle_") ||
                any_of(op->getOperandTypes(), logical) ||
                any_of(op->getResultTypes(), logical);
    });
    if (needed)
      entries.push_back(program.getSymName().str());
  }
  return entries;
}
Expected<OracleCommonRequirements>
oracleRequirements(ModuleOp source, StringRef entry,
                   ArrayRef<OracleRootSelection> selections) {
  std::map<std::vector<unsigned>, const OracleTableRealization *> selected;
  for (const auto &item : selections)
    if (item.entry == entry &&
        !selected.emplace(item.path, &item.realization).second)
      return error("oracle-realization-selection");
  auto selection = [&](const OracleAnchorConstructor &constructor)
      -> const OracleTableRealization * {
    auto found = selected.find(constructor.path);
    return found == selected.end() ? nullptr : found->second;
  };
  auto storage = planOracleAnchorStorage(
      source, entry,
      [&](const OracleAnchorConstructor &constructor) -> Expected<std::string> {
        auto selected = selection(constructor);
        if (!selected)
          return error("oracle-realization-selection");
        return selected->scheme;
      });
  if (!storage)
    return storage.takeError();
  auto unit = cast<pir::ProtocolModuleOp>(source.getBody()->front());
  auto program = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(unit, entry));
  if (!program)
    return refuse();
  auto capacity = analyzeOracleQueryCapacity(source, entry);
  if (!capacity)
    return capacity.takeError();
  OracleCommonRequirements result{std::move(*storage), {}, {1, 1}, {}};
  for (const auto &constructor : result.storage.constructors) {
    auto choice = selection(constructor);
    result.realizations.push_back(choice ? *choice : OracleTableRealization{});
  }
  for (const auto &map : {&capacity->constructors, &capacity->queries})
    for (const auto &[op, bound] : *map) {
      (void)op;
      result.capacity.leaves = std::max(result.capacity.leaves, bound.leaves);
      result.capacity.nodes = std::max(result.capacity.nodes, bound.nodes);
    }
  auto add = [&](StringRef role, pir::OracleKindAttr kind,
                 OracleControllerAccess access) -> Error {
    if (kind.getIdentity() != "table")
      return refuse();
    auto reference = oracleReferenceType(kind);
    if (!reference)
      return reference.takeError();
    for (const auto &other : result.controllers)
      if (other.role == role && other.access == access &&
          cantFail(oracleReferenceType(other.kind)) == *reference)
        return Error::success();
    if (result.controllers.size() >= 64)
      return error("oracle-common-limit");
    result.controllers.push_back({role.str(), kind, access});
    return Error::success();
  };
  for (const auto &constructor : result.storage.constructors)
    for (const auto &owner : constructor.roles)
      if (auto e = add(owner.role, constructor.kind,
                       OracleControllerAccess::Available))
        return std::move(e);
  Error failure = Error::success();
  // A sequence can have no constructing occurrence. Its element still has a
  // typed use after selection, even though every such execution stops there.
  // Keep a total lowering recipe without manufacturing an anchor or a store.
  program.walk([&](pir::OracleSequenceAtOp op) {
    for (Attribute role : op.getRoles())
      if (!failure)
        failure = add(cast<StringAttr>(role).getValue(),
                      op.getResult().getType().getKind(),
                      OracleControllerAccess::Available);
  });
  program.walk([&](pir::OracleContentsOp op) {
    if (!failure)
      failure = add(op.getOwner(), op.getHandle().getType().getKind(),
                    OracleControllerAccess::Holder);
  });
  unsigned remaining = 100000;
  program.walk([&](pir::OracleComponentsOp op) {
    if (failure)
      return;
    SmallVector<Value> pending{op.getData()};
    llvm::DenseSet<Value> seen;
    bool needed = false;
    while (!pending.empty() && !needed) {
      Value data = pending.pop_back_val();
      if (!seen.insert(data).second)
        continue;
      for (OpOperand &use : data.getUses()) {
        if (!remaining) {
          failure = error("oracle-common-limit");
          return;
        }
        --remaining;
        if (auto restriction = dyn_cast<pir::RestrictRolesOp>(use.getOwner()))
          pending.push_back(restriction.getOutput());
        else if (!isa<pir::OracleInputOp>(use.getOwner()) ||
                 use.getOperandNumber() != 0)
          needed = true;
      }
    }
    if (needed)
      failure = add(op.getHolder(), op.getHandle().getType().getKind(),
                    OracleControllerAccess::Holder);
  });
  if (failure)
    return std::move(failure);
  return result;
}
Expected<OracleCommonPlan>
planOracleCommon(ModuleOp source, StringRef entry,
                 const OracleCommonRequirements &requirements,
                 ArrayRef<OracleCommonController> controllers,
                 ArrayRef<std::vector<func::FuncOp>> allocators,
                 ArrayRef<OracleMerkleFunctions> merkle) {
  if (allocators.size() != requirements.storage.constructors.size() ||
      merkle.size() != allocators.size() ||
      requirements.realizations.size() != allocators.size())
    return error("oracle-common-helper");
  for (auto [i, items] : enumerate(allocators))
    if (items.size() != requirements.storage.constructors[i].roles.size())
      return error("oracle-common-helper");
  auto unit = cast<pir::ProtocolModuleOp>(source.getBody()->front());
  auto program =
      cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, entry));
  return PlanBuilder(source, program, requirements, controllers, allocators,
                     merkle)
      .run();
}
} // namespace zkc::protocol
