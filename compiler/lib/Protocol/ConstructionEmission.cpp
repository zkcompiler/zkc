#include "ConstructionState.h"

using namespace llvm;
namespace zkc::protocol::construction {
std::string Construction::transcriptType() const {
  return "transcript:" + suite;
}

std::string Construction::transcriptBinding(const std::string &operation,
                                            const std::string &payload) {
  std::string cacheKey = operation + "/" + payload;
  auto found = generatedBindings.find(cacheKey);
  if (found != generatedBindings.end())
    return found->second;
  source::OperationBinding binding{{}, fresh(), operation, {suite}, ""};
  if (!payload.empty()) {
    auto ty = parseBoundType(payload, false);
    if (!ty) {
      consumeError(ty.takeError());
      fail("construction-payload-type");
      return {};
    }
    StringRef codec = defaultCodec(*ty);
    if (codec.empty()) {
      fail("construction-payload-codec:" + payload);
      return {};
    }
    if (!ty->identity.empty())
      binding.arguments.push_back(ty->identity);
    binding.arguments.push_back(codec.str());
  }
  auto selected = resolveBinding(binding, false);
  if (!selected) {
    fail("construction-transcript-binding:" + operation + ":" +
         toString(selected.takeError()));
    return {};
  }
  operations.emplace(binding.name, binding);
  outBindings.push_back(binding);
  generatedBindings.emplace(cacheKey, binding.name);
  return binding.name;
}

std::string Construction::seedBinding(const std::string &operation,
                                      const std::string &payload) {
  auto type = parseBoundType(payload, false);
  if (!type) {
    fail("construction-seed-type:" + payload + ":" +
         toString(type.takeError()));
    return {};
  }
  std::string identity = type->kind == "bool"
                             ? associatedIdentity(suite, "ChallengeField").str()
                             : type->identity;
  std::string cacheKey = "seed/" + operation + "/" + identity;
  auto found = generatedBindings.find(cacheKey);
  if (found != generatedBindings.end())
    return found->second;
  source::OperationBinding binding{{}, fresh(), operation, {identity}, ""};
  auto selected = resolveBinding(binding, false);
  if (!selected) {
    fail("construction-seed-binding:" + payload + ":" +
         toString(selected.takeError()));
    return {};
  }
  operations.emplace(binding.name, binding);
  outBindings.push_back(binding);
  generatedBindings.emplace(cacheKey, binding.name);
  return binding.name;
}

bool Construction::omitResult(const std::string &id, size_t k) {
  return id == root && inertEntryResults.count(k);
}

std::string Construction::lookup(const Names &env, const std::string &name) {
  auto p = env.find(name);
  if (p == env.end()) {
    fail("construction-unavailable-emission:" + name);
    return "invalid";
  }
  return p->second;
}

std::string Construction::value(EmissionState &st, const std::string &name,
                                bool replay) {
  return lookup(
      replay && st.roles.at(name) == validator ? st.mirror : st.original, name);
}

std::string Construction::helper(
    source::Body &body, const std::string &role, const std::string &key,
    const source::Names &attrs, const std::vector<std::string> &operands,
    const std::string &protocol, const std::string &callsite,
    const std::string &function, const std::string &opsite,
    const std::string &sourceRole, const std::string &kind,
    std::vector<std::string> &results, const source::Node *origin) {
  if (!budget())
    return {};
  const auto *kernel = signature(key);
  if (!kernel)
    return {};
  std::string name = fresh(), site = fresh();
  source::Function fn;
  fn.name = name;
  if (origin)
    fn.location = origin->location;
  source::Names fnOperands, fnResults, actualResults;
  for (size_t k = 0; k < operands.size(); ++k) {
    std::string n = "arg" + std::to_string(k);
    fn.arguments.push_back({n, kernel->inputs[k]});
    fnOperands.push_back(n);
  }
  for (size_t k = 0; k < kernel->outputs.size(); ++k) {
    std::string n = "result" + std::to_string(k), actual = fresh();
    fn.results.push_back(kernel->outputs[k]);
    fnResults.push_back(n);
    actualResults.push_back(actual);
    results.push_back(actual);
  }
  std::string generatedOp = opsite.empty() ? std::string("transition") : opsite;
  fn.body = source::Body{
      instruction(
          generatedOp,
          source::Operation{key, {}, attrs, std::move(fnOperands), fnResults},
          origin),
      instruction("", source::Return{std::move(fnResults)}, origin)};
  // The certificate separately relates this definition to its source.
  fn.origin = source::LogicalOrigin{name, {}};
  outFunctions.push_back(std::move(fn));
  body.push_back(instruction(
      site, source::LocalCall{role, name, operands, std::move(actualResults)},
      origin));
  origins.push_back(json::Array{name, generatedOp, protocol, callsite, function,
                                opsite, sourceRole, kind});
  return name;
}

bool Construction::preserveLocal(const std::string &id, const std::string &path,
                                 const source::Function &fn,
                                 const std::string &role, bool active) {
  // Preserve computations over installed immutable local values, including
  // private custody. This does not mirror them to another role. Provider
  // transitions keep their construction-specific helper/frame interpretation.
  for (const auto &arg : fn.arguments)
    if (!duplicable(arg.type))
      return false;
  for (const auto &type : fn.results)
    if (!duplicable(type))
      return false;
  if (hasLocalControl(fn)) {
    if (active && role == validator)
      for (const auto &output : fn.body->back().get<source::Return>()->values)
        if (needs(id, path, output)) {
          fail("construction-local-control-replay");
          return false;
        }
    return true; // Formation already checked every nested primitive's custody.
  }
  for (const auto &ins : *fn.body) {
    if (!budget())
      return false;
    const auto *op = ins.get<source::Operation>();
    if (!op)
      continue; // Source admission allows only operations and the return.
    const auto *sig = signature(op->callee);
    if (!sig)
      return false;
    for (const auto &type : sig->inputs)
      if (!duplicable(type))
        return false;
    for (const auto &type : sig->outputs)
      if (!duplicable(type))
        return false;
    if (active && role == validator)
      for (const auto &output : op->outputs)
        if (needs(id, path, output))
          return false;
  }
  return true;
}

void Construction::emitLocal(const std::string &id, const std::string &path,
                             const source::Instruction &ins,
                             EmissionState &state, source::Body &body,
                             bool active) {
  const auto &call = *ins.get<source::LocalCall>();
  const auto &fn = *functions.at(call.callee);
  auto &inst = instances.at(id);
  std::string role = inst.roles.at(call.role),
              localPath = path + "/" + ins.site;
  if (preserveLocal(id, localPath, fn, role, active)) {
    // A distinct clone per call occurrence makes the existing (function, site)
    // manifest key unambiguous, including calls from different roles/instances.
    source::Function preserved = fn;
    preserved.name = fresh();
    preserved.origin = source::LogicalOrigin{preserved.name, {}};
    source::Names args, results;
    for (const auto &input : call.inputs)
      args.push_back(value(state, input));
    const auto &returned = fn.body->back().get<source::Return>()->values;
    for (size_t k = 0; k < call.outputs.size(); ++k) {
      const auto &output = call.outputs[k];
      std::string actual = fresh();
      results.push_back(actual);
      state.original[output] = actual;
      state.roles[output] = role;
      state.types[output] = fn.results[k];
      if (role == producer)
        state.mirror[output] = actual;
      else {
        // A returned argument can already have a public mirror without any
        // operation in this call requiring replay.
        for (size_t j = 0; j < fn.arguments.size(); ++j)
          if (returned[k] == fn.arguments[j].name &&
              state.mirror.count(call.inputs[j]))
            state.mirror[output] = state.mirror.at(call.inputs[j]);
      }
    }
    source::walk(*fn.body, [&](const source::Instruction &op) {
      if (!op.site.empty())
        origins.push_back(json::Array{preserved.name, op.site, inst.def->name,
                                      ins.site, fn.name, op.site, call.role,
                                      "original"});
    });
    body.push_back(
        instruction(ins.site,
                    source::LocalCall{role, preserved.name, std::move(args),
                                      std::move(results)},
                    &ins));
    outFunctions.push_back(std::move(preserved));
    return;
  }
  if (!problem.empty())
    return;
  EmissionState st;
  st.producerTranscript = state.producerTranscript;
  st.validatorTranscript = state.validatorTranscript;
  for (size_t k = 0; k < fn.arguments.size(); ++k) {
    std::string formal = fn.arguments[k].name, actual = call.inputs[k];
    st.original[formal] = value(state, actual);
    st.roles[formal] = role;
    st.types[formal] = fn.arguments[k].type;
    if (role == producer)
      st.mirror[formal] = st.original[formal];
    else if (state.mirror.count(actual))
      st.mirror[formal] = state.mirror.at(actual);
  }
  for (const auto &v : *fn.body) {
    if (const auto *ret = v.get<source::Return>()) {
      for (size_t k = 0; k < ret->values.size(); ++k) {
        std::string formal = ret->values[k], actual = call.outputs[k];
        state.original[actual] = value(st, formal);
        state.types[actual] = st.types.at(formal);
        state.roles[actual] = role;
        if (st.mirror.count(formal))
          state.mirror[actual] = st.mirror.at(formal);
      }
      state.producerTranscript = st.producerTranscript;
      state.validatorTranscript = st.validatorTranscript;
      return;
    }
    if (!v.get<source::Operation>()) {
      fail("construction-local-control-static-trace");
      return;
    }
    const auto &op = *v.get<source::Operation>();
    const std::string key = op.callee;
    const std::string operation = contract(key);
    const auto *sample = samplingContract(operation);
    bool challenge = active && role == validator && randomDraw(operation);
    const std::string emittedKey =
        challenge ? transcriptBinding(sample->derivedCounterpart.str()) : key;
    if (!problem.empty())
      return;
    bool replay = challenge;
    for (size_t k = 0; k < op.outputs.size(); ++k)
      replay |= active && role == validator &&
                needs(id, localPath, op.outputs[k]) &&
                serializable(outputType(key, k));
    std::vector<std::string> args, out;
    if (challenge) {
      for (size_t i = 0; i < op.inputs.size(); ++i)
        args.push_back(i == sample->stateInput ? st.validatorTranscript
                                               : value(st, op.inputs[i]));
    } else
      for (auto &n : op.inputs)
        args.push_back(value(st, n));
    source::Names attrs = challenge ? source::Names{inst.def->name, ins.site,
                                                    fn.name, v.site, call.role}
                                    : op.attributes;
    helper(body, role, emittedKey, attrs, args, inst.def->name, ins.site,
           fn.name, v.site, call.role, challenge ? "construction" : "original",
           out, &v);
    if (!problem.empty())
      return;
    if (challenge) {
      st.original[op.outputs[sample->valueOutput]] = out[sample->valueOutput];
      // Explicit source-resource interpretation: the original RNG successor
      // aliases its input. It is not the transcript's transition counter.
      st.original[op.outputs[sample->stateOutput]] =
          value(st, op.inputs[sample->stateInput]);
      st.validatorTranscript = out[sample->stateOutput];
    } else
      for (size_t k = 0; k < out.size(); ++k)
        st.original[op.outputs[k]] = out[k];
    for (size_t k = 0; k < op.outputs.size(); ++k) {
      std::string n = op.outputs[k];
      st.types[n] = outputType(key, k);
      st.roles[n] = role;
      if (role == producer)
        st.mirror[n] = st.original[n];
    }
    if (replay) {
      args.clear();
      out.clear();
      if (challenge) {
        for (size_t i = 0; i < op.inputs.size(); ++i)
          args.push_back(i == sample->stateInput
                             ? st.producerTranscript
                             : value(st, op.inputs[i], true));
      } else
        for (auto &n : op.inputs)
          args.push_back(value(st, n, true));
      if (!challenge && !recipe(operation)) {
        fail("construction-unavailable-recipe:" + operation);
        return;
      }
      helper(body, producer, emittedKey, attrs, args, inst.def->name, ins.site,
             fn.name, v.site, call.role, challenge ? "construction" : "recipe",
             out, &v);
      if (!problem.empty())
        return;
      if (challenge) {
        st.mirror[op.outputs[sample->valueOutput]] = out[sample->valueOutput];
        st.producerTranscript = out[sample->stateOutput];
      } else
        for (size_t k = 0; k < out.size(); ++k)
          st.mirror[op.outputs[k]] = out[k];
    }
  }
}

std::string Construction::outputType(const std::string &key, size_t index) {
  const auto *k = signature(key);
  if (!k) {
    return "invalid";
  }
  return k->outputs.at(index);
}

void Construction::observe(const std::string &id,
                           const source::Instruction &ins, EmissionState &st,
                           source::Body &body) {
  auto &inst = instances.at(id);
  const auto &op = *ins.get<source::Message>();
  std::string sender = inst.roles.at(op.sender),
              receiver = inst.roles.at(op.receiver);
  std::string type = st.types.at(op.input);
  std::string key =
      transcriptBinding("transcript.observe." + typeKind(type).str(), type);
  if (!problem.empty())
    return;
  source::Names attrs{inst.def->name, ins.site, op.schema, op.sender,
                      op.receiver};
  for (const std::string &role : {producer, validator}) {
    std::string payload;
    if (role == sender)
      payload = value(st, op.input);
    else if (role == producer)
      payload = value(st, op.input, true);
    else
      payload = value(st, op.output);
    std::vector<std::string> out;
    helper(body, role, key, attrs,
           {role == producer ? st.producerTranscript : st.validatorTranscript,
            payload},
           inst.def->name, ins.site, "", ins.site, op.sender, "construction",
           out, &ins);
    if (!problem.empty())
      return;
    (role == producer ? st.producerTranscript : st.validatorTranscript) =
        out[0];
  }
  (void)receiver;
}

bool Construction::inputMirror(const std::string &id, size_t k) {
  const auto &i = instances.at(id);
  const auto &p = i.def->arguments[k];
  return i.roles.at(p.role) == validator && serializable(p.type) &&
         needs(id, "", p.name);
}

bool Construction::outputMirror(const std::string &id, size_t k) {
  const auto &i = instances.at(id);
  const auto &p = i.def->results[k];
  return i.roles.at(p.role) == validator && serializable(p.type) &&
         needs(id, "", "result/" + std::to_string(k));
}

std::string Construction::inactiveInstance(const std::string &id) {
  if (inactiveNames.count(id))
    return inactiveNames.at(id);
  const auto &i = instances.at(id);
  std::string name = fresh(), definition = fresh();
  inactiveNames[id] = name;
  inactiveDefinitions[id] = definition;
  source::Instance instance = *i.record;
  instance.name = name;
  instance.protocol = definition;
  instance.dependencies.clear();
  instance.roles.clear();
  source::Protocol def = *i.def;
  def.name = definition;
  def.dependencies.clear();
  for (const auto &p : i.dependencies) {
    instance.dependencies.emplace_back(p.first, inactiveInstance(p.second));
    source::Dependency dep;
    dep.name = p.first;
    dep.protocol = inactiveDefinitions.at(p.second);
    def.dependencies.push_back(std::move(dep));
  }
  for (auto &role : def.roles)
    role = i.roles.at(role);
  for (auto &port : def.arguments)
    port.role = i.roles.at(port.role);
  for (auto &port : def.results)
    port.role = i.roles.at(port.role);
  source::walk(*def.body, [&](source::Instruction &ins) {
    if (auto *call = ins.get<source::LocalCall>())
      call->role = i.roles.at(call->role);
    else if (auto *stop = ins.get<source::Stop>())
      stop->role = i.roles.at(stop->role);
    else if (auto *message = ins.get<source::Message>()) {
      message->sender = i.roles.at(message->sender);
      message->receiver = i.roles.at(message->receiver);
    }
  });
  outProtocols.push_back(std::move(def));
  for (const auto &role : i.roles)
    instance.roles.emplace_back(role.second, role.second);
  outInstances.push_back(std::move(instance));
  return name;
}

std::vector<std::string> Construction::emitBlock(
    const std::string &id, const std::string &path,
    const source::Body &instructions, EmissionState &st, source::Body &body,
    std::vector<source::Dependency> &depDecls, source::Assignments &depBindings,
    bool active, std::vector<std::string> *returnedMirrors) {
  auto &inst = instances.at(id);
  for (const auto &v : instructions) {
    if (!budget() || !problem.empty())
      return {};
    if (v.get<source::Return>() || v.get<source::Yield>()) {
      const auto &values = v.get<source::Return>()
                               ? v.get<source::Return>()->values
                               : v.get<source::Yield>()->values;
      std::vector<std::string> results;
      for (auto &n : values) {
        results.push_back(value(st, n));
        if (returnedMirrors)
          returnedMirrors->push_back(st.roles.at(n) == producer ? value(st, n)
                                     : st.mirror.count(n) ? st.mirror.at(n)
                                                          : "");
      }
      return results;
    }
    if (v.get<source::LocalCall>())
      emitLocal(id, path, v, st, body, active);
    else if (const auto *message = v.get<source::Message>()) {
      std::string sender = inst.roles.at(message->sender),
                  receiver = inst.roles.at(message->receiver);
      std::string output = fresh();
      st.roles[message->output] = receiver;
      st.types[message->output] = st.types.at(message->input);
      if (!active || sender == producer) {
        body.push_back(
            instruction(v.site,
                        source::Message{message->schema, sender, receiver,
                                        value(st, message->input), output},
                        &v));
        st.original[message->output] = output;
        if (active)
          st.mirror[message->output] = value(st, message->input);
      } else {
        st.original[message->output] = value(st, message->input, true);
        st.mirror[message->output] = st.original[message->output];
      }
      if (active)
        observe(id, v, st, body);
    } else if (const auto *call = v.get<source::ProtocolCall>()) {
      std::string child = inst.dependencies.at(call->callee);
      auto &ci = instances.at(child);
      std::string alias = call->callee;
      if (active)
        emitInstance(child);
      else {
        alias = fresh();
        std::string inactive = inactiveInstance(child);
        source::Dependency dep;
        dep.name = alias;
        dep.protocol = inactiveDefinitions.at(child);
        depDecls.push_back(std::move(dep));
        depBindings.emplace_back(alias, inactive);
      }
      source::Names args, outputs;
      for (auto &n : call->inputs)
        args.push_back(value(st, n));
      for (size_t k = 0; k < call->outputs.size(); ++k) {
        std::string n = call->outputs[k], actual = fresh();
        const auto &p = ci.def->results[k];
        st.original[n] = actual;
        st.types[n] = p.type;
        st.roles[n] = ci.roles.at(p.role);
        outputs.push_back(actual);
        if (st.roles[n] == producer)
          st.mirror[n] = actual;
      }
      if (active) {
        for (size_t k = 0; k < call->inputs.size(); ++k)
          if (inputMirror(child, k))
            args.push_back(value(st, call->inputs[k], true));
        args.push_back(st.producerTranscript);
        args.push_back(st.validatorTranscript);
        for (size_t k = 0; k < call->outputs.size(); ++k)
          if (outputMirror(child, k)) {
            std::string n = fresh();
            st.mirror[call->outputs[k]] = n;
            outputs.push_back(n);
          }
        st.producerTranscript = fresh();
        st.validatorTranscript = fresh();
        outputs.push_back(st.producerTranscript);
        outputs.push_back(st.validatorTranscript);
      }
      body.push_back(instruction(
          v.site,
          source::ProtocolCall{alias, std::move(args), std::move(outputs)},
          &v));
    } else if (const auto *loop = v.get<source::Loop>()) {
      const EmissionState beforeLoop = st;
      uint64_t n = active ? count(*loop, inst) : 0;
      bool live = active && n != 0;
      EmissionState inner;
      source::Assignments initials;
      source::Names captures, outputs;
      source::Body nested;
      std::vector<std::string> carryNames, outputNames;
      for (size_t k = 0; k < loop->carried.size(); ++k) {
        std::string name = loop->carried[k].first,
                    sourceName = loop->carried[k].second;
        std::string argument = fresh(), output = fresh();
        inner.original[name] = argument;
        inner.types[name] = st.types.at(sourceName);
        inner.roles[name] = st.roles.at(sourceName);
        initials.push_back({argument, value(st, sourceName)});
        std::string resultName = loop->outputs[k];
        st.original[resultName] = output;
        st.types[resultName] = inner.types[name];
        st.roles[resultName] = inner.roles[name];
        outputs.push_back(output);
        carryNames.push_back(name);
        outputNames.push_back(resultName);
        if (inner.roles[name] == producer) {
          inner.mirror[name] = argument;
          st.mirror[resultName] = output;
        }
      }
      for (auto &v : loop->captures) {
        std::string name = v, actual = value(st, name);
        captures.push_back(actual);
        inner.original[name] = actual;
        inner.types[name] = st.types.at(name);
        inner.roles[name] = st.roles.at(name);
        if (inner.roles[name] == producer)
          inner.mirror[name] = actual;
        else if (live && st.mirror.count(name)) {
          inner.mirror[name] = st.mirror.at(name);
          if (!is_contained(captures, st.mirror.at(name)))
            captures.push_back(st.mirror.at(name));
        }
      }
      std::vector<size_t> mirrored;
      for (size_t k = 0; k < carryNames.size(); ++k) {
        std::string name = carryNames[k];
        if (inner.roles[name] != validator || !serializable(inner.types[name]))
          continue;
        bool inputNeeded = live && needs(id, path + "/" + v.site, name);
        bool outputNeeded = active && needs(id, path, outputNames[k]);
        if (!inputNeeded && !outputNeeded)
          continue;
        if (!n) {
          st.mirror[outputNames[k]] = value(st, loop->carried[k].second, true);
          continue;
        }
        std::string initial;
        if (inputNeeded || n > 1)
          initial = value(st, loop->carried[k].second, true);
        else {
          // A single iteration may produce a public result from a private
          // initial slot. The seed is unobserved, so use an available value
          // of the same type, or the installed scalar constant constructor.
          for (auto &candidate : beforeLoop.types)
            if (candidate.second == inner.types[name] &&
                beforeLoop.mirror.count(candidate.first)) {
              initial = beforeLoop.mirror.at(candidate.first);
              break;
            }
          if (initial.empty()) {
            std::vector<std::string> seed;
            std::string type = inner.types[name];
            auto kind = typeKind(type);
            std::string key = kind == "field" || kind == "bool"
                                  ? "field.constant"
                              : kind == "group"  ? "curve.generator"
                              : kind == "groups" ? "curve.empty"
                              : kind == "point"  ? "poly.empty_point"
                                                 : "";
            if (!key.empty()) {
              helper(body, producer, seedBinding(key, type),
                     key == "field.constant" ? source::Names{"0"}
                                             : source::Names{},
                     {}, inst.def->name, v.site, "", "seed", "", "construction",
                     seed, &v);
              if (!seed.empty())
                initial = seed[0];
              if (kind == "bool" && !initial.empty()) {
                seed.clear();
                helper(body, producer, seedBinding("field.equal", type), {},
                       {initial, initial}, inst.def->name, v.site, "", "seed",
                       "", "construction", seed, &v);
                if (!seed.empty())
                  initial = seed[0];
              }
            }
          }
          if (initial.empty()) {
            fail("construction-single-loop-seed");
            return {};
          }
        }
        std::string argument = fresh(), output = fresh();
        initials.push_back({argument, initial});
        inner.mirror[name] = argument;
        st.mirror[outputNames[k]] = output;
        outputs.push_back(output);
        mirrored.push_back(k);
      }
      if (active) {
        inner.producerTranscript = fresh();
        inner.validatorTranscript = fresh();
        initials.push_back({inner.producerTranscript, st.producerTranscript});
        initials.push_back({inner.validatorTranscript, st.validatorTranscript});
      }
      std::string loopPt = inner.producerTranscript,
                  loopVt = inner.validatorTranscript;
      std::vector<std::string> mirrors;
      auto values = emitBlock(id, path + "/" + v.site, loop->body, inner,
                              nested, depDecls, depBindings, live, &mirrors);
      if (!problem.empty())
        return {};
      source::Names yields;
      for (auto &v : values)
        yields.push_back(v);
      for (size_t k : mirrored) {
        bool outputNeeded = needs(id, path, outputNames[k]);
        std::string yielded = (n == 1 && !outputNeeded)
                                  ? inner.mirror.at(carryNames[k])
                                  : mirrors[k];
        if (yielded.empty()) {
          fail("construction-loop-recipe");
          return {};
        }
        yields.push_back(yielded);
      }
      if (active) {
        yields.push_back(live ? inner.producerTranscript : loopPt);
        yields.push_back(live ? inner.validatorTranscript : loopVt);
        st.producerTranscript = fresh();
        st.validatorTranscript = fresh();
        outputs.push_back(st.producerTranscript);
        outputs.push_back(st.validatorTranscript);
      }
      nested.push_back(instruction("", source::Yield{std::move(yields)},
                                   &loop->body.back()));
      body.push_back(instruction(
          v.site,
          source::Loop{loop->count, std::move(initials), std::move(captures),
                       std::move(nested), std::move(outputs)},
          &v));
    } else {
      fail("construction-incomplete-control");
      return {};
    }
  }
  fail("construction-body");
  return {};
}

void Construction::emitInstance(const std::string &id) {
  if (!emitted.insert(id).second || !problem.empty())
    return;
  auto &inst = instances.at(id);
  const auto &def = *inst.def;
  EmissionState st;
  std::vector<source::OwnedParameter> ports;
  std::vector<source::OwnedResult> returns;
  std::vector<source::Dependency> depDecls;
  source::Assignments depBindings;
  source::Body body;
  for (const auto &p : def.arguments) {
    std::string name = p.name, role = inst.roles.at(p.role);
    st.original[name] = name;
    st.types[name] = p.type;
    st.roles[name] = role;
    ports.push_back({name, role, p.type});
    if (role == producer)
      st.mirror[name] = name;
    if (id == root)
      inputMap.push_back(json::Array{role, name, json::Array{"source", name}});
  }
  for (size_t k = 0; k < def.results.size(); ++k) {
    const auto &p = def.results[k];
    if (!omitResult(id, k))
      returns.push_back({inst.roles.at(p.role), p.type});
  }
  if (id == root) {
    for (auto &binding : bindings) {
      std::string p = binding.producerPort;
      if (p.empty()) {
        p = fresh();
        ports.push_back({p, producer, binding.type});
        inputMap.push_back(
            json::Array{producer, p, json::Array{"public", binding.label}});
      }
      for (auto &n : binding.ports)
        if (st.roles.at(n) == validator)
          st.mirror[n] = p;
    }
  } else
    for (size_t k = 0; k < def.arguments.size(); ++k)
      if (inputMirror(id, k)) {
        const auto &p = def.arguments[k];
        std::string name = fresh();
        st.mirror[p.name] = name;
        ports.push_back({name, producer, p.type});
      }
  st.producerTranscript = fresh();
  st.validatorTranscript = fresh();
  ports.push_back({st.producerTranscript, producer, transcriptType()});
  ports.push_back({st.validatorTranscript, validator, transcriptType()});
  if (id == root) {
    inputMap.push_back(json::Array{producer, st.producerTranscript,
                                   json::Array{"transcript"}});
    inputMap.push_back(json::Array{validator, st.validatorTranscript,
                                   json::Array{"transcript"}});
  }
  for (size_t k = 0; k < def.results.size(); ++k)
    if (outputMirror(id, k))
      returns.push_back({producer, def.results[k].type});
  if (id == root) {
    std::map<std::string, unsigned> sourceIndices, generatedIndices;
    for (size_t k = 0; k < def.results.size(); ++k) {
      std::string role = inst.roles.at(def.results[k].role);
      unsigned sourceIndex = sourceIndices[role]++;
      if (!omitResult(id, k))
        resultMap.push_back(
            json::Array{role, std::to_string(generatedIndices[role]++),
                        json::Array{"source", std::to_string(sourceIndex)}});
    }
    for (const std::string &role : {producer, validator})
      resultMap.push_back(json::Array{role,
                                      std::to_string(generatedIndices[role]),
                                      json::Array{"transcript"}});
  }
  returns.push_back({producer, transcriptType()});
  returns.push_back({validator, transcriptType()});
  std::set<std::string> liveAliases;
  std::function<void(const source::Body &)> calls =
      [&](const source::Body &instructions) {
        for (const auto &v : instructions) {
          if (const auto *call = v.get<source::ProtocolCall>())
            liveAliases.insert(call->callee);
          else if (const auto *loop = v.get<source::Loop>()) {
            if (count(*loop, inst) != 0)
              calls(loop->body);
          }
          if (!problem.empty())
            return;
        }
      };
  calls(*def.body);
  if (!problem.empty())
    return;
  for (const auto &alias : liveAliases) {
    const auto &childId = inst.dependencies.at(alias);
    source::Dependency dep;
    dep.name = alias;
    dep.protocol = instances.at(childId).generated;
    depDecls.push_back(std::move(dep));
    depBindings.emplace_back(alias, childId);
  }
  std::vector<std::string> mirrors;
  auto values = emitBlock(id, "", *def.body, st, body, depDecls, depBindings,
                          true, &mirrors);
  if (!problem.empty())
    return;
  source::Names outputs;
  for (size_t k = 0; k < values.size(); ++k)
    if (!omitResult(id, k))
      outputs.push_back(values[k]);
  for (size_t k = 0; k < values.size(); ++k)
    if (outputMirror(id, k)) {
      if (mirrors[k].empty()) {
        fail("construction-result-recipe");
        return;
      }
      outputs.push_back(mirrors[k]);
    }
  outputs.push_back(st.producerTranscript);
  outputs.push_back(st.validatorTranscript);
  body.push_back(
      instruction("", source::Return{std::move(outputs)}, &def.body->back()));
  source::Protocol protocol = def;
  protocol.name = inst.generated;
  protocol.roles = {producer, validator};
  protocol.arguments = std::move(ports);
  protocol.results = std::move(returns);
  protocol.dependencies = std::move(depDecls);
  protocol.body = std::move(body);
  outProtocols.push_back(std::move(protocol));
  source::Instance instance = *inst.record;
  instance.protocol = inst.generated;
  instance.dependencies = std::move(depBindings);
  instance.roles = {{producer, producer}, {validator, validator}};
  outInstances.push_back(std::move(instance));
}

} // namespace zkc::protocol::construction
