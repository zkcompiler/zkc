#include "SignatureWitness.h"
#include "Checker.h"
#include "Conformance.h"
#include "DescriptorFactories.h"
#include "Effects.h"
#include "Internal.h"
#include "ScopedWitness.h"
#include "WrittenSource.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/MathExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool checkOrigins(Semantics &types, const Declaration &decl,
                  const SyntaxDeclaration &source,
                  const ScopedParameter &parameter,
                  const SyntaxScopedSignature &written) {
  auto refuse = [&](llvm::StringRef message) {
    return types.fail("source.scoped-witness", message, parameter.span);
  };
  const auto &signature = parameter.signature;
  if (!types.charge(
          written.inputLabels.size() + source.descriptorInputs.size() +
              written.itemOrigins.size() + parameter.itemOrigins.size() + 1,
          parameter.span))
    return false;
  if (written.inputLabels.size() != signature.inputs.size() ||
      written.inputLabels != parameter.inputLabels ||
      source.descriptorInputs.size() != decl.descriptorInputs.size())
    return refuse("callback source input coverage differs");
  std::map<std::string, unsigned> labels, domains;
  for (unsigned i = 0; i < written.inputLabels.size(); ++i) {
    const auto &label = written.inputLabels[i];
    if (!types.charge(label.size() + 1, parameter.span))
      return false;
    if (!label.empty() && !labels.emplace(label, i).second)
      return refuse("duplicate callback source label");
  }
  for (unsigned i = 0; i < source.descriptorInputs.size(); ++i) {
    const auto &name = source.descriptorInputs[i].name;
    if (!types.charge(name.size() + 1, parameter.span))
      return false;
    if (name != decl.descriptorInputs[i].name ||
        !domains.emplace(name, i).second)
      return refuse("callback source domain differs");
  }
  std::map<unsigned, unsigned> expected;
  for (const auto &condition : written.itemOrigins) {
    if (!types.charge(condition.input.size() + condition.domain.size() + 1,
                      condition.span))
      return false;
    auto input = labels.find(condition.input);
    auto domain = domains.find(condition.domain);
    if (input == labels.end() || domain == domains.end() ||
        !finiteDescriptorItem(decl.descriptorInputs[domain->second].contract) ||
        signature.inputs[input->second] !=
            *finiteDescriptorItem(
                decl.descriptorInputs[domain->second].contract) ||
        !expected.emplace(input->second, domain->second).second)
      return refuse("invalid authored callback item origin");
  }
  return parameter.itemOrigins == expected ||
         refuse("callback item origins differ from authored selectors");
}

} // namespace
llvm::Error checkSignatureSources(const CheckedStorage &storage, Work &work) {
  Semantics types(storage.declarations, storage.assets, work);
  size_t retained = 0;
  for (const auto &decl : storage.declarations) {
    if (!types.charge(1, decl.span))
      return types.takeError();
    if (!decl.scopedInputs.empty() && decl.kind != Declaration::Kind::Math &&
        decl.kind != Declaration::Kind::Local)
      return failure("source.scoped-witness",
                     "callable mode cannot retain scoped inputs", decl.span);
    auto found = storage.signatureSources.find(decl.id.index);
    if (found == storage.signatureSources.end()) {
      if (!decl.scopedInputs.empty() || decl.effectAllowance)
        return failure("source.scoped-witness", "missing signature source",
                       decl.span);
      continue;
    }
    ++retained;
    auto refuse = [&] {
      return failure("source.scoped-witness",
                     "contract differs from authored signature", decl.span);
    };
    if (!found->second)
      return refuse();
    const auto &source = *found->second;
    if (!types.charge(source.scopedInputs.size() +
                          source.effectDependencies.size() + 1,
                      decl.span))
      return types.takeError();
    if (decl.scopedInputs.size() != source.scopedInputs.size())
      return refuse();
    for (unsigned slot = 0; slot < decl.scopedInputs.size(); ++slot) {
      const auto &written = source.scopedInputs[slot].scoped;
      const auto &parameter = decl.scopedInputs[slot];
      if (!written || written->mode != parameter.signature.mode ||
          written->allowance != parameter.signature.allowance)
        return refuse();
      if (!checkOrigins(types, decl, source, parameter, *written))
        return types.takeError();
    }
    std::optional<EffectSummary> expected;
    if (source.effects) {
      expected = EffectSummary{*source.effects};
      for (const auto &name : source.effectDependencies) {
        if (!types.charge(source.scopedInputs.size() + 1, decl.span))
          return types.takeError();
        auto input = llvm::find_if(source.scopedInputs, [&](const auto &port) {
          return port.name == name;
        });
        if (input == source.scopedInputs.end() || !input->scoped)
          return refuse();
        expected->dependencies.emplace(
            unsigned(input - source.scopedInputs.begin()),
            input->scoped->allowance);
      }
      if (!joinEffects(types, *expected, EffectSummary{}, decl.span))
        return types.takeError();
    }
    if (expected != decl.effectAllowance)
      return refuse();
  }
  if (retained != storage.signatureSources.size())
    return failure("source.scoped-witness", "invalid signature source owner");
  return llvm::Error::success();
}
namespace {
// The expected edges come from immutable authored headers and frozen canonical
// IDs, not the mutable Declaration::members or conformance vectors.
struct ContractHeaders {
  const CheckedStorage &storage;
  Semantics &types;
  std::map<uint32_t, const SyntaxDeclaration *> sources;
  std::map<uint32_t, uint32_t> parents;
  bool allHeaders = false;
  std::map<uint32_t, SyntaxDeclaration> generatedHeaders;
  bool collect(const SyntaxDeclaration &source, const std::string &path,
               std::optional<DeclarationId> parent, unsigned depth,
               bool contractMember = false) {
    if (depth > types.work.limits.typeDepth)
      return types.fail("source.limit", "conformance source depth",
                        source.span);
    if (!types.charge(path.size() + source.members.size() + 1, source.span))
      return false;
    if (source.generated ||
        (source.anonymous && (!allHeaders || !source.constructionHandler)))
      return true;
    if (!allHeaders && source.kind != Declaration::Kind::Module &&
        source.kind != Declaration::Kind::Interface &&
        source.kind != Declaration::Kind::Associated &&
        source.kind != Declaration::Kind::Alias &&
        source.kind != Declaration::Kind::Domain &&
        source.kind != Declaration::Kind::Record &&
        source.kind != Declaration::Kind::Variant &&
        source.kind != Declaration::Kind::Math &&
        source.kind != Declaration::Kind::Local &&
        !(source.kind == Declaration::Kind::Protocol && contractMember) &&
        source.kind != Declaration::Kind::View)
      return true;
    std::optional<DeclarationId> id;
    if (source.anonymous) {
      // Anonymous handlers are absent from the named namespace. Grouped rules
      // can share spans, so join their frozen written-declaration links under
      // the frozen parent rather than matching candidate names or locations.
      if (!parent || !source.writtenDeclaration)
        return types.fail("source.scoped-witness",
                          "missing authored handler owner", source.span);
      for (auto member : storage.declarationIndex->members(*parent)) {
        if (!types.charge(1, source.span))
          return false;
        auto body = storage.bodySources.find(member.index);
        if (body == storage.bodySources.end() || !body->second ||
            body->second->owner.index != member.index || !body->second->syntax)
          continue;
        const auto &written = *body->second->syntax;
        if (!written.constructionHandler ||
            written.writtenDeclaration != source.writtenDeclaration)
          continue;
        if (id)
          return types.fail("source.scoped-witness",
                            "ambiguous authored handler", source.span);
        id = member;
      }
    } else {
      id = storage.declarationIndex->canonical(path);
    }
    if (!id || id->index >= storage.declarations.size())
      return types.fail("source.scoped-witness", "missing authored declaration",
                        source.span);
    // An external child link has no signature; its captured file supplies it.
    if (source.externalModule)
      return true;
    if (!sources.emplace(id->index, &source).second)
      return types.fail("source.scoped-witness", "duplicate authored header",
                        source.span);
    if (!parent && StringRef(path).contains("::"))
      parent = storage.declarationIndex->canonical(
          StringRef(path).rsplit("::").first);
    if (parent)
      parents.emplace(id->index, parent->index);
    if (allHeaders && source.kind == Declaration::Kind::Oracle) {
      // Oracle signatures inspect their generated predicate header. Its name
      // and owner are fixed by collection; no candidate body supplies a fact.
      auto predicate = storage.declarationIndex->canonical(
          path + "::__oracle_admissibility");
      if (!predicate || predicate->index >= storage.declarations.size())
        return types.fail("source.scoped-witness",
                          "missing authored Oracle predicate", source.span);
      if (!types.charge(1, source.span))
        return false;
      auto &header = generatedHeaders[predicate->index];
      header.kind = Declaration::Kind::Relation;
      header.name = "__oracle_admissibility";
      header.span = source.span;
      header.oraclePredicate = true;
      sources.emplace(predicate->index, &header);
      parents.emplace(predicate->index, id->index);
    }
    bool memberContract =
        source.kind == Declaration::Kind::Interface ||
        (source.kind == Declaration::Kind::Module && source.definition);
    for (const auto &member : source.members)
      if (!collect(member, path + "::" + member.name, *id, depth + 1,
                   memberContract))
        return false;
    return true;
  }
};
bool useRetainedProtocolHeaders(const CheckedStorage &storage,
                                ContractHeaders &headers, Semantics &types) {
  // Classification and lexical input IDs belong to immutable parsed syntax.
  // Re-resolve managed constructor routes before replaying its type terms.
  for (auto &[id, source] : headers.sources) {
    if (source->kind != Declaration::Kind::Protocol)
      continue;
    auto found = storage.bodySources.find(id);
    if (!types.charge(1, source->span))
      return false;
    if (found == storage.bodySources.end() || !found->second ||
        found->second->owner.index != id || !found->second->syntax)
      return types.fail("source.scoped-witness", "missing Protocol header",
                        source->span);
    const auto &parsed = *found->second->syntax;
    if (parsed.kind != source->kind || parsed.name != source->name ||
        parsed.span.source.index != source->span.source.index ||
        parsed.span.begin != source->span.begin ||
        parsed.span.end != source->span.end)
      return types.fail("source.scoped-witness", "Protocol source differs",
                        source->span);
    source = &parsed;
    for (const auto &port : source->services) {
      auto selected = storage.declarationIndex->lookup(
          SourceAccess{DeclarationId{id}}, port.type.name,
          {[&] { return types.charge(1, port.span); }, {}});
      auto *reference = std::get_if<ResolvedReference>(&selected);
      if (!reference || !port.serviceReference ||
          *reference != *port.serviceReference)
        return types.diagnostic
                   ? false
                   : types.fail("source.scoped-witness",
                                "managed constructor lookup differs",
                                port.span);
    }
  }
  return true;
}
bool chargeDataPreconditions(Semantics &types,
                             ArrayRef<DataPrecondition> conditions, Span span) {
  if (!types.charge(conditions.size(), span))
    return false;
  for (const auto &condition : conditions)
    if (!types.charge(condition.left.path.size() + condition.right.path.size() +
                          1,
                      condition.span))
      return false;
  return true;
}
llvm::Error chargePremiseIndex(const CheckedStorage &storage, Work &work) {
  if (auto error = work.charge(storage.declarations.size() + 1))
    return error;
  for (const auto &decl : storage.declarations) {
    if (auto error = work.charge(
            decl.qualifiedName.size() + decl.parameters.size() + 1, decl.span))
      return error;
    for (const auto &parameter : decl.parameters)
      if (auto error = work.charge(parameter.atom.size() + 1, decl.span))
        return error;
  }
  return Error::success();
}
bool chargePremiseNatural(Semantics &types, const Natural &natural, Span span) {
  if (!types.charge(natural.terms().size(), span))
    return false;
  for (const auto &[factors, coefficient] : natural.terms()) {
    (void)coefficient;
    if (!types.charge(factors.size(), span))
      return false;
    for (const auto &factor : factors)
      if (!types.charge(factor.name.size() + factor.member.size() + 1, span))
        return false;
  }
  return true;
}
bool chargePremiseType(Semantics &types, const Type &type, Span span) {
  // chargeType computes complexity before debiting work. Preflight variable
  // containers first so even a single oversized nested term cannot traverse
  // unpaid arguments or polynomial factors during that computation.
  uint64_t nodes = 0;
  std::function<bool(const Type &, unsigned)> preflight = [&](const Type &term,
                                                              unsigned depth) {
    if (++nodes > types.work.limits.typeNodes ||
        depth > types.work.limits.typeDepth)
      return types.fail("source.limit", "premise type limit exceeded", span);
    if (!types.charge(term.arguments.size() + term.domain.size() +
                          term.sort.size() + 1,
                      span) ||
        !chargePremiseNatural(types, term.dimension, span))
      return false;
    for (const auto &argument : term.arguments)
      if (!preflight(argument, depth + 1))
        return false;
    return true;
  };
  return preflight(type, 1) && types.chargeType(type, span);
}
bool chargePremiseBounds(Semantics &types, ArrayRef<NaturalBound> naturals,
                         ArrayRef<PermissionBound> permissions,
                         ArrayRef<CapabilityBound> capabilities, Span span) {
  if (!types.charge(
          naturals.size() + permissions.size() + capabilities.size() + 1, span))
    return false;
  for (const auto &bound : naturals)
    if (!chargePremiseNatural(types, bound.lhs, span) ||
        !chargePremiseNatural(types, bound.rhs, span))
      return false;
  for (const auto &bound : permissions)
    if (!chargePremiseType(types, bound.type, span))
      return false;
  for (const auto &bound : capabilities) {
    if (!types.charge(bound.predicate.size() + bound.arguments.size() + 1,
                      span))
      return false;
    for (const auto &argument : bound.arguments)
      if (!chargePremiseType(types, argument, span))
        return false;
  }
  return true;
}
bool chargePremiseParameters(Semantics &types, ArrayRef<Parameter> parameters,
                             Span span) {
  if (!types.charge(parameters.size(), span))
    return false;
  for (const auto &parameter : parameters) {
    if (!types.charge(parameter.name.size() + parameter.atom.size() +
                          parameter.domainSort.size() +
                          parameter.arguments.size() + 1,
                      span))
      return false;
    for (const auto &argument : parameter.arguments)
      if (!chargePremiseType(types, argument, span))
        return false;
  }
  return true;
}
// All header consumers start from the same authored parameter indexing and
// signature inference/admission lifecycle. Candidate parameter atoms must not
// enter the reader's semantic index before these telescopes are reconstructed.
std::unique_ptr<Checker> reconstructHeaders(const CheckedStorage &storage,
                                            CheckedStorage &replay,
                                            const ContractHeaders &headers,
                                            Semantics &types, Work &work) {
  // The shared semantic index charges consumer requirements and admissions.
  // Preflight premise structures before the existing snapshot, including
  // candidate premises whose owner has no authored header. Effect maps on
  // unrelated declarations are copied too, before any signature comparison.
  for (const auto &decl : storage.declarations)
    if (!chargeDataPreconditions(types, decl.dataPreconditions, decl.span) ||
        !chargePremiseParameters(types, decl.parameters, decl.span) ||
        !chargePremiseBounds(types, decl.bounds, decl.permissionBounds,
                             decl.capabilityBounds, decl.span) ||
        (decl.effectAllowance &&
         !types.charge(decl.effectAllowance->dependencies.size(), decl.span)))
      return {};
  if (auto error = chargeSemanticIndex(storage.declarations, work)) {
    types.accept(std::move(error));
    return {};
  }
  // Inheritance and lexical access must come from the frozen header tree too.
  // Otherwise a candidate parent edit could reconstruct its own replacement
  // demand under a different telescope or provider namespace.
  for (const auto &[index, source] : headers.sources) {
    const auto &actual = storage.declarations[index];
    auto parent = headers.parents.find(index);
    auto canonical = storage.declarationIndex->canonical(actual.qualifiedName);
    bool identity = canonical && canonical->index == index;
    if (source->anonymous) {
      identity = parent != headers.parents.end() &&
                 actual.kind == source->kind && actual.name == source->name &&
                 actual.qualifiedName ==
                     storage.declarations[parent->second].qualifiedName +
                         "::<" + source->name + ">";
    }
    auto owner = index;
    std::set<uint32_t> ancestors;
    while (headers.sources.at(owner)->kind != Declaration::Kind::Module) {
      auto enclosing = headers.parents.find(owner);
      if (!ancestors.insert(owner).second ||
          enclosing == headers.parents.end() ||
          !headers.sources.count(enclosing->second)) {
        types.fail("source.scoped-witness", "invalid authored header owner",
                   source->span);
        return {};
      }
      if (!types.charge(1, source->span))
        return {};
      owner = enclosing->second;
    }
    if (!identity || actual.generated || actual.id.index != index ||
        actual.anonymous != source->anonymous ||
        bool(actual.parent) != (parent != headers.parents.end()) ||
        (actual.parent && actual.parent->index != parent->second) ||
        actual.module.index != owner) {
      types.fail("source.scoped-witness", "authored header identity differs",
                 source->span);
      return {};
    }
  }
  replay.declarations = storage.declarations;
  replay.assets = storage.assets;
  replay.sources = storage.sources;
  replay.declarationIndex = storage.declarationIndex;
  for (const auto &[index, source] : headers.sources) {
    auto &decl = replay.declarations[index];
    decl.parameters.clear();
  }
  auto reader = std::make_unique<Checker>(replay, work, SourceAccess{{0}});
  // Register all dependencies before reading a signature; complete them in
  // declaration order, matching the producer's lazy signature lifecycle.
  for (const auto &[index, source] : headers.sources) {
    if (!reader->prepareSignatureReconstruction(DeclarationId{index},
                                                *source)) {
      types.accept(reader->types.takeError());
      return {};
    }
    if (headers.allHeaders) {
      // The ordinary contract reader projects callable/type headers. The
      // combined replay also visits construction, relation and Oracle owners;
      // supply only their additional header terms, never bodies or expressions.
      auto &written = *reader->sources[index];
      written.target = source->target;
      written.targetArguments = source->targetArguments;
      written.targetLabels = source->targetLabels;
      written.relation = source->relation;
      written.oracleDefinition = source->oracleDefinition;
      written.oraclePredicate = source->oraclePredicate;
      written.constructionHandler = source->constructionHandler;
      written.setups = source->setups;
    }
  }
  for (const auto &[index, source] : headers.sources)
    if (!reader->reconstructSignature(DeclarationId{index})) {
      types.accept(reader->types.takeError());
      return {};
    }
  return reader;
}
bool reconstructInferredResult(Semantics &types, const CheckedStorage &storage,
                               const SyntaxDeclaration &source,
                               Declaration &written) {
  if (!source.outputs.empty() || source.abstract || source.descriptorResult ||
      (source.kind != Declaration::Kind::Math &&
       source.kind != Declaration::Kind::Local &&
       source.kind != Declaration::Kind::View))
    return true;
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "inferred result differs from checked source body",
                      source.span);
  };
  if (!types.charge(1, source.span))
    return false;
  const auto &actual = storage.declarations[written.id.index];
  auto retained = storage.bodySources.find(written.id.index);
  if (retained == storage.bodySources.end() || !retained->second ||
      retained->second->owner.index != written.id.index ||
      !retained->second->syntax || !actual.body)
    return refuse();
  const auto &syntax = *retained->second->syntax;
  const auto &body = *actual.body;
  if (syntax.kind != source.kind || syntax.name != source.name ||
      syntax.abstract || !syntax.outputs.empty() || syntax.bodies.empty() ||
      syntax.span.source.index != source.span.source.index ||
      syntax.span.begin != source.span.begin ||
      syntax.span.end != source.span.end || body.stopped ||
      body.mode != (source.kind == Declaration::Kind::Local ? Body::Mode::Local
                                                            : Body::Mode::Math))
    return refuse();
  const auto &region = syntax.bodies.front();
  if (!types.charge(region.results.size() + body.results.size() + 1,
                    region.span))
    return false;
  if (!region.returned || region.results.size() != 1 ||
      body.results.size() != 1 ||
      region.results.front().second >= syntax.expressions.size())
    return refuse();
  auto value = body.expressionValues.find(region.results.front().second);
  if (value == body.expressionValues.end() ||
      value->second.index != body.results.front().index ||
      value->second.index >= body.values.size())
    return refuse();
  // An omitted annotation authorizes body result inference, independently of
  // whether precondition inference is allowed. The result type comes from the
  // immutable checked Body, never Declaration::outputs or the interface. The
  // surrounding scoped witness checks the source/SSA graph with its existing
  // body witnesses; here we additionally bind its return to the authored tail.
  const auto &type = body.values[value->second.index].type;
  if (!types.chargeType(type, region.span))
    return false;
  written.outputs.push_back({"result", type, {}, region.span});
  return true;
}
bool viewBindingsAgree(Semantics &types, ArrayRef<DescriptorBinding> actual,
                       ArrayRef<DescriptorBinding> written, Span span) {
  auto refuse = [&](Span at) {
    return types.fail("source.view-witness",
                      "View recipe differs from authored definition", at);
  };
  if (!types.charge(actual.size() + written.size() + 1, span))
    return false;
  if (actual.size() != written.size())
    return refuse(span);
  for (unsigned i = 0; i < actual.size(); ++i) {
    const auto &x = actual[i], &y = written[i];
    if (!types.charge(x.operands.size() + x.children.size() +
                          x.arguments.size() + x.argumentOrder.size() + 1,
                      x.span) ||
        !types.chargeType(descriptorType(x.contract), x.span,
                          /*complete=*/false))
      return false;
    for (const auto &edge : x.children)
      if (!types.chargeType(descriptorType(edge.contract), x.span,
                            /*complete=*/false))
        return false;
    for (const auto &argument : x.arguments)
      if (!types.chargeType(argument, x.span))
        return false;
    if (x.factory && x.factory->module &&
        !types.chargeType(*x.factory->module, x.span))
      return false;
    if (x.kind != y.kind || x.contract != y.contract ||
        !llvm::equal(x.operands, y.operands,
                     [](ValueId a, ValueId b) { return a.index == b.index; }) ||
        x.children != y.children || x.axis != y.axis ||
        x.parameter != y.parameter || x.expression != y.expression ||
        x.arguments != y.arguments || x.argumentOrder != y.argumentOrder ||
        x.span.source.index != y.span.source.index ||
        x.span.begin != y.span.begin || x.span.end != y.span.end ||
        bool(x.factory) != bool(y.factory))
      return refuse(x.span);
    // Authored drift keeps the existing witness diagnostic. Candidates that
    // agree still undergo complete shape validation before acceptance.
    if (!types.chargeContract(x.contract, x.span))
      return false;
    for (const auto &edge : x.children)
      if (!types.chargeContract(edge.contract, x.span))
        return false;
    if (x.factory &&
        (x.factory->declaration.index != y.factory->declaration.index ||
         x.factory->module != y.factory->module ||
         x.factory->reference != y.factory->reference ||
         x.factory->authoredReference != y.factory->authoredReference))
      return refuse(x.span);
  }
  return true;
}
// Compare the existing reader's fresh ordinary View body, not a candidate
// expression map used as its own expected result. Other callable modes keep
// their independent invocation/value witnesses.
bool viewBodyAgrees(Semantics &types, const Body &actual, const Body &written,
                    Span span) {
  auto refuse = [&] {
    return types.fail("source.view-witness",
                      "ordinary View body differs from authored definition",
                      span);
  };
  auto sameSpan = [](Span a, Span b) {
    return a.source.index == b.source.index && a.begin == b.begin &&
           a.end == b.end;
  };
  auto values = [&](ArrayRef<ValueId> a, ArrayRef<ValueId> b) {
    return types.charge(a.size() + b.size() + 1, span) &&
           llvm::equal(a, b,
                       [](ValueId x, ValueId y) { return x.index == y.index; });
  };
  auto statics = [&](ArrayRef<Type> a, ArrayRef<Type> b) {
    for (const auto &type : a)
      if (!types.chargeType(type, span))
        return false;
    for (const auto &type : b)
      if (!types.chargeType(type, span))
        return false;
    return llvm::equal(a, b);
  };
  if (!types.charge(actual.values.size() + written.values.size() +
                        actual.operations.size() + written.operations.size() +
                        actual.expressionValues.size() +
                        written.expressionValues.size() + 1,
                    span))
    return false;
  if (actual.mode != written.mode || actual.stage != written.stage ||
      actual.inputs != written.inputs || actual.stopped != written.stopped ||
      actual.stopReason != written.stopReason ||
      actual.effects != written.effects ||
      actual.parameterizedSummary != written.parameterizedSummary ||
      actual.formationRequirements != written.formationRequirements ||
      !actual.services.empty() || !actual.scopedBindings.empty() ||
      actual.values.size() != written.values.size() ||
      actual.operations.size() != written.operations.size() ||
      !values(actual.results, written.results) ||
      !llvm::equal(actual.expressionValues, written.expressionValues,
                   [](const auto &a, const auto &b) {
                     return a.first == b.first &&
                            a.second.index == b.second.index;
                   }))
    return types.diagnostic ? false : refuse();
  if (!viewBindingsAgree(types, actual.descriptorBindings,
                         written.descriptorBindings, span))
    return false;
  for (unsigned i = 0; i < written.values.size(); ++i) {
    const auto &a = actual.values[i], &b = written.values[i];
    if (!types.chargeType(a.type, a.span) ||
        !types.chargeType(b.type, b.span) ||
        !types.charge(a.components.size() + b.components.size() + 1, span))
      return false;
    if (a.type != b.type || a.components != b.components ||
        a.oracleHolder != b.oracleHolder || a.placement != b.placement ||
        !sameSpan(a.span, b.span))
      return refuse();
  }
  for (unsigned i = 0; i < written.operations.size(); ++i) {
    const auto &a = actual.operations[i], &b = written.operations[i];
    if (a.action.index() != b.action.index() || !sameSpan(a.span, b.span) ||
        a.statement != b.statement || a.site != b.site ||
        a.expression != b.expression || bool(a.binding) != bool(b.binding) ||
        !values(a.results, b.results))
      return types.diagnostic ? false : refuse();
    if (const auto *math = std::get_if<MathValue>(&a.action)) {
      for (const auto &parameter : math->parameters)
        if (!types.charge(parameter.size() + 1, span))
          return false;
    }
    if (const auto *call = std::get_if<HelperCall>(&a.action)) {
      if ((call->module && !types.chargeType(*call->module, span)) ||
          !types.charge(call->scopedArguments.size() +
                            call->descriptorArguments.size() + 1,
                        span))
        return false;
    }
    bool agrees = std::visit(
        [&](const auto &expected) {
          using T = std::decay_t<decltype(expected)>;
          const auto &candidate = std::get<T>(a.action);
          if constexpr (std::is_same_v<T, MathValue>)
            return candidate.identity == expected.identity &&
                   values(candidate.operands, expected.operands) &&
                   types.charge(candidate.literal.size() +
                                    expected.literal.size() + 1,
                                span) &&
                   candidate.literal == expected.literal &&
                   candidate.parameters == expected.parameters &&
                   statics(candidate.staticArguments, expected.staticArguments);
          else if constexpr (std::is_same_v<T, HelperCall>)
            return candidate.callee.index == expected.callee.index &&
                   values(candidate.operands, expected.operands) &&
                   statics(candidate.arguments, expected.arguments) &&
                   candidate.module == expected.module &&
                   candidate.owner == expected.owner &&
                   candidate.scopedArguments == expected.scopedArguments &&
                   candidate.descriptorArguments ==
                       expected.descriptorArguments;
          else if constexpr (std::is_same_v<T, Projection>)
            return types.charge(candidate.path.size() + expected.path.size() +
                                    1,
                                span) &&
                   candidate.input.index == expected.input.index &&
                   candidate.path == expected.path;
          else if constexpr (std::is_same_v<T, Construct>)
            return candidate.kind == expected.kind &&
                   candidate.alternative == expected.alternative &&
                   values(candidate.operands, expected.operands);
          else
            return false;
        },
        b.action);
    if (!agrees)
      return types.diagnostic ? false : refuse();
  }
  return true;
}
bool dataPreconditionsAgree(Semantics &types, const Declaration &actual,
                            const Declaration &written) {
  if (!chargeDataPreconditions(types, actual.dataPreconditions, actual.span) ||
      !chargeDataPreconditions(types, written.dataPreconditions, written.span))
    return false;
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "data preconditions differ from authored header",
                      written.span);
  };
  // Checked-project premises are authored and ordered. Additional inferred
  // data requirements belong to closed specialization and its own replay.
  if (actual.dataPreconditions != written.dataPreconditions)
    return refuse();
  auto sameSpan = [](Span a, Span b) {
    return a.source.index == b.source.index && a.begin == b.begin &&
           a.end == b.end;
  };
  for (unsigned i = 0; i < written.dataPreconditions.size(); ++i) {
    const auto &a = actual.dataPreconditions[i];
    const auto &b = written.dataPreconditions[i];
    if (!sameSpan(a.span, b.span) || !sameSpan(a.left.span, b.left.span) ||
        !sameSpan(a.right.span, b.right.span))
      return refuse();
  }
  return true;
}
bool consumerRequirementsAgree(Semantics &types, const Declaration &actual,
                               const Declaration &written) {
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "consumer requirements differ from authored header",
                      actual.span);
  };
  if (actual.consumerRequirements.size() != written.consumerRequirements.size())
    return refuse();
  for (unsigned i = 0; i < written.consumerRequirements.size(); ++i) {
    const auto &a = actual.consumerRequirements[i];
    const auto &b = written.consumerRequirements[i];
    if (auto error = chargeConsumerRequirement(a, types.work))
      return types.accept(std::move(error), actual.span);
    if (a.reference != b.reference || a.arguments != b.arguments ||
        a.span.source.index != b.span.source.index ||
        a.span.begin != b.span.begin || a.span.end != b.span.end)
      return refuse();
  }
  return true;
}
bool requiredAdmissionsIncluded(Semantics &types, const Declaration &actual,
                                const Declaration &written, bool exact) {
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "signature admissions differ from authored header",
                      actual.span);
  };
  // Reconstruct signature-derived boundary premises, rather than accepting
  // candidate premises or permitting their omission. Defined bodies may add
  // derived obligations; member inclusion independently checks those as goals.
  auto admissionKeys = [&](const Declaration &declaration,
                           std::set<std::pair<Boundary, std::string>> &keys) {
    for (const auto &obligation : declaration.admissions) {
      if (!types.chargeType(obligation.type, declaration.span) ||
          !types.charge(obligation.calls.size() + 1, declaration.span))
        return false;
      keys.emplace(obligation.boundary, typeIdentity(obligation.type));
    }
    return true;
  };
  std::set<std::pair<Boundary, std::string>> actualAdmissions,
      writtenAdmissions;
  if (!admissionKeys(actual, actualAdmissions) ||
      !admissionKeys(written, writtenAdmissions))
    return false;
  if (!std::includes(actualAdmissions.begin(), actualAdmissions.end(),
                     writtenAdmissions.begin(), writtenAdmissions.end()) ||
      (exact && actualAdmissions != writtenAdmissions))
    return refuse();
  return true;
}
template <typename Header>
bool headerPremisesAgree(Semantics &types, const CheckedStorage &storage,
                         const Declaration &actual, const Header &written,
                         bool permitsInference) {
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "static premises differ from authored header",
                      written.span);
  };
  if (!chargePremiseParameters(types, actual.parameters, actual.span) ||
      !chargePremiseParameters(types, written.parameters, written.span) ||
      !chargePremiseBounds(types, actual.bounds, actual.permissionBounds,
                           actual.capabilityBounds, actual.span) ||
      !chargePremiseBounds(types, written.bounds, written.permissionBounds,
                           written.capabilityBounds, written.span))
    return false;
  if (actual.generated || actual.id.index != written.id.index ||
      actual.module.index != written.module.index ||
      actual.qualifiedName != written.qualifiedName ||
      bool(actual.parent) != bool(written.parent) ||
      (actual.parent && actual.parent->index != written.parent->index) ||
      actual.parameters.size() != written.parameters.size())
    return refuse();
  for (unsigned i = 0; i < actual.parameters.size(); ++i) {
    const auto &a = actual.parameters[i], &b = written.parameters[i];
    if (a.name != b.name || a.atom != b.atom || a.sort != b.sort ||
        a.domainSort != b.domainSort || a.arguments != b.arguments ||
        bool(a.interface) != bool(b.interface) ||
        (a.interface && a.interface->index != b.interface->index) ||
        !(a.permissions == b.permissions))
      return refuse();
  }
  // Replay includes signature inference, not just written bounds. Bodies can
  // append obligations (or strengthen an inferred usage leaf) only where the
  // authored declaration permits inference. Origin is authenticated below;
  // conformance separately checks additions as goals. Abstract/explicit
  // contracts must match the independently reconstructed product exactly.
  auto boundsAgree = [&](const auto &candidate, const auto &expected,
                         auto agrees) {
    if (candidate.size() < expected.size())
      return false;
    for (unsigned i = 0; i < expected.size(); ++i)
      if (candidate[i].inferred != expected[i].inferred ||
          !agrees(candidate[i], expected[i]))
        return false;
    for (unsigned i = expected.size(); i < candidate.size(); ++i)
      if (!permitsInference || !candidate[i].inferred)
        return false;
    return true;
  };
  auto sameNatural = [](const auto &a, const auto &b) {
    return a.lhs == b.lhs && a.rhs == b.rhs;
  };
  auto samePermission = [](const auto &a, const auto &b) {
    return a.type == b.type && a.permissions == b.permissions;
  };
  auto sameCapability = [](const auto &a, const auto &b) {
    return a.predicate == b.predicate && a.arguments == b.arguments;
  };
  if (!boundsAgree(actual.bounds, written.bounds, sameNatural) ||
      !boundsAgree(actual.permissionBounds, written.permissionBounds,
                   [&](const auto &a, const auto &b) {
                     return a.type == b.type &&
                            (permitsInference && b.inferred
                                 ? a.permissions.includes(b.permissions)
                                 : a.permissions == b.permissions);
                   }) ||
      !boundsAgree(actual.capabilityBounds, written.capabilityBounds,
                   sameCapability))
    return refuse();
  // Eligibility authorizes inference, not a candidate-supplied premise. Match
  // the inferred subsequence to the immutable original source-check product.
  // This also authenticates strengthening of a signature-inferred usage leaf.
  if (!storage.inferredHeaderPremises)
    return refuse();
  if (!types.charge(Log2_64_Ceil(storage.inferredHeaderPremises->size() + 1) +
                        1,
                    written.span))
    return false;
  auto found = storage.inferredHeaderPremises->find(written.id.index);
  const InferredHeaderPremises empty;
  const auto &inferred =
      found == storage.inferredHeaderPremises->end() ? empty : found->second;
  if (!chargePremiseBounds(types, inferred.naturals, inferred.permissions,
                           inferred.capabilities, written.span))
    return false;
  auto inferredAgree = [&](const auto &candidate, const auto &retained,
                           auto agrees) {
    size_t next = 0;
    for (const auto &bound : candidate) {
      if (!bound.inferred)
        continue;
      if (next == retained.size() || !agrees(bound, retained[next++]))
        return false;
    }
    return next == retained.size();
  };
  if (!inferredAgree(actual.bounds, inferred.naturals, sameNatural) ||
      !inferredAgree(actual.permissionBounds, inferred.permissions,
                     samePermission) ||
      !inferredAgree(actual.capabilityBounds, inferred.capabilities,
                     sameCapability))
    return refuse();
  // Explicit and abstract ceilings remain source exact; inferred body effects
  // belong to the existing independent body/effect checker.
  if (written.effectAllowance || written.abstract) {
    if (!types.charge((actual.effectAllowance
                           ? actual.effectAllowance->dependencies.size()
                           : 0) +
                          (written.effectAllowance
                               ? written.effectAllowance->dependencies.size()
                               : 0) +
                          1,
                      written.span))
      return false;
    if (actual.effectAllowance != written.effectAllowance)
      return refuse();
  }
  return true;
}
bool signatureAgrees(Semantics &types, const CheckedStorage &storage,
                     const Declaration &actual, const Declaration &written,
                     bool permitsInference) {
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "conformance signature differs from authored header",
                      actual.span);
  };
  if (!types.charge(actual.parameters.size() + actual.inputs.size() +
                        actual.outputs.size() + actual.bounds.size() +
                        actual.permissionBounds.size() +
                        actual.capabilityBounds.size() + 1,
                    actual.span))
    return false;
  if (actual.descriptorResult &&
      !types.chargeType(descriptorType(*actual.descriptorResult), actual.span,
                        /*complete=*/false))
    return false;
  if (actual.kind != written.kind || actual.abstract != written.abstract ||
      actual.completes != written.completes ||
      actual.associatedSort != written.associatedSort ||
      !(actual.permissions == written.permissions) ||
      actual.resource != written.resource || actual.sealed != written.sealed ||
      actual.domain != written.domain || actual.roles != written.roles ||
      actual.implementation != written.implementation ||
      actual.parameters.size() != written.parameters.size() ||
      actual.inputs.size() != written.inputs.size() ||
      actual.outputs.size() != written.outputs.size() ||
      actual.descriptorResult != written.descriptorResult)
    return refuse();
  if (actual.descriptorResult &&
      !types.chargeContract(*actual.descriptorResult, actual.span))
    return false;
  if (!headerPremisesAgree(types, storage, actual, written, permitsInference) ||
      !dataPreconditionsAgree(types, actual, written) ||
      !consumerRequirementsAgree(types, actual, written))
    return false;
  for (bool input : {true, false}) {
    const auto &a = input ? actual.inputs : actual.outputs;
    const auto &b = input ? written.inputs : written.outputs;
    for (unsigned i = 0; i < a.size(); ++i)
      if (a[i].name != b[i].name || a[i].type != b[i].type)
        return refuse();
  }
  if (!memberInputs(types, written, actual, {}, "source.scoped-witness"))
    return false;
  if (!requiredAdmissionsIncluded(types, actual, written,
                                  !actual.body || actual.abstract))
    return false;
  return true;
}
} // namespace
llvm::Error retainHeaderPremises(CheckedStorage &storage, Work &work) {
  if (storage.inferredHeaderPremises || storage.authoredHeaderPremises)
    return failure("source.scoped-witness",
                   "inferred premises already retained");
  if (auto error = chargePremiseIndex(storage, work))
    return error;
  Semantics types(storage.declarations, storage.assets, work);
  if (!types.charge(storage.declarations.size(), {}))
    return types.takeError();
  auto retained =
      std::make_shared<std::map<uint32_t, InferredHeaderPremises>>();
  for (const auto &decl : storage.declarations) {
    if (!chargePremiseBounds(types, decl.bounds, decl.permissionBounds,
                             decl.capabilityBounds, decl.span))
      return types.takeError();
    InferredHeaderPremises inferred;
    for (const auto &bound : decl.bounds)
      if (bound.inferred)
        inferred.naturals.push_back(bound);
    for (const auto &bound : decl.permissionBounds)
      if (bound.inferred)
        inferred.permissions.push_back(bound);
    for (const auto &bound : decl.capabilityBounds)
      if (bound.inferred)
        inferred.capabilities.push_back(bound);
    if (!inferred.naturals.empty() || !inferred.permissions.empty() ||
        !inferred.capabilities.empty()) {
      if (!types.charge(Log2_64_Ceil(retained->size() + 1) + 1, decl.span))
        return types.takeError();
      retained->emplace(decl.id.index, std::move(inferred));
    }
  }
  if (!storage.writtenSources || !storage.declarationIndex)
    return failure("source.scoped-witness", "missing authored headers");
  uint64_t tokens = 0;
  for (const auto &source : storage.tokens)
    tokens += source.size();
  if (!types.charge(tokens, {}))
    return types.takeError();
  auto authored = storage.writtenSources->modules;
  if (auto error = expandLayoutSections(authored, work))
    return error;
  ContractHeaders headers{storage, types, {}, {}, true, {}};
  for (const auto &source : authored)
    if (!headers.collect(source, source.name, {}, 1))
      return types.takeError();
  if (!useRetainedProtocolHeaders(storage, headers, types))
    return types.takeError();
  CheckedStorage replay(storage.capture, storage.installation);
  auto reader = reconstructHeaders(storage, replay, headers, types, work);
  if (!reader)
    return types.takeError();
  auto premises =
      std::make_shared<std::map<uint32_t, AuthoredHeaderPremises>>();
  for (const auto &[id, source] : headers.sources) {
    auto &written = replay.declarations[id];
    if (!types.charge(Log2_64_Ceil(premises->size() + 1) + 1, source->span))
      return types.takeError();
    auto &header = (*premises)[id];
    header.id = written.id;
    header.module = written.module;
    header.parent = written.parent;
    header.qualifiedName = std::move(written.qualifiedName);
    header.span = source->span;
    header.abstract = source->abstract;
    header.permitsInference =
        reader->permitsContractInference(DeclarationId{id});
    header.parameters = std::move(written.parameters);
    header.bounds = std::move(written.bounds);
    header.permissionBounds = std::move(written.permissionBounds);
    header.capabilityBounds = std::move(written.capabilityBounds);
    header.effectAllowance = std::move(written.effectAllowance);
  }
  storage.inferredHeaderPremises = std::move(retained);
  storage.authoredHeaderPremises = std::move(premises);
  return Error::success();
}
llvm::Expected<std::map<uint32_t, std::vector<ServicePort>>>
replayHeaderContracts(const CheckedStorage &storage, Work &work) {
  if (auto error = chargePremiseIndex(storage, work))
    return std::move(error);
  std::map<uint32_t, std::vector<ServicePort>> ports;
  Semantics types(storage.declarations, storage.assets, work);
  if (!storage.writtenSources || !storage.declarationIndex ||
      !storage.authoredHeaderPremises)
    return failure("source.scoped-witness", "missing authored headers");
  if (!types.charge(storage.authoredHeaderPremises->size(), {}))
    return types.takeError();
  for (const auto &[id, header] : *storage.authoredHeaderPremises) {
    if (id >= storage.declarations.size() ||
        !headerPremisesAgree(types, storage, storage.declarations[id], header,
                             header.permitsInference))
      return types.diagnostic
                 ? types.takeError()
                 : failure("source.scoped-witness", "missing authored owner");
  }
  // Authored clauses own the obligation inventory. A candidate may erase both
  // its metadata and expansion, including in an unused standalone declaration.
  bool needed = false;
  std::vector<const SyntaxDeclaration *> pending;
  for (const auto &source : storage.writtenSources->modules)
    pending.push_back(&source);
  while (!pending.empty()) {
    const auto &source = *pending.back();
    pending.pop_back();
    if (!types.charge(source.members.size() + 1, source.span))
      return types.takeError();
    if (!types.charge(source.requirements.size(), source.span))
      return types.takeError();
    for (const auto &requirement : source.requirements)
      needed |= requirement.data.has_value() || !requirement.capability.empty();
    for (const auto &member : source.members)
      pending.push_back(&member);
  }
  for (const auto &[id, source] : storage.bodySources) {
    if (!types.charge(1, {}))
      return types.takeError();
    if (!source || !source->syntax)
      return failure("source.binding-witness", "missing body source syntax");
    needed |= !source->syntax->services.empty();
  }
  // An injected demand also requires authentication; it cannot create an
  // authored owner or turn off the source-derived inventory above.
  for (const auto &decl : storage.declarations) {
    if (!types.charge(1, decl.span))
      return types.takeError();
    needed |=
        !decl.consumerRequirements.empty() || !decl.dataPreconditions.empty();
  }
  if (!needed)
    return ports;
  uint64_t tokens = 0;
  for (const auto &source : storage.tokens)
    tokens += source.size();
  if (!types.charge(tokens, {}))
    return types.takeError();
  auto authored = storage.writtenSources->modules;
  if (auto error = expandLayoutSections(authored, work))
    return std::move(error);
  ContractHeaders headers{storage, types, {}, {}, true, {}};
  for (const auto &source : authored)
    if (!headers.collect(source, source.name, {}, 1))
      return types.takeError();
  if (!useRetainedProtocolHeaders(storage, headers, types))
    return types.takeError();
  CheckedStorage replay(storage.capture, storage.installation);
  auto reader = reconstructHeaders(storage, replay, headers, types, work);
  if (!reader)
    return types.takeError();
  for (const auto &[id, source] : headers.sources) {
    const auto &actual = storage.declarations[id];
    const auto &written = replay.declarations[id];
    if (!dataPreconditionsAgree(types, actual, written) ||
        !consumerRequirementsAgree(types, actual, written) ||
        !requiredAdmissionsIncluded(types, actual, written, false))
      return types.takeError();
    if (source->kind == Declaration::Kind::Protocol)
      ports.emplace(id, written.services);
  }
  for (const auto &decl : storage.declarations) {
    if (!types.charge(1, decl.span))
      return types.takeError();
    // Authored handlers were replayed with their inherited contracts above.
    // Generated API members have no authored clauses; specialization discharges
    // their selected protocol's demands.
    if (!headers.sources.count(decl.id.index) &&
        (!decl.consumerRequirements.empty() || !decl.dataPreconditions.empty()))
      return failure("source.scoped-witness",
                     "requirement has no authored header", decl.span);
  }
  return ports;
}
llvm::Error checkViewSources(const CheckedStorage &storage, Work &work) {
  Semantics types(storage.declarations, storage.assets, work);
  if (!storage.writtenSources || !storage.declarationIndex)
    return failure("source.view-witness", "missing authored View headers");
  // Replay obligations originate in immutable source, even when no candidate
  // still calls itself a View. Do not trust the mutable declaration inventory.
  bool needed = false;
  std::vector<const SyntaxDeclaration *> pending;
  for (const auto &source : storage.writtenSources->modules)
    pending.push_back(&source);
  while (!pending.empty()) {
    const auto &source = *pending.back();
    pending.pop_back();
    if (auto error = work.charge(source.members.size() + 1, source.span))
      return error;
    needed |= source.kind == Declaration::Kind::View;
    for (const auto &member : source.members)
      pending.push_back(&member);
  }
  if (!needed) {
    for (const auto &decl : storage.declarations) {
      if (auto error = work.charge(1, decl.span))
        return error;
      if (decl.kind == Declaration::Kind::View)
        return failure("source.view-witness",
                       "View has no authored declaration", decl.span);
    }
    return Error::success();
  }
  auto refuse = [](Span span) {
    return failure("source.view-witness",
                   "View differs from authored definition", span);
  };
  auto authored = storage.writtenSources->modules;
  if (auto error = expandLayoutSections(authored, work))
    return error;
  ContractHeaders headers{storage, types, {}, {}, false, {}};
  for (const auto &source : authored)
    if (!headers.collect(source, source.name, {}, 1))
      return types.takeError();
  for (const auto &decl : storage.declarations) {
    if (auto error = work.charge(1, decl.span))
      return error;
    auto header = headers.sources.find(decl.id.index);
    if (decl.kind == Declaration::Kind::View &&
        (header == headers.sources.end() ||
         header->second->kind != Declaration::Kind::View))
      return refuse(decl.span);
  }
  CheckedStorage replay(storage.capture, storage.installation);
  auto reader = reconstructHeaders(storage, replay, headers, types, work);
  if (!reader)
    return types.takeError();
  reader->beginViewReconstruction();
  for (const auto &[id, header] : headers.sources) {
    if (header->kind != Declaration::Kind::View || header->abstract)
      continue;
    auto found = storage.bodySources.find(id);
    if (found == storage.bodySources.end() || !found->second ||
        !found->second->syntax)
      return refuse(header->span);
    if (found->second->owner.index != id ||
        found->second->syntax->kind != Declaration::Kind::View)
      return refuse(header->span);
    reader->prepareViewReconstruction(DeclarationId{id},
                                      *found->second->syntax);
  }
  for (const auto &[id, header] : headers.sources) {
    if (header->kind != Declaration::Kind::View)
      continue;
    const auto &actual = storage.declarations[id];
    auto &written = replay.declarations[id];
    if (actual.kind != Declaration::Kind::View ||
        actual.abstract != header->abstract)
      return refuse(header->span);
    // Infer ordinary results from a fresh body, for explicit and omitted
    // annotations alike. Lazy View dependencies have all been reset above.
    if (!header->abstract && !reader->body(DeclarationId{id}, 1))
      return reader->types.takeError();
    if (!signatureAgrees(types, storage, actual, written,
                         reader->permitsContractInference(DeclarationId{id})))
      return types.takeError();
    if (actual.abstract)
      continue;
    auto found = storage.bodySources.find(id);
    if (found == storage.bodySources.end() || !found->second ||
        !found->second->syntax)
      return refuse(actual.span);
    const auto &source = *found->second->syntax;
    if (source.kind != Declaration::Kind::View)
      return refuse(actual.span);
    if (!actual.descriptorResult) {
      if (!actual.body || !written.body)
        return refuse(actual.span);
      if (!viewBodyAgrees(types, *actual.body, *written.body, actual.span))
        return types.takeError();
      continue;
    }
    if (!actual.descriptorDefinition || !written.descriptorDefinition)
      return refuse(actual.span);
    const auto &a = *actual.descriptorDefinition,
               &b = *written.descriptorDefinition;
    if (a.constructor != b.constructor || a.axis != b.axis ||
        a.result != b.result || a.bindings.size() != b.bindings.size())
      return refuse(actual.span);
    if (!viewBindingsAgree(types, a.bindings, b.bindings, actual.span))
      return types.takeError();
  }
  return Error::success();
}
llvm::Error checkModuleContracts(const CheckedStorage &storage, Work &work) {
  if (!storage.sources || !storage.declarationIndex)
    return failure("source.scoped-witness",
                   "invalid conformance source context");
  for (unsigned i = 0; i < storage.declarations.size(); ++i) {
    const auto &decl = storage.declarations[i];
    if (auto error = work.charge(decl.members.size() + 1, decl.span))
      return error;
    if (decl.id.index != i ||
        decl.span.source.index >= storage.sources->size() ||
        decl.module.index >= storage.declarations.size() ||
        (decl.parent && decl.parent->index >= storage.declarations.size()) ||
        llvm::any_of(decl.members, [&](auto id) {
          return id.index >= storage.declarations.size();
        }))
      return failure("source.scoped-witness",
                     "invalid conformance declaration identity", decl.span);
  }
  Semantics types(storage.declarations, storage.assets, work);
  auto verify = [&]() -> bool {
    if (!storage.writtenSources || !storage.declarationIndex)
      return types.fail("source.scoped-witness",
                        "missing conformance source headers", {});
    bool needsConformance =
        llvm::any_of(storage.declarations, [](const auto &decl) {
          return decl.implementation || !decl.conformance.empty();
        });
    std::function<bool(const SyntaxDeclaration &)> findImplementation =
        [&](const SyntaxDeclaration &source) {
          if (!types.charge(1, source.span))
            return false;
          needsConformance |= source.kind == Declaration::Kind::Module &&
                              source.definition.has_value();
          for (const auto &child : source.members)
            if (!findImplementation(child))
              return false;
          return true;
        };
    for (const auto &source : storage.writtenSources->modules)
      if (!findImplementation(source))
        return false;
    if (!needsConformance)
      return true;
    // Use the same section expansion on an independent authored snapshot;
    // written parameter groups do not create declaration namespaces.
    uint64_t tokens = 0;
    for (const auto &source : storage.tokens)
      tokens += source.size();
    if (!types.charge(tokens, {}))
      return false;
    auto authored = storage.writtenSources->modules;
    if (auto error = expandLayoutSections(authored, work))
      return types.accept(std::move(error));
    ContractHeaders headers{storage, types, {}, {}, false, {}};
    for (const auto &source : authored)
      if (!headers.collect(source, source.name, {}, 1))
        return false;
    if (!useRetainedProtocolHeaders(storage, headers, types))
      return false;
    std::vector<DeclarationId> implementations;
    for (unsigned index = 0; index < storage.declarations.size(); ++index) {
      const auto &decl = storage.declarations[index];
      if (!types.charge(1, decl.span))
        return false;
      if (decl.id.index != index)
        return types.fail("source.scoped-witness",
                          "invalid declaration identity", decl.span);
      auto source = headers.sources.find(decl.id.index);
      const bool implements =
          source != headers.sources.end() &&
          source->second->kind == Declaration::Kind::Module &&
          source->second->definition.has_value();
      if (implements)
        implementations.push_back(decl.id);
      if ((!implements && (!decl.conformance.empty() || decl.implementation)) ||
          (implements &&
           (!decl.implementation || decl.kind != Declaration::Kind::Module)))
        return types.fail("source.scoped-witness", "invalid conformance owner",
                          decl.span);
    }
    if (implementations.empty())
      return true;
    if (!storage.declarationIndex)
      return types.fail("source.scoped-witness",
                        "missing conformance namespaces", {});
    CheckedStorage replay(storage.capture, storage.installation);
    auto reader = reconstructHeaders(storage, replay, headers, types, work);
    if (!reader)
      return false;
    for (const auto &[index, source] : headers.sources)
      if (!reconstructInferredResult(types, storage, *source,
                                     replay.declarations[index]))
        return false;
    // Conformance is a proof query over reconstructed premises. In particular,
    // it has no inference hooks and cannot consult candidate alias, permission
    // or interface bounds to justify a candidate implementation requirement.
    if (auto error = chargeSemanticIndex(replay.declarations, work))
      return types.accept(std::move(error));
    Semantics premises(replay.declarations, replay.assets, work);
    std::set<uint32_t> reconstructed;
    std::function<bool(DeclarationId)> reconstruct = [&](DeclarationId id) {
      if (!reconstructed.insert(id.index).second)
        return true;
      auto source = headers.sources.find(id.index);
      if (source == headers.sources.end())
        return types.fail("source.scoped-witness", "missing authored contract",
                          {});
      const auto &actual = storage.declarations[id.index];
      // reconstructHeaders already authenticated the complete lexical tree.
      if (actual.parent && !reconstruct(*actual.parent))
        return false;
      if (!reader->reconstructSignature(id)) {
        if (reader->types.diagnostic)
          return types.accept(reader->types.takeError());
        return types.fail("source.scoped-witness", "invalid authored contract",
                          actual.span);
      }
      if (!signatureAgrees(premises, storage, actual,
                           replay.declarations[id.index],
                           reader->permitsContractInference(id)))
        return types.accept(premises.takeError());
      return true;
    };
    for (auto id : implementations) {
      const auto &module = storage.declarations[id.index];
      const auto &source = *headers.sources.at(id.index);
      auto selection = storage.declarationIndex->lookup(
          SourceAccess{id}, source.definition->name,
          {[&] { return types.charge(1, source.definition->span); }, {}});
      const auto *reference = std::get_if<ResolvedReference>(&selection);
      auto contract =
          reference ? std::optional(reference->target) : std::nullopt;
      if (!contract || contract->index >= storage.declarations.size())
        return types.fail("source.scoped-witness", "missing authored interface",
                          module.span);
      auto writtenInterface = headers.sources.find(contract->index);
      if (writtenInterface == headers.sources.end() ||
          writtenInterface->second->kind != Declaration::Kind::Interface)
        return types.fail("source.scoped-witness", "invalid authored interface",
                          module.span);
      const auto &interface = storage.declarations[contract->index];
      if (interface.kind != Declaration::Kind::Interface ||
          module.implementation->domain != interface.qualifiedName ||
          !reconstruct(*contract) || !reconstruct(id))
        return types.diagnostic
                   ? false
                   : types.fail("source.scoped-witness",
                                "module interface differs", module.span);
      const auto &requiredSources = writtenInterface->second->members;
      if (module.conformance.size() != requiredSources.size() ||
          interface.members.size() != requiredSources.size())
        return types.fail("source.scoped-witness",
                          "conformance edge coverage differs", module.span);
      std::set<uint32_t> providedIds;
      const auto &writtenModule = replay.declarations[id.index];
      const auto &writtenContract = replay.declarations[contract->index];
      auto bindings = premises.substitution(
          writtenContract, writtenModule.implementation->arguments);
      Type self(Type::Kind::Module, writtenModule.qualifiedName);
      for (const auto &p : writtenModule.parameters)
        self.arguments.push_back(parameterType(p));
      bindings.emplace("self:" + interface.qualifiedName, std::move(self));
      for (unsigned i = 0; i < requiredSources.size(); ++i) {
        const auto &requiredSource = requiredSources[i];
        auto requiredId = storage.declarationIndex->canonical(
            interface.qualifiedName + "::" + requiredSource.name);
        auto providedId = storage.declarationIndex->canonical(
            module.qualifiedName + "::" + requiredSource.name);
        const auto &edge = module.conformance[i];
        if (!requiredId || !providedId ||
            edge.required.index != requiredId->index ||
            edge.provided.index != providedId->index ||
            interface.members[i].index != requiredId->index ||
            edge.provided.index >= storage.declarations.size() ||
            !providedIds.insert(edge.provided.index).second)
          return types.fail("source.scoped-witness",
                            "conformance edge differs from source",
                            module.span);
        const auto &required = storage.declarations[requiredId->index];
        const auto &provided = storage.declarations[providedId->index];
        auto ownSource = headers.sources.find(providedId->index);
        if (ownSource == headers.sources.end() ||
            ownSource->second->kind != requiredSource.kind ||
            headers.parents.find(providedId->index) == headers.parents.end() ||
            headers.parents.at(providedId->index) != id.index ||
            !required.parent || required.parent->index != contract->index ||
            !provided.parent || provided.parent->index != id.index ||
            provided.module.index != id.index ||
            required.name != requiredSource.name ||
            provided.name != requiredSource.name ||
            required.kind != requiredSource.kind ||
            provided.kind != requiredSource.kind ||
            llvm::count_if(module.members, [&](auto member) {
              return member.index == providedId->index;
            }) != 1)
          return types.fail("source.scoped-witness",
                            "conformance member owner or kind differs",
                            module.span);
        if (!reconstruct(*requiredId) || !reconstruct(*providedId))
          return false;
        if (!memberContract(premises, writtenModule, writtenContract,
                            replay.declarations[requiredId->index], provided,
                            bindings, "source.scoped-witness"))
          return types.accept(premises.takeError());
      }
    }
    return true;
  };
  if (verify())
    return llvm::Error::success();
  if (types.diagnostic && types.diagnostic->code != "source.limit" &&
      types.diagnostic->code != "source.cancelled")
    types.diagnostic->code = "source.scoped-witness";
  return types.diagnostic
             ? types.takeError()
             : failure("source.scoped-witness", "conformance contract differs");
}
} // namespace zkc::language::detail
