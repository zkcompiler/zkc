#include "ConstructionWitness.h"
#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
struct Projection {
  std::optional<Type> provider, state;
  std::optional<ConstructionMethod> initializer;
  std::optional<ConstructionCodec> codec;
};
class ConstructionCheck {
  const CheckedStorage &storage;
  Checker &reader;
  Semantics &types;
  std::map<ReferenceSite, std::vector<uint32_t>, std::owner_less<ReferenceSite>>
      occurrences;
  std::map<uint32_t, Projection> projections;
  std::vector<unsigned> states, heights;

  bool refuse(Span span, StringRef message) {
    return types.fail("source.binding-witness", message, span);
  }
  const ReferenceRecord *occurrence(const Declaration &owner,
                                    const SyntaxType &syntax, StringRef slot,
                                    uint32_t &index) {
    const ReferenceRecord *result = nullptr;
    auto found = occurrences.find(syntax.referenceSite);
    if (found != occurrences.end())
      for (auto id : found->second) {
        const auto &record = (*storage.authoredReferences)[id];
        if (!types.charge(1, syntax.span))
          return nullptr;
        if (record.owner.index != owner.id.index ||
            record.position.slot != slot)
          continue;
        if (result || record.written != slot ||
            record.position.kind != ReferenceRoute::Construction ||
            record.position.ordinal != 0 ||
            record.target.index != record.reference.target.index ||
            record.provider.index != record.reference.provider.index ||
            record.target.index >= storage.declarations.size()) {
          refuse(syntax.span, "invalid construction reference occurrence");
          return nullptr;
        }
        result = &record;
        index = id;
      }
    if (!result)
      refuse(syntax.span, "missing construction reference occurrence");
    return result;
  }
  bool member(const Declaration &owner, const SyntaxType &syntax,
              const Type &provider, StringRef slot, CallableReference &result) {
    uint32_t index = 0;
    const auto *record = occurrence(owner, syntax, slot, index);
    if (!record)
      return false;
    // Written provenance stays in the author's environment. It is not a
    // dispatch result and is never rewritten with inherited actual arguments.
    if (!record->reference.abstract ||
        record->reference.abstract->module != provider)
      return refuse(syntax.span, "construction provider occurrence differs");
    if (!types.charge(record->reference.path.size() + 1, syntax.span))
      return false;
    result = {record->target, provider, record->reference, index};
    return true;
  }
  bool method(const Declaration &owner, const SyntaxType &syntax,
              const Type &provider, StringRef slot,
              ConstructionMethod &result) {
    if (!member(owner, syntax, provider, slot, result.target))
      return false;
    const auto &function =
        storage.declarations[result.target.declaration.index];
    if (function.kind != Declaration::Kind::Local || !function.parent ||
        function.parent->index >= storage.declarations.size() ||
        function.parameters.size() !=
            storage.declarations[function.parent->index].parameters.size())
      return refuse(syntax.span, "construction member contract differs");
    auto bindings =
        types.boundMemberSubstitution(function, provider, syntax.span);
    if (!bindings)
      return false;
    for (const auto &parameter : function.parameters) {
      auto found = bindings->find(parameter.atom);
      if (found == bindings->end())
        return refuse(syntax.span,
                      "construction member arguments are incomplete");
      if (!types.chargeType(found->second, syntax.span))
        return false;
      result.arguments.push_back(found->second);
    }
    return true;
  }
  bool chargeProjection(const Projection &projection, Span span) {
    auto method = [&](const ConstructionMethod &value) {
      if (!types.charge(value.target.reference.path.size() + 1, span) ||
          (value.target.module &&
           !types.chargeType(*value.target.module, span)))
        return false;
      for (const auto &argument : value.arguments)
        if (!types.chargeType(argument, span))
          return false;
      return true;
    };
    for (auto *value : {&projection.provider, &projection.state})
      if (*value && !types.chargeType(**value, span))
        return false;
    if (projection.initializer && !method(*projection.initializer))
      return false;
    if (projection.codec) {
      const auto &codec = *projection.codec;
      if (!types.chargeType(codec.provider, span) ||
          !types.chargeType(codec.record, span))
        return false;
      for (auto *value : {&codec.initialize, &codec.write, &codec.finish})
        if (!method(*value))
          return false;
    }
    return true;
  }
  bool replace(Projection &projection, const Substitution &bindings,
               Span span) {
    auto term = [&](Type &value) {
      auto selected = types.substitute(value, bindings, span);
      if (!selected)
        return false;
      value = std::move(*selected);
      return true;
    };
    auto method = [&](ConstructionMethod &value) {
      if (!value.target.module || !term(*value.target.module))
        return false;
      for (auto &argument : value.arguments)
        if (!term(argument))
          return false;
      return true;
    };
    for (auto *value : {&projection.provider, &projection.state})
      if (*value && !term(**value))
        return false;
    if (projection.initializer && !method(*projection.initializer))
      return false;
    if (projection.codec) {
      auto &codec = *projection.codec;
      if (!term(codec.provider) || !term(codec.record))
        return false;
      for (auto *value : {&codec.initialize, &codec.write, &codec.finish})
        if (!method(*value))
          return false;
    }
    return true;
  }
  bool same(const ConstructionMethod &expected, const CallableReference &actual,
            ArrayRef<Type> arguments, Span span) {
    if (!types.charge(expected.target.reference.path.size() +
                          expected.arguments.size() + 1,
                      span))
      return false;
    return (expected.target.declaration.index == actual.declaration.index &&
            expected.target.module == actual.module &&
            expected.target.reference == actual.reference &&
            expected.target.authoredReference == actual.authoredReference &&
            ArrayRef<Type>(expected.arguments) == arguments) ||
           refuse(span, "construction callable projection differs");
  }
  bool check(DeclarationId id, unsigned depth) {
    if (id.index >= storage.declarations.size())
      return refuse({}, "construction source is outside declarations");
    const auto &decl = storage.declarations[id.index];
    if (depth > types.work.limits.typeDepth ||
        heights[id.index] > types.work.limits.typeDepth - depth)
      return types.fail("source.limit", "construction witness depth",
                        decl.span);
    if (!types.charge(1, decl.span))
      return false;
    if (states[id.index] == 2)
      return true;
    if (states[id.index] == 1)
      return refuse(decl.span, "cyclic construction source");
    auto source = storage.constructionSources.find(id.index);
    if (source == storage.constructionSources.end() || !source->second ||
        decl.id.index != id.index ||
        decl.kind != Declaration::Kind::Construction || !decl.construction)
      return refuse(decl.span, "missing authored construction projection");
    states[id.index] = 1;
    const auto &syntax = *source->second;
    const auto &actual = *decl.construction;
    Projection expected;
    std::optional<DeclarationId> parent;
    std::vector<Type> arguments;
    if (syntax.parent) {
      auto selected =
          reader.select(decl, syntax.parent->name, syntax.parent->span);
      if (!selected || selected->target.index >= storage.declarations.size())
        return types.diagnostic
                   ? false
                   : refuse(decl.span, "missing authored construction base");
      parent = selected->target;
      if (!check(*parent, depth + 1))
        return false;
      heights[id.index] = 1 + heights[parent->index];
      const auto &base = storage.declarations[parent->index];
      auto selectedArguments =
          reader.arguments(decl, base, syntax.parent->arguments,
                           syntax.parent->span, syntax.parent->labels);
      if (!selectedArguments)
        return false;
      arguments = std::move(*selectedArguments);
      const auto &inherited = projections.at(parent->index);
      if (!chargeProjection(inherited, decl.span))
        return false;
      expected = inherited;
      if (!replace(expected, types.substitution(base, arguments), decl.span))
        return false;
    }
    if (bool(parent) != bool(actual.parent) ||
        (parent && parent->index != actual.parent->index) ||
        arguments != actual.arguments)
      return refuse(decl.span, "construction base projection differs");
    if (syntax.provider) {
      auto provider = reader.type(decl, *syntax.provider);
      if (!provider)
        return false;
      if (provider->kind == Type::Kind::Module) {
        CallableReference state;
        if (expected.initializer ||
            !member(decl, *syntax.provider, *provider, "State", state))
          return types.diagnostic
                     ? false
                     : refuse(decl.span,
                              "construction replaces inherited provider");
        auto value = types.associated(*provider, state.declaration, decl.span);
        if (!value)
          return false;
        expected.provider = *provider;
        expected.state = std::move(*value);
        expected.initializer.emplace();
        if (!method(decl, *syntax.provider, *provider, "initialize",
                    *expected.initializer))
          return false;
      }
    }
    if (syntax.codec) {
      if (expected.codec)
        return refuse(decl.span, "construction replaces inherited codec");
      auto provider = reader.type(decl, *syntax.codec);
      if (!provider)
        return false;
      CallableReference record;
      if (!member(decl, *syntax.codec, *provider, "Record", record))
        return false;
      auto value = types.associated(*provider, record.declaration, decl.span);
      if (!value)
        return false;
      expected.codec.emplace();
      auto &codec = *expected.codec;
      codec.provider = *provider;
      codec.record = std::move(*value);
      if (!method(decl, *syntax.codec, *provider, "initialize",
                  codec.initialize) ||
          !method(decl, *syntax.codec, *provider, "write", codec.write) ||
          !method(decl, *syntax.codec, *provider, "finish", codec.finish))
        return false;
    }
    if (bool(expected.initializer) != bool(actual.initializer) ||
        bool(expected.codec) != bool(actual.codec) ||
        (expected.provider && expected.provider != actual.provider) ||
        (expected.state && expected.state != actual.state) ||
        (!expected.initializer && !actual.initializerArguments.empty()))
      return refuse(decl.span, "construction projection coverage differs");
    if (expected.initializer &&
        !same(*expected.initializer, *actual.initializer,
              actual.initializerArguments, decl.span))
      return false;
    if (expected.codec) {
      const auto &a = *expected.codec, &b = *actual.codec;
      if (a.provider != b.provider || a.record != b.record)
        return refuse(decl.span, "construction codec provider differs");
      for (auto [x, y] :
           {std::pair{&a.initialize, &b.initialize},
            std::pair{&a.write, &b.write}, std::pair{&a.finish, &b.finish}})
        if (!same(*x, y->target, y->arguments, decl.span))
          return false;
    }
    if (heights[id.index] > types.work.limits.typeDepth - depth)
      return types.fail("source.limit", "construction witness depth",
                        decl.span);
    projections.emplace(id.index, std::move(expected));
    states[id.index] = 2;
    return true;
  }

public:
  ConstructionCheck(const CheckedStorage &storage, Checker &reader)
      : storage(storage), reader(reader), types(reader.types),
        states(storage.declarations.size()), heights(states.size()) {}
  bool run() {
    for (uint32_t i = 0; i < storage.authoredReferences->size(); ++i) {
      const auto &record = (*storage.authoredReferences)[i];
      if (!types.charge(1, record.span))
        return false;
      if (record.route == ReferenceRoute::Construction) {
        if (!record.site)
          return refuse(record.span, "missing construction reference identity");
        occurrences[record.site].push_back(i);
      }
    }
    for (const auto &[index, source] : storage.constructionSources) {
      (void)source;
      if (!check(DeclarationId{index}, 1))
        return false;
    }
    return true;
  }
};
} // namespace
Error checkConstructionSources(const CheckedStorage &storage, Work &work) {
  for (const auto &decl : storage.declarations) {
    if (auto error = work.charge(1, decl.span))
      return error;
    if ((decl.kind == Declaration::Kind::Construction || decl.construction) &&
        !storage.constructionSources.count(decl.id.index))
      return failure("source.binding-witness", "missing construction source",
                     decl.span);
  }
  if (storage.constructionSources.empty())
    return Error::success();
  if (!storage.authoredReferences || !storage.declarationIndex)
    return failure("source.binding-witness", "missing construction authority");
  if (auto error = chargeSemanticIndex(storage.declarations, work))
    return error;
  // Read only static header terms in a private semantic view. Bodies and
  // conformance are never elaborated by this owner; their independent checks
  // remain prerequisites of the enclosing source witness.
  CheckedStorage replay(storage.capture, storage.installation);
  replay.declarations = storage.declarations;
  replay.assets = storage.assets;
  replay.sources = storage.sources;
  replay.declarationIndex = storage.declarationIndex;
  Checker reader(replay, work, SourceAccess{{0}});
  if (!ConstructionCheck(storage, reader).run())
    return reader.types.takeError();
  return Error::success();
}
} // namespace zkc::language::detail
