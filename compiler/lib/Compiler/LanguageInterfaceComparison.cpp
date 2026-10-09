#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
bool sameSpan(Span a, Span b) {
  return a.module.index == b.module.index && a.begin == b.begin &&
         a.end == b.end;
}
bool sameSelector(const SpecificationSelector &a,
                  const SpecificationSelector &b) {
  return a.output == b.output && a.port == b.port && a.role == b.role &&
         a.path == b.path && sameSpan(a.span, b.span);
}
StringRef clauseKind(SpecificationClause::Kind kind) {
  using K = SpecificationClause::Kind;
  switch (kind) {
  case K::Target:
    return "target";
  case K::Input:
    return "input";
  case K::Output:
    return "output";
  case K::Continuation:
    return "continuation";
  }
  llvm_unreachable("unknown clause kind");
}
class Comparison {
  const ClosedEntry &entry;
  const LanguageInterface &view;
  const Limits &limits;
  Layouts layouts;
  uint64_t remaining;
  Error failure = Error::success();
  std::set<std::pair<const Layout *, const InterfaceSchema *>> compared;
  std::map<std::string, unsigned> protocols, relations;
  bool fail(StringRef message) {
    if (!failure)
      failure = error("source.correspondence", message);
    return false;
  }
  bool charge(uint64_t amount) {
    if (failure)
      return false;
    if (amount > remaining) {
      failure =
          error("source.limit", "source interface comparison limit exceeded");
      return false;
    }
    remaining -= amount;
    return true;
  }
  bool text(StringRef a, StringRef b) {
    return charge(a.size() + b.size() + 1) &&
           (a == b || fail("interface spelling differs from checked source"));
  }
  bool fields(ArrayRef<LayoutField> source, ArrayRef<InterfaceField> actual,
              unsigned depth) {
    if (!charge(source.size() + actual.size() + 1))
      return false;
    if (source.size() != actual.size())
      return fail("logical field count differs");
    for (unsigned i = 0; i < source.size(); ++i)
      if (!text(source[i].name, actual[i].name) ||
          source[i].offset != actual[i].offset || !actual[i].schema ||
          !schema(*source[i].layout, *actual[i].schema, depth + 1))
        return fail("logical field mapping differs");
    return true;
  }
  bool schema(const Layout &source, const InterfaceSchema &actual,
              unsigned depth = 0) {
    if (!charge(1))
      return false;
    if (depth > limits.typeDepth) {
      failure = error("source.limit", "source interface schema depth exceeded");
      return false;
    }
    if (!compared.emplace(&source, &actual).second)
      return true;
    auto identity = typeIdentity(source.type);
    if (!charge(identity.size()))
      return false;
    if (!text(toHex(SHA256::hash(arrayRefFromStringRef(identity)), true),
              actual.identity) ||
        !text(spelling(source.type), actual.type) ||
        source.type.kind != actual.kind || source.custody != actual.custody ||
        !(source.permissions == actual.permissions) ||
        source.leaves.size() != actual.leaves.size() ||
        source.alternatives.size() != actual.alternatives.size())
      return fail("logical source schema differs");
    for (unsigned i = 0; i < source.leaves.size(); ++i)
      if (!source.leaves[i].data() ||
          !text(*source.leaves[i].data(), actual.leaves[i]))
        return fail("logical source leaf differs");
    if (!fields(source.fields, actual.fields, depth))
      return false;
    for (unsigned i = 0; i < source.alternatives.size(); ++i)
      if (!text(source.alternatives[i].name, actual.alternatives[i].name) ||
          !fields(source.alternatives[i].fields, actual.alternatives[i].fields,
                  depth))
        return false;
    return true;
  }
  std::shared_ptr<const Layout> layout(const Type &type) {
    auto result = layouts.get(type);
    if (!result) {
      failure = result.takeError();
      return {};
    }
    return *result;
  }
  bool slice(ArrayRef<unsigned> native, unsigned &flat, unsigned count) {
    if (!charge(native.size() + 1))
      return false;
    if (native.size() != count)
      return fail("source interface native arity differs");
    for (auto index : native)
      if (index != flat++)
        return fail("source interface native slice differs");
    return true;
  }
  bool ports(ArrayRef<Port> source, ArrayRef<InterfacePort> actual,
             unsigned &flat) {
    if (!charge(source.size() + actual.size() + 1))
      return false;
    if (source.size() != actual.size())
      return fail("logical source port count differs");
    for (unsigned i = 0; i < source.size(); ++i) {
      auto expected = layout(source[i].type);
      if (!expected)
        return false;
      if (!text(source[i].name, actual[i].name) ||
          source[i].roles != actual[i].roles || !actual[i].schema ||
          !schema(*expected, *actual[i].schema) ||
          !slice(actual[i].native, flat, expected->leaves.size()))
        return fail("logical source port differs");
    }
    return true;
  }
  bool selector(const Declaration &protocol,
                const SpecificationSelector &source,
                const InterfaceSelector &actual) {
    if (!charge(source.path.size() + actual.path.size() + 1))
      return false;
    if (source.output != actual.output || source.port != actual.port ||
        source.role != actual.role || source.path != actual.path)
      return fail(
          "source selector direction, port, path or participant differs");
    const auto &ports = source.output ? protocol.outputs : protocol.inputs;
    unsigned offset = 0;
    for (unsigned i = 0; i < source.port; ++i) {
      auto value = layout(ports[i].type);
      if (!value)
        return false;
      offset += value->leaves.size();
    }
    auto value = layout(ports[source.port].type);
    if (!value)
      return false;
    for (auto index : source.path) {
      if (index >= value->fields.size())
        return fail("checked selector has no layout field");
      offset += value->fields[index].offset;
      value = value->fields[index].layout;
    }
    return slice(actual.native, offset, value->leaves.size());
  }
  bool application(const Declaration &protocol,
                   const RelationApplication &source,
                   const InterfaceApplication &actual) {
    const auto &relation = entry.declarations()[source.relation.index];
    if (actual.relation >= view.relations.size() ||
        !text(relation.symbol, view.relations[actual.relation].symbol) ||
        source.operands.size() != actual.operands.size())
      return fail("source relation application differs");
    for (unsigned i = 0; i < source.operands.size(); ++i)
      if (!selector(protocol, source.operands[i], actual.operands[i]))
        return false;
    return true;
  }
  bool templateApplication(const RelationApplication &source,
                           const RelationApplication &closed) {
    if (!charge(source.operands.size() + closed.operands.size() + 1))
      return false;
    const auto &relation = entry.declarations()[closed.relation.index];
    if (!relation.origin || relation.origin->index != source.relation.index ||
        relation.staticArguments != closed.arguments ||
        source.operands.size() != closed.operands.size() ||
        !sameSpan(source.span, closed.span))
      return fail("closure changed the source relation application");
    for (unsigned i = 0; i < source.operands.size(); ++i)
      if (!sameSelector(source.operands[i], closed.operands[i]))
        return fail("closure changed a source selector");
    return true;
  }
  bool inventory() {
    auto saved = remaining;
    auto restore = llvm::scope_exit([&] { remaining = saved; });
    remaining = limits.work;
    using Start = std::pair<unsigned, unsigned>;
    std::map<Start, const Declaration *> blocks;
    std::set<unsigned> anonymous;
    for (const auto &decl : entry.project().declarations()) {
      if (!charge(1))
        return false;
      if (decl.specificationBlock) {
        auto span = *decl.specificationBlock;
        if (decl.kind != Declaration::Kind::Protocol ||
            span.module.index != decl.span.module.index ||
            span.begin < decl.span.begin || span.end > decl.span.end ||
            !blocks.emplace(Start{span.module.index, span.begin}, &decl).second)
          return fail("source specification block inventory differs");
      } else if (!decl.specifications.empty())
        return fail("source clauses have no specification block");
      auto subject = [&](const RelationApplication &application) {
        const auto &relation =
            entry.project().declarations()[application.relation.index];
        if (!relation.anonymous)
          return true;
        return (relation.parent && relation.parent->index == decl.id.index &&
                sameSpan(relation.span, application.span) &&
                anonymous.insert(relation.id.index).second) ||
               fail("inline predicate ownership differs");
      };
      for (const auto &clause : decl.specifications)
        if (!subject(clause.subject) ||
            (clause.residual && !subject(*clause.residual)))
          return false;
    }
    for (const auto &decl : entry.project().declarations())
      if (decl.anonymous && !anonymous.count(decl.id.index))
        return fail("source omitted an inline predicate binding");
    auto sources = entry.project().capture().sources();
    for (unsigned module = 0; module < sources.size(); ++module) {
      SmallVector<const Token *> tokens;
      for (const auto &token : entry.project().tokens({module})) {
        if (!charge(1))
          return false;
        if (token.kind != TokenKind::Whitespace &&
            token.kind != TokenKind::Comment && token.kind != TokenKind::End)
          tokens.push_back(&token);
      }
      auto spelling = [&](unsigned index) -> StringRef {
        if (index >= tokens.size())
          return {};
        auto span = tokens[index]->span;
        return StringRef(sources[module].text).slice(span.begin, span.end);
      };
      for (unsigned i = 0; i < tokens.size(); ++i) {
        if (tokens[i]->kind != TokenKind::Word || spelling(i) != "spec")
          continue;
        auto found = blocks.find({module, tokens[i]->span.begin});
        if (found == blocks.end() || spelling(i + 1) != "{")
          return fail("source omitted a specification block");
        const auto &decl = *found->second;
        unsigned cursor = i + 2;
        for (const auto &clause : decl.specifications) {
          if (cursor >= tokens.size() || !charge(1) ||
              clause.span.module.index != module ||
              clause.span.begin != tokens[cursor]->span.begin ||
              spelling(cursor) != clauseKind(clause.kind) ||
              spelling(cursor + 1) != clause.name ||
              spelling(cursor + 2) != "=")
            return fail("source clause inventory differs from captured tokens");
          while (cursor < tokens.size() &&
                 tokens[cursor]->span.end < clause.span.end) {
            if (!charge(1))
              return false;
            ++cursor;
          }
          if (cursor >= tokens.size() || spelling(cursor) != ";" ||
              tokens[cursor]->span.end != clause.span.end)
            return fail("source clause span does not cover its tokens");
          ++cursor;
        }
        if (cursor >= tokens.size() || spelling(cursor) != "}" ||
            tokens[cursor]->span.end != decl.specificationBlock->end)
          return fail("source omitted clauses or changed its block span");
        blocks.erase(found);
        i = cursor;
      }
    }
    return blocks.empty() || fail("source invented a specification block");
  }
  bool protocol(const Declaration &decl, const InterfaceProtocol &actual) {
    if (decl.roles != actual.roles)
      return fail("source participant roster differs");
    unsigned input = 0, output = 0;
    if (!ports(decl.inputs, actual.inputs, input) ||
        !ports(decl.outputs, actual.outputs, output))
      return false;
    if (decl.services.size() != actual.services.size())
      return fail("source service count differs");
    for (unsigned i = 0; i < decl.services.size(); ++i) {
      const auto &s = decl.services[i];
      const auto &a = actual.services[i];
      if (!text(s.name, a.name) || !text(s.contract, a.contract) ||
          s.owner != a.owner || a.native != input++)
        return fail("source service binding differs");
    }
    const auto &source = entry.project().declarations()[decl.origin->index];
    if (source.specifications.size() != decl.specifications.size() ||
        actual.clauses.size() != source.specifications.size())
      return fail("source clause inventory was changed or omitted");
    for (unsigned i = 0; i < source.specifications.size(); ++i) {
      const auto &s = source.specifications[i], &c = decl.specifications[i];
      const auto &a = actual.clauses[i];
      if (!text(s.name, c.name) || !text(s.name, a.name) || s.kind != c.kind ||
          s.kind != a.kind || !sameSpan(s.span, c.span) ||
          bool(s.residual) != bool(c.residual) ||
          bool(s.residual) != bool(a.residual) ||
          bool(s.decision) != bool(c.decision) ||
          bool(s.decision) != bool(a.decision))
        return fail("source clause shape differs");
      if (!templateApplication(s.subject, c.subject) ||
          !application(decl, c.subject, a.subject))
        return false;
      if (s.residual && (!templateApplication(*s.residual, *c.residual) ||
                         !application(decl, *c.residual, *a.residual)))
        return false;
      if (s.decision && (!sameSelector(*s.decision, *c.decision) ||
                         !selector(decl, *c.decision, *a.decision)))
        return fail("source decision differs");
    }
    return true;
  }
  bool setups() {
    const auto &source = entry.entry().setups;
    if (!charge(source.size() + view.setups.size() + 1))
      return false;
    if (source.size() != view.setups.size())
      return fail("source setup slot count differs");
    for (unsigned i = 0; i < source.size(); ++i) {
      const auto &s = source[i];
      const auto &a = view.setups[i];
      if (!text(s.name, a.name) || s.inputs.size() != a.inputs.size())
        return fail("source setup slot differs");
      for (unsigned j = 0; j < s.inputs.size(); ++j) {
        if (!charge(s.inputs[j].path.size() + a.inputs[j].path.size() + 1))
          return false;
        if (s.inputs[j].port != a.inputs[j].port ||
            s.inputs[j].path != a.inputs[j].path)
          return fail("source setup selector differs");
        auto selected = layouts.selectInput(entry.protocol(), s.inputs[j]);
        if (!selected) {
          failure = selected.takeError();
          return false;
        }
        auto offset = selected->offset;
        if (!slice(a.inputs[j].native, offset, selected->layout->leaves.size()))
          return false;
      }
    }
    return true;
  }
  bool job() {
    const auto &source = entry.entry().proof;
    if (bool(source) != bool(view.proof))
      return fail("source Entry job kind differs");
    if (!source)
      return true;
    const auto &actual = *view.proof;
    if (!charge(source->publicInputs.size() + actual.publicInputs.size() + 1))
      return false;
    return (source->construction == actual.construction &&
            source->prover == actual.prover &&
            source->verifier == actual.verifier &&
            source->publicInputs == actual.publicInputs &&
            source->target == actual.target &&
            source->service == actual.service &&
            bool(source->completion) == bool(actual.completion) &&
            (!source->completion ||
             selector(entry.protocol(), *source->completion,
                      *actual.completion)) &&
            text(source->suite, actual.suite) &&
            selector(entry.protocol(), source->acceptance,
                     actual.acceptance)) ||
           fail("source Entry choices differ");
  }
  bool relation(const Declaration &decl, const InterfaceRelation &actual) {
    const auto &definition = *decl.relation;
    const auto &source =
        *entry.project().declarations()[decl.origin->index].relation;
    if (source.kind != definition.kind ||
        source.purposes != definition.purposes ||
        source.asset != definition.asset ||
        source.externalKind != definition.externalKind ||
        source.key != definition.key ||
        source.revision != definition.revision ||
        actual.kind != definition.kind ||
        actual.inputs.size() != decl.inputs.size())
      return fail("source relation definition differs");
    unsigned flat = 0;
    for (unsigned i = 0; i < decl.inputs.size(); ++i) {
      auto expected = layout(decl.inputs[i].type);
      if (!expected)
        return false;
      const auto &input = actual.inputs[i];
      if (!text(decl.inputs[i].name, input.name) ||
          definition.purposes[i] != input.purpose || !input.schema ||
          !schema(*expected, *input.schema) ||
          !slice(input.native, flat, expected->leaves.size()))
        return fail("source relation formal differs");
    }
    using K = RelationDefinition::Kind;
    if (definition.kind == K::Formula)
      return (actual.formula && !actual.asset &&
              *actual.formula == formulaSymbol(decl) &&
              actual.externalKind == "zkc.language.formula/0" &&
              actual.key == decl.symbol) ||
             fail("source predicate binding differs");
    if (definition.kind == K::Opaque)
      return (!actual.formula && !actual.asset &&
              text(definition.externalKind, actual.externalKind) &&
              text(definition.key, actual.key) &&
              text(definition.revision, actual.revision)) ||
             fail("source opaque relation identity differs");
    const auto &asset = entry.project().assets()[*definition.asset];
    return (!actual.formula && actual.asset &&
            actual.asset->identity() == asset.identity() &&
            actual.key == asset.identity() && actual.revision == "0" &&
            actual.externalKind == (definition.kind == K::R1CS
                                        ? "zkc.relation.r1cs/0"
                                        : "zkc.relation.air/0")) ||
           fail("source captured relation identity differs");
  }

public:
  Comparison(const ClosedEntry &entry, const LanguageInterface &view,
             const Limits &limits)
      : entry(entry), view(view), limits(limits), layouts(entry, limits),
        remaining(limits.work) {
    (void)!!failure;
  }
  Error run() {
    if (!inventory())
      return std::move(failure);
    if (view.capture != entry.project().capture().identity() ||
        view.entry != entry.entry().qualifiedName ||
        view.selected >= view.protocols.size() ||
        view.protocols[view.selected].symbol != entry.protocol().symbol)
      return error("source.correspondence",
                   "source capture or selected Entry differs");
    for (unsigned i = 0; i < view.protocols.size(); ++i)
      if (!charge(view.protocols[i].symbol.size() + 1) ||
          !protocols.emplace(view.protocols[i].symbol, i).second) {
        fail("duplicate source interface protocol");
        return std::move(failure);
      }
    for (unsigned i = 0; i < view.relations.size(); ++i)
      if (!charge(view.relations[i].symbol.size() + 1) ||
          !relations.emplace(view.relations[i].symbol, i).second) {
        fail("duplicate source interface relation");
        return std::move(failure);
      }
    for (const auto &decl : entry.declarations()) {
      if (!charge(1))
        return std::move(failure);
      if (!decl.origin)
        continue;
      if (decl.kind == Declaration::Kind::Protocol) {
        auto found = protocols.find(decl.symbol);
        if (found == protocols.end())
          return error("source.correspondence",
                       "omitted source protocol interface");
        if (!protocol(decl, view.protocols[found->second]))
          return std::move(failure);
        protocols.erase(found);
      } else if (decl.relation) {
        auto found = relations.find(decl.symbol);
        if (found == relations.end())
          return error("source.correspondence",
                       "omitted source relation interface");
        if (!relation(decl, view.relations[found->second]))
          return std::move(failure);
        relations.erase(found);
      }
    }
    if (!job() || !setups())
      return std::move(failure);
    if (!protocols.empty() || !relations.empty())
      return error("source.correspondence",
                   "extra source interface definitions");
    return Error::success();
  }
};
} // namespace
Error compareInterface(const ClosedEntry &entry, const LanguageInterface &view,
                       const Limits &limits) {
  if (auto error = checkLimits(limits))
    return error;
  return Comparison(entry, view, limits).run();
}
} // namespace zkc::language
