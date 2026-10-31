#include "LanguageInterface.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/SourceTerms.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Syntax/Syntax.h"
#include "zkc/Translation/Entry.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
bool sameSpan(Span a, Span b) {
  return a.source.index == b.source.index && a.begin == b.begin &&
         a.end == b.end;
}
bool sameSelector(const SpecificationSelector &a,
                  const SpecificationSelector &b) {
  return a.anchor == b.anchor && a.output == b.output && a.port == b.port &&
         a.role == b.role && a.path == b.path && sameSpan(a.span, b.span);
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
          source[i].maximumRows != actual[i].maximumRows ||
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
    bool record = source.type.kind == Type::Kind::LogicalRecord;
    if (!text(toHex(SHA256::hash(arrayRefFromStringRef(identity)), true),
              actual.identity) ||
        !text(spelling(source.type), actual.type) ||
        source.type.kind != actual.kind || source.custody != actual.custody ||
        source.constructible != actual.constructible ||
        !(source.permissions == actual.permissions) ||
        ((source.type.kind == Type::Kind::Oracle ||
          source.type.kind == Type::Kind::OracleSequence)
             ? !actual.oracle || !actual.leaves.empty()
             : actual.oracle.has_value() || actual.maximum.has_value() ||
                   actual.oracleData ||
                   (record ? !actual.leaves.empty()
                           : source.leaves.size() != actual.leaves.size())) ||
        source.alternatives.size() != actual.alternatives.size())
      return fail("logical source schema differs");
    if (actual.oracle) {
      if (source.leaves.size() != 1 || !source.leaves[0].oracle())
        return fail("logical oracle schema differs");
      const auto &logical = *source.leaves[0].oracle();
      const auto &kind = logical.kind;
      if (logical.maximum != actual.maximum ||
          !text(kind.identity, actual.oracle->kind) ||
          kind.arguments != actual.oracle->arguments || !source.oracleData ||
          !actual.oracleData ||
          !schema(*source.oracleData, *actual.oracleData, depth + 1))
        return fail("logical oracle kind, capacity or data schema differs");
    } else if (!record) {
      for (unsigned i = 0; i < source.leaves.size(); ++i)
        if (!source.leaves[i].data() ||
            !text(*source.leaves[i].data(), actual.leaves[i]))
          return fail("logical source leaf differs");
    }
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
      auto observed = layouts.protocolPort(source[i]);
      if (!observed) {
        failure = observed.takeError();
        return false;
      }
      if (!text(source[i].name, actual[i].name) ||
          source[i].roles != actual[i].roles || !actual[i].schema ||
          !schema(*expected, *actual[i].schema) ||
          !slice(actual[i].native, flat, observed->size()))
        return fail("logical source port differs");
      if (source[i].oracle.has_value() != actual[i].oracle.has_value())
        return fail("oracle role family is missing or invented");
      if (source[i].oracle) {
        const auto &before = *source[i].oracle;
        const auto &after = *actual[i].oracle;
        std::optional<uint64_t> maximum;
        if (before.maximumRows)
          maximum = before.maximumRows->dimension.closedValue();
        if (before.holder != after.holder || maximum != after.maximumRows)
          return fail("oracle holder or maximum differs");
      }
    }
    return true;
  }
  bool selector(const Declaration &protocol,
                const SpecificationSelector &source,
                const InterfaceSelector &actual) {
    if (!charge(source.path.size() + actual.path.size() + 1))
      return false;
    if (source.anchor != actual.anchor || source.output != actual.output ||
        source.port != actual.port || source.role != actual.role ||
        source.path != actual.path)
      return fail(
          "source selector direction, port, path or participant differs");
    auto selected = layouts.select(protocol, source);
    if (!selected) {
      failure = selected.takeError();
      return false;
    }
    unsigned offset = selected->offset;
    return slice(actual.native, offset,
                 source.anchor ? 1 : selected->layout->leaves.size());
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
    std::map<Start, const PendingSpecification *> pending;
    for (const auto &spec : entry.project().pendingSpecifications()) {
      if (!charge(1) ||
          !pending
               .emplace(Start{spec.span.source.index, spec.span.begin}, &spec)
               .second)
        return fail("pending specification inventory differs");
    }
    std::map<Start, const Declaration *> blocks;
    std::map<Start, const SourceClaimBlock *> claimBlocks;
    std::set<unsigned> anonymous;
    for (const auto &decl : entry.project().declarations()) {
      if (!charge(1))
        return false;
      for (const auto &block : decl.sourceClaims) {
        auto span = block.span;
        if (!charge(1) ||
            (decl.kind != Declaration::Kind::Module &&
             decl.kind != Declaration::Kind::Entry) ||
            span.source.index != decl.span.source.index ||
            span.begin < decl.span.begin || span.end > decl.span.end ||
            !claimBlocks.emplace(Start{span.source.index, span.begin}, &block)
                 .second)
          return fail("source claim block inventory differs");
      }
      if (decl.specificationBlock) {
        auto span = *decl.specificationBlock;
        if (decl.kind != Declaration::Kind::Protocol ||
            span.source.index != decl.span.source.index ||
            span.begin < decl.span.begin || span.end > decl.span.end ||
            !blocks.emplace(Start{span.source.index, span.begin}, &decl).second)
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
      if (decl.anonymous && decl.relation && !anonymous.count(decl.id.index))
        return fail("source omitted an inline predicate binding");
    auto sources = entry.project().sources();
    for (unsigned module = 0; module < sources.size(); ++module) {
      if (entry.project().capture().format() == "zkc-layout" &&
          sources[module].origin == SourceOrigin::Captured) {
        syntax::Budget budget;
        budget.bytes = limits.fileBytes;
        budget.tokens = limits.tokens;
        budget.tokenBytes = limits.tokenBytes;
        budget.identifierBytes = limits.identifierBytes;
        budget.depth = limits.parseDepth;
        budget.work = remaining;
        auto tree = syntax::parseHeaders(source::Revision(sources[module]),
                                         {module}, budget);
        if (!charge(tree.workUsed()) ||
            tree.status() != syntax::Status::Complete ||
            !tree.diagnostics().empty())
          return fail(
              "captured layout headers could not be read independently");
        for (unsigned i = 0; i < tree.nodes().size(); ++i) {
          if (!charge(1))
            return false;
          syntax::NodeId id{i};
          if (tree.node(id).kind != syntax::Kind::Spec)
            continue;
          auto span = tree.span(id);
          auto found = pending.find({module, span.begin});
          if (found == pending.end() || !sameSpan(found->second->span, span))
            return fail("source omitted or changed a pending specification");
          const auto &spec = *found->second;
          auto declarations = entry.project().declarations();
          if (spec.module.index >= declarations.size() ||
              spec.protocol.index >= declarations.size() ||
              declarations[spec.protocol.index].kind !=
                  Declaration::Kind::Protocol)
            return fail("pending specification has no protocol subject");
          const auto &owner = declarations[spec.module.index];
          if (owner.span.source.index != module ||
              span.begin < owner.span.begin || span.end > owner.span.end)
            return fail("pending specification escaped its source owner");
          auto children = tree.children(id);
          SmallVector<StringRef, 4> head;
          for (unsigned t = tree.node(id).firstToken;
               t < tree.node(id).lastToken && head.size() < 3; ++t) {
            auto token = tree.tokens()[t];
            if (!token.trivia() && !token.synthetic())
              head.push_back(tree.text(token));
          }
          bool visible = head.front() == "pub";
          bool named = head[visible ? 2 : 1] != "for";
          if (named ? tree.text(children.front()) != spec.name
                    : !spec.name.empty())
            return fail("pending specification name differs");
          if (visible != spec.isPublic)
            return fail("pending specification visibility differs");
          unsigned subjectIndex = named ? 1 : 0;
          if (tree.node(children[subjectIndex]).kind ==
              syntax::Kind::StaticParameters)
            ++subjectIndex;
          auto subject = children[subjectIndex];
          auto subjectText = tree.text(subject);
          bool localName = tree.node(subject).kind == syntax::Kind::Name &&
                           !subjectText.contains("::");
          const auto &protocol = declarations[spec.protocol.index];
          bool localOwner = !named && localName && protocol.parent &&
                            protocol.parent->index == spec.module.index;
          if (localOwner != spec.owner ||
              (spec.owner && protocol.name != subjectText))
            return fail("pending specification owner attachment differs");
          pending.erase(found);
        }
        continue;
      }
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
        // Claims are a separate, non-executable construct. Consume only a
        // retained claim block at this exact source address; do not relax the
        // independent inventory of protocol relation specifications below.
        auto claimBlock = claimBlocks.find({module, tokens[i]->span.begin});
        if (claimBlock != claimBlocks.end()) {
          const auto &block = *claimBlock->second;
          unsigned cursor = i + 1;
          while (cursor < tokens.size() && spelling(cursor) != "{") {
            if (!charge(1))
              return false;
            ++cursor;
          }
          if (cursor >= tokens.size())
            return fail("source claim block has no opening brace");
          ++cursor;
          for (const auto &claim : block.claims) {
            if (cursor >= tokens.size() || !charge(1) ||
                claim.span.source.index != module ||
                claim.span.begin != tokens[cursor]->span.begin ||
                spelling(cursor) != claim.label || spelling(cursor + 1) != ":")
              return fail(
                  "source claim inventory differs from captured tokens");
            while (cursor < tokens.size() &&
                   tokens[cursor]->span.end < claim.span.end) {
              if (!charge(1))
                return false;
              ++cursor;
            }
            if (cursor >= tokens.size() || spelling(cursor) != ";" ||
                tokens[cursor]->span.end != claim.span.end)
              return fail("source claim span does not cover its tokens");
            ++cursor;
          }
          if (cursor >= tokens.size() || spelling(cursor) != "}" ||
              tokens[cursor]->span.end != block.span.end)
            return fail("source omitted claims or changed its block span");
          claimBlocks.erase(claimBlock);
          i = cursor;
          continue;
        }
        auto found = blocks.find({module, tokens[i]->span.begin});
        if (found == blocks.end() || spelling(i + 1) != "{")
          return fail("source omitted a specification block");
        const auto &decl = *found->second;
        unsigned cursor = i + 2;
        for (const auto &clause : decl.specifications) {
          if (cursor >= tokens.size() || !charge(1) ||
              clause.span.source.index != module ||
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
    return (blocks.empty() && claimBlocks.empty() && pending.empty()) ||
           fail("source invented a specification or claim block");
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
    const auto &source = entry.entry().proof();
    if (bool(source) != bool(view.proof))
      return fail("source Entry job kind differs");
    if (!source)
      return true;
    const auto &actual = *view.proof;
    if (!charge(source->publicInputs.size() + actual.publicInputs.size() + 1))
      return false;
    return (source->construction == actual.construction &&
            source->format == actual.format &&
            source->prover == actual.prover &&
            source->verifier == actual.verifier &&
            source->publicInputs == actual.publicInputs &&
            source->target == actual.target &&
            source->services == actual.services &&
            bool(source->completion) == bool(actual.completion) &&
            (!source->completion ||
             selector(entry.protocol(), *source->completion,
                      *actual.completion)) &&
            text(source->suite, actual.suite) &&
            text(source->construction == ProofEntry::Construction::Derived
                     ? entry.declarations()[source->selectedConstruction->index]
                           .symbol
                     : "",
                 actual.selectedConstruction) &&
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
    json::Array arguments;
    if (definition.kind == RelationDefinition::Kind::Opaque)
      for (const auto &argument : decl.staticArguments) {
        auto encoded = encodeStaticTerm(argument);
        if (!encoded) {
          failure = encoded.takeError();
          return false;
        }
        arguments.push_back(std::move(*encoded));
      }
    if (json::Value(std::move(arguments)) != actual.staticArguments)
      return fail("source relation typed static arguments differ");
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
            actual.externalKind ==
                (definition.kind == K::R1CS  ? "zkc.relation.r1cs/0"
                 : definition.kind == K::AIR ? "zkc.relation.air/0"
                                             : "zkc.relation.bundle/0")) ||
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
        view.entry != entry.name() || view.selected >= view.protocols.size() ||
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
  if (entry.entry().kind == Declaration::Kind::EntryFunction) {
    if (!view.host || view.capture != entry.project().capture().identity() ||
        view.entry != entry.name() ||
        view.host->function != entry.root().symbol || !view.protocols.empty() ||
        !view.relations.empty() || view.proof || !view.setups.empty())
      return error("source.correspondence",
                   "Host source/interface identity differs");
    auto signatures = renderHostSignatures(entry, limits);
    if (!signatures)
      return signatures.takeError();
    if (signatures->size() != view.host->functions.size())
      return error("source.correspondence", "Host interface closure differs");
    // The reader independently bound these schemas and signatures to actual
    // SSA. The canonical source interface fixes nominal fields and permissions.
    for (auto [i, declared] : enumerate(view.host->functions)) {
      const auto &expected = *(*signatures)[i].getAsObject();
      if (expected.getString("symbol") != declared.symbol ||
          expected.getArray("parameters")->size() !=
              declared.parameters.size() ||
          !declared.result ||
          *expected.get("result") !=
              detail::encodeInterfaceSchema(*declared.result))
        return error("source.correspondence", "Host source signature differs");
      for (auto [j, parameter] : enumerate(declared.parameters)) {
        const auto &source =
            *(*expected.getArray("parameters"))[j].getAsObject();
        if (!parameter.schema || source.getString("name") != parameter.name ||
            *source.get("schema") !=
                detail::encodeInterfaceSchema(*parameter.schema))
          return error("source.correspondence",
                       "Host source parameter differs");
      }
    }
    return Error::success();
  }
  return Comparison(entry, view, limits).run();
}
} // namespace zkc::language
