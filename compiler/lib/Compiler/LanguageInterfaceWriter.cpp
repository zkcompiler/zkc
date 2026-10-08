#include "LanguageInterface.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
using namespace llvm;
namespace zkc::language::detail {
namespace {
std::string digest(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
Error writeInterface(json::OStream &out, BoundedStream &stream,
                     const ClosedEntry &entry, StringRef original,
                     StringRef toolchain, const Limits &limits) {
  Layouts layouts(entry, limits);
  struct Ports {
    std::vector<std::shared_ptr<const Layout>> inputs, outputs;
  };
  std::map<unsigned, Ports> declared;
  for (const auto &decl : entry.declarations()) {
    if ((!decl.body || decl.kind != Declaration::Kind::Protocol) &&
        !(decl.relation && decl.origin))
      continue;
    auto &record = declared[decl.id.index];
    for (bool input : {true, false})
      for (const auto &port : input ? decl.inputs : decl.outputs) {
        if (spelling(port.type).size() > protocol::VariantSpellingBytes)
          return make_error<DiagnosticError>(
              Diagnostic{"source.limit",
                         "interface type spelling exceeds byte limit",
                         port.span,
                         {}});
        auto layout = layouts.get(port.type);
        if (!layout)
          return layout.takeError();
        if ((*layout)->formal)
          return error("source.formal",
                       "interface ports cannot contain formal values");
        (input ? record.inputs : record.outputs).push_back(*layout);
      }
  }
  uint64_t remaining = limits.work;
  bool limited = false, formal = false;
  auto charge = [&](uint64_t work) {
    if (limited || stream.overflow() || work > remaining) {
      limited = true;
      return false;
    }
    remaining -= work;
    return true;
  };
  std::map<const Layout *, std::string> identities;
  std::optional<Diagnostic> spellingDiagnostic;
  std::function<void(const Layout &, Span)> schema;
  schema = [&](const Layout &layout, Span port) {
    if (spellingDiagnostic) {
      out.value(nullptr);
      return;
    }
    auto display = spelling(layout.type);
    if (display.size() > protocol::VariantSpellingBytes) {
      spellingDiagnostic =
          Diagnostic{"source.limit",
                     "interface schema type spelling exceeds byte limit",
                     port,
                     {}};
      out.value(nullptr);
      return;
    }
    if (!charge(1)) {
      out.value(nullptr);
      return;
    }
    auto found = identities.find(&layout);
    if (found == identities.end()) {
      auto key = typeIdentity(layout.type);
      if (!charge(key.size())) {
        out.value(nullptr);
        return;
      }
      found = identities.emplace(&layout, digest(key)).first;
    }
    out.object([&] {
      out.attribute("kind", typeKindName(layout.type.kind));
      out.attribute("identity", found->second);
      out.attribute("type", display);
      out.attribute("custody", layout.custody);
      out.attributeArray("permissions", [&] {
        if (layout.permissions.copy)
          out.value("Copy");
        if (layout.permissions.drop)
          out.value("Drop");
        if (layout.permissions.share)
          out.value("Share");
        if (layout.permissions.wire)
          out.value("Wire");
      });
      auto fields = [&](ArrayRef<LayoutField> fields) {
        for (auto &field : fields) {
          if (!charge(field.name.size() + 1))
            break;
          out.object([&] {
            out.attribute("name", field.name);
            out.attribute("offset", field.offset);
            out.attributeBegin("schema");
            schema(*field.layout, port);
            out.attributeEnd();
          });
        }
      };
      out.attributeArray("fields", [&] { fields(layout.fields); });
      out.attributeArray("alternatives", [&] {
        for (auto &alternative : layout.alternatives) {
          if (!charge(alternative.name.size() + 1))
            break;
          out.object([&] {
            out.attribute("name", alternative.name);
            out.attributeArray("fields", [&] { fields(alternative.fields); });
          });
        }
      });
      out.attributeArray("leaves", [&] {
        for (auto &leaf : layout.leaves) {
          if (!charge(leaf.cost()))
            break;
          const auto *data = leaf.data();
          if (!data) {
            formal = true;
            break;
          }
          out.value(*data);
        }
      });
    });
  };
  auto ports = [&](const Declaration &protocol, StringRef name,
                   ArrayRef<Port> source,
                   ArrayRef<std::shared_ptr<const Layout>> layouts) {
    unsigned flat = 0;
    out.attributeArray(name, [&] {
      for (unsigned i = 0; i < source.size(); ++i) {
        if (!charge(source[i].name.size() + 1))
          break;
        out.object([&] {
          out.attribute("name", source[i].name);
          out.attribute("type", spelling(source[i].type));
          out.attributeArray("roles", [&] {
            for (unsigned role : source[i].roles)
              out.value(protocol.roles[role]);
          });
          out.attribute("index", i);
          out.attributeArray("native", [&] {
            for (unsigned j = 0; j < layouts[i]->leaves.size(); ++j)
              out.value(flat++);
          });
          out.attributeBegin("schema");
          schema(*layouts[i], source[i].span);
          out.attributeEnd();
        });
      }
    });
  };
  auto selector = [&](const Declaration &protocol,
                      const SpecificationSelector &value) {
    if (!charge(value.path.size() + protocol.roles[value.role].size() + 1)) {
      out.value(nullptr);
      return;
    }
    out.object([&] {
      out.attribute("direction", value.output ? "output" : "input");
      out.attribute("port", value.port);
      out.attribute("role", protocol.roles[value.role]);
      out.attributeArray("path", [&] {
        for (auto index : value.path)
          out.value(index);
      });
    });
  };
  auto application = [&](const Declaration &protocol,
                         const RelationApplication &value) {
    if (!charge(value.operands.size() +
                entry.declarations()[value.relation.index].symbol.size() + 1)) {
      out.value(nullptr);
      return;
    }
    out.object([&] {
      out.attribute("relation",
                    entry.declarations()[value.relation.index].symbol);
      out.attributeArray("operands", [&] {
        for (const auto &operand : value.operands)
          selector(protocol, operand);
      });
    });
  };
  out.object([&] {
    out.attribute("format", "zkc.language-interface/5");
    out.attribute("capture", entry.project().capture().identity());
    out.attribute("original", original);
    out.attribute("toolchain", toolchain);
    out.attribute("entry", entry.entry().qualifiedName);
    out.attribute("protocol", entry.protocol().symbol);
    out.attributeObject("job", [&] {
      const auto &proof = entry.entry().proof;
      out.attribute("kind", proof ? "proof" : "run");
      if (!proof)
        return;
      const auto &protocol = entry.protocol();
      if (!charge(proof->publicInputs.size() + proof->suite.size() + 1))
        return;
      out.attribute("prover", protocol.roles[proof->prover]);
      out.attribute("verifier", protocol.roles[proof->verifier]);
      out.attributeArray("public", [&] {
        for (unsigned index : proof->publicInputs)
          out.value(index);
      });
      out.attributeBegin("acceptance");
      selector(protocol, proof->acceptance);
      out.attributeEnd();
      out.attributeBegin("target");
      if (proof->target)
        out.value(protocol.specifications[*proof->target].name);
      else
        out.value(nullptr);
      out.attributeEnd();
      out.attributeObject("construction", [&] {
        bool derived =
            proof->construction == ProofEntry::Construction::FiatShamir;
        out.attribute("kind", derived ? "fiat_shamir" : "authored");
        if (derived) {
          out.attribute("suite", proof->suite);
          out.attribute("service", *proof->service);
        }
      });
    });
    out.attributeArray("protocols", [&] {
      for (const auto &protocol : entry.declarations()) {
        if (!protocol.body || protocol.kind != Declaration::Kind::Protocol)
          continue;
        if (!charge(protocol.symbol.size() + 1))
          break;
        const auto &record = declared.at(protocol.id.index);
        out.object([&] {
          out.attribute("symbol", protocol.symbol);
          out.attributeArray("roles", [&] {
            for (const auto &role : protocol.roles)
              out.value(role);
          });
          ports(protocol, "inputs", protocol.inputs, record.inputs);
          ports(protocol, "outputs", protocol.outputs, record.outputs);
          out.attributeArray("services", [&] {
            unsigned native = 0;
            for (const auto &layout : record.inputs)
              native += layout->leaves.size();
            for (const auto &service : protocol.services) {
              if (!charge(service.name.size() + service.contract.size() + 1))
                break;
              out.object([&] {
                out.attribute("name", service.name);
                out.attribute("contract", service.contract);
                out.attribute("owner", protocol.roles[service.owner]);
                out.attribute("native", native++);
              });
            }
          });
          out.attributeArray("clauses", [&] {
            for (const auto &clause : protocol.specifications) {
              if (!charge(clause.name.size() + 1))
                break;
              out.object([&] {
                out.attribute("name", clause.name);
                using K = SpecificationClause::Kind;
                out.attribute("kind", clause.kind == K::Target  ? "target"
                                      : clause.kind == K::Input ? "input"
                                      : clause.kind == K::Output
                                          ? "output"
                                          : "continuation");
                out.attributeBegin("subject");
                application(protocol, clause.subject);
                out.attributeEnd();
                out.attributeBegin("residual");
                if (clause.residual)
                  application(protocol, *clause.residual);
                else
                  out.value(nullptr);
                out.attributeEnd();
                out.attributeBegin("decision");
                if (clause.decision)
                  selector(protocol, *clause.decision);
                else
                  out.value(nullptr);
                out.attributeEnd();
              });
            }
          });
        });
      }
    });
    out.attributeArray("relations", [&] {
      for (const auto &decl : entry.declarations()) {
        if (!decl.relation || !decl.origin)
          continue;
        if (!charge(decl.symbol.size() + 1))
          break;
        const auto &definition = *decl.relation;
        out.object([&] {
          out.attribute("symbol", decl.symbol);
          out.attributeArray("inputs", [&] {
            unsigned flat = 0;
            for (unsigned i = 0; i < decl.inputs.size(); ++i) {
              if (!charge(decl.inputs[i].name.size() + 1))
                break;
              const auto &layout = *declared.at(decl.id.index).inputs[i];
              out.object([&] {
                out.attribute("name", decl.inputs[i].name);
                auto purpose = definition.purposes[i];
                out.attribute("purpose", purpose == RelationPurpose::Parameter
                                             ? "parameter"
                                         : purpose == RelationPurpose::Statement
                                             ? "statement"
                                             : "witness");
                out.attributeArray("native", [&] {
                  for (unsigned j = 0; j < layout.leaves.size(); ++j)
                    out.value(flat++);
                });
                out.attributeBegin("schema");
                schema(layout, decl.inputs[i].span);
                out.attributeEnd();
              });
            }
          });
          out.attributeObject("definition", [&] {
            using K = RelationDefinition::Kind;
            out.attribute("kind", definition.kind == K::Formula  ? "formula"
                                  : definition.kind == K::Opaque ? "opaque"
                                  : definition.kind == K::R1CS   ? "r1cs"
                                                                 : "air");
            if (definition.kind == K::Formula)
              out.attribute("function", formulaSymbol(decl));
            if (definition.asset)
              out.attribute(
                  "asset",
                  entry.project().assets()[*definition.asset].identity());
          });
        });
      }
    });
  });
  if (spellingDiagnostic)
    return make_error<DiagnosticError>(std::move(*spellingDiagnostic));
  if (formal)
    return error("source.formal", "interface schema contains formal leaves");
  if (limited || stream.overflow())
    return error("source.limit", "interface traversal or byte limit exceeded");
  return Error::success();
}
} // namespace
Expected<std::string> emitInterface(const ClosedEntry &entry,
                                    StringRef original, StringRef toolchain,
                                    const Limits &limits) {
  std::string result;
  BoundedStream stream(result, limits.interfaceBytes);
  json::OStream out(stream);
  if (auto error =
          writeInterface(out, stream, entry, original, toolchain, limits))
    return std::move(error);
  return result;
}
} // namespace zkc::language::detail
