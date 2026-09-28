#include "../Carrier/Reader.h"
#include "../Carrier/Spelling.h"
#include "../Lowering/Admission.h"
#include "../Static/Structural.h"
#include "../Syntax/Grammar.h"
#include "../Syntax/Lexer.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace zkc::frontend {
namespace {
class Printer {
  raw_ostream &out;
  const std::vector<source::StaticParameter> *parameters = nullptr;
  void quoted(StringRef value) { out << json::Value(value); }
  void name(StringRef value) {
    if (grammar::identifier(value) && !grammar::reserved(value))
      out << value;
    else
      quoted(value);
  }
  template <typename T, typename F>
  void list(const std::vector<T> &values, F element, StringRef open = "(",
            StringRef close = ")") {
    out << open;
    bool comma = false;
    for (const auto &value : values) {
      if (comma)
        out << ", ";
      element(value);
      comma = true;
    }
    out << close;
  }
  void names(const source::Names &values) {
    list(values, [&](StringRef value) { name(value); });
  }
  void pairs(const source::Assignments &values) {
    list(values, [&](const auto &pair) {
      name(pair.first);
      out << " = ";
      name(pair.second);
    });
  }
  void clause(StringRef key, const source::Names &values,
              bool required = false) {
    if (!required && values.empty())
      return;
    out << key << ' ';
    names(values);
    out << ";\n";
  }
  void bindingClause(StringRef key, const source::Assignments &values,
                     bool required = false) {
    if (!required && values.empty())
      return;
    out << key << ' ';
    pairs(values);
    out << ";\n";
  }
  void bindingClause(StringRef key, const source::ParameterBindings &values) {
    if (values.empty())
      return;
    out << key << " (";
    llvm::interleaveComma(values, out, [&](const auto &p) {
      name(p.first);
      out << " = ";
      if (const auto *constant = std::get_if<std::string>(&p.second))
        out << *constant;
      else {
        const auto &ingress = std::get<source::FamilyIngress>(p.second);
        out << "ingress(" << ingress.bound;
        for (const auto &selector : ingress.selectors) {
          out << ", ";
          name(selector.role);
          out << " = ";
          name(selector.function);
          names(selector.arguments);
        }
        out << ")";
      }
    });
    out << ");\n";
  }
  void pathSegment(StringRef value) {
    if (grammar::reserved(value))
      out << "r#";
    out << value;
  }
  void operationName(StringRef value) {
    if (carrier::operationContract(value)) {
      SmallVector<StringRef> parts;
      value.split(parts, '.');
      interleave(parts, out, [&](StringRef part) { pathSegment(part); }, "::");
      return;
    }
    name(value);
  }
  void typeExport(const protocol::SourceTypeExport &spelling) {
    SmallVector<StringRef> modules;
    StringRef(spelling.module).split(modules, "::");
    interleave(modules, out, [&](StringRef part) { pathSegment(part); }, "::");
    out << "::";
    pathSegment(spelling.name);
  }
  void type(StringRef value) {
    if (parameters)
      for (const auto &parameter : *parameters)
        if (parameter.sort == "Type" && parameter.name == value) {
          quoted(value);
          return;
        }
    auto parsed = splitLogical(value);
    if (!parsed) {
      quoted(value);
      return;
    }
    StringRef kind = parsed->constructor;
    StringRef identity = parsed->arguments.size() == 1
                             ? StringRef(parsed->arguments.front())
                             : StringRef{};
    if (kind == "bool" || kind == "index") {
      out << kind;
      return;
    }
    for (const auto &associated : protocol::sourceAssociatedTypes())
      if (kind == associated.constructor) {
        quoted(identity);
        out << "::";
        pathSegment(associated.member);
        return;
      }
    for (const auto &family : protocol::sourceTypeFamilies()) {
      if (kind != family.resultConstructor)
        continue;
      for (const auto &exported : protocol::sourceTypeExports())
        if (exported.constructor == family.family) {
          typeExport(exported);
          out << '<';
          type(family.elementConstructor + ":" + identity.str());
          out << '>';
          return;
        }
    }
    for (const auto &spelling : protocol::sourceTypeExports()) {
      if (kind != spelling.constructor)
        continue;
      typeExport(spelling);
      if (!parsed->arguments.empty()) {
        out << '<';
        const auto *declaration = protocol::typeDeclaration(kind);
        for (size_t i = 0; i < parsed->arguments.size(); ++i) {
          if (i)
            out << ", ";
          if (declaration && i < declaration->parameters.size() &&
              declaration->parameters[i].kind == protocol::StaticKind::Type)
            type(parsed->arguments[i]);
          else
            quoted(parsed->arguments[i]);
        }
        out << '>';
      }
      return;
    }
    // Admission and the exact round-trip check refuse unsupported carriers.
    quoted(value);
  }
  void values(const source::Names &values) {
    if (values.size() == 1)
      name(values.front());
    else
      names(values);
  }
  void binding(const source::Names &outputs) {
    if (outputs.empty())
      return;
    out << "let ";
    values(outputs);
    out << " = ";
  }
  void statics(const source::Names &arguments) {
    if (!arguments.empty())
      list(arguments, [&](StringRef value) { quoted(value); }, "::<", ">");
  }
  void arguments(const std::vector<source::Parameter> &values) {
    list(values, [&](const source::Parameter &argument) {
      name(argument.name);
      out << ": ";
      type(argument.type);
    });
  }
  void arguments(const std::vector<source::OwnedParameter> &values) {
    list(values, [&](const source::OwnedParameter &argument) {
      name(argument.role);
      out << ' ';
      name(argument.name);
      out << ": ";
      type(argument.type);
    });
  }
  void results(const source::Names &values) {
    if (values.size() == 1)
      type(values.front());
    else
      list(values, [&](StringRef value) { type(value); });
  }
  void results(const std::vector<source::OwnedResult> &values) {
    list(values, [&](const source::OwnedResult &result) {
      name(result.role);
      out << ' ';
      type(result.type);
    });
  }
  void site(StringRef value) {
    out << '[';
    name(value);
    out << "] ";
  }
  void body(const source::Body &body) {
    for (const auto &instruction : body) {
      if (const auto *ret = instruction.get<source::Return>()) {
        out << "return";
        if (!ret->values.empty()) {
          out << ' ';
          values(ret->values);
        }
      } else if (const auto *yield = instruction.get<source::Yield>()) {
        out << "yield";
        if (!yield->values.empty()) {
          out << ' ';
          values(yield->values);
        }
      } else if (const auto *operation = instruction.get<source::Operation>()) {
        site(instruction.site);
        binding(operation->outputs);
        operationName(operation->callee);
        statics(operation->staticArguments);
        names(operation->inputs);
        // An unqualified installed key needs the operation marker even when
        // its attributes are empty; otherwise it reads as a helper call.
        if (!operation->attributes.empty() ||
            (carrier::operationContract(operation->callee) &&
             !StringRef(operation->callee).contains('.'))) {
          out << " attributes ";
          names(operation->attributes);
        }
      } else if (const auto *call = instruction.get<source::AlgorithmCall>()) {
        site(instruction.site);
        binding(call->outputs);
        name(call->callee);
        statics(call->staticArguments);
        names(call->inputs);
      } else if (const auto *call = instruction.get<source::LocalCall>()) {
        out << "local ";
        site(instruction.site);
        name(call->role);
        out << ": ";
        binding(call->outputs);
        name(call->callee);
        names(call->inputs);
      } else if (const auto *query = instruction.get<source::Query>()) {
        out << "query ";
        site(instruction.site);
        name(query->role);
        out << ": ";
        binding(query->outputs);
        name(query->root);
        names(query->inputs);
      } else if (const auto *guard = instruction.get<source::Guard>()) {
        out << "guard ";
        site(instruction.site);
        name(guard->role);
        out << ": ";
        name(guard->condition);
      } else if (const auto *pure = instruction.get<source::Pure>()) {
        out << "pure ";
        site(instruction.site);
        name(pure->role);
        out << " capture ";
        arguments(pure->captures);
        out << " -> ";
        arguments(pure->outputs);
        out << " {\n";
        this->body(pure->body);
        out << "}\n";
        continue;
      } else if (const auto *message = instruction.get<source::Message>()) {
        out << "message ";
        site(instruction.site);
        name(message->schema);
        out << ": ";
        name(message->sender);
        out << '(';
        name(message->input);
        out << ") -> ";
        name(message->receiver);
        out << '(';
        name(message->output);
        out << ')';
      } else if (const auto *call = instruction.get<source::ProtocolCall>()) {
        out << "invoke ";
        site(instruction.site);
        name(call->callee);
        names(call->inputs);
        out << " -> ";
        names(call->outputs);
      } else if (const auto *stop = instruction.get<source::Stop>()) {
        out << "stop ";
        site(instruction.site);
        name(stop->role);
        out << ' ';
        name(stop->reason);
      } else if (const auto *branch = instruction.get<source::Conditional>()) {
        out << "if ";
        site(instruction.site);
        name(branch->condition);
        out << " capture ";
        names(branch->captures);
        out << " -> ";
        names(branch->outputs);
        out << " {\n";
        this->body(branch->thenBody);
        out << "} else {\n";
        this->body(branch->elseBody);
        out << "}\n";
        continue;
      } else if (const auto *loop = instruction.get<source::For>()) {
        out << "for ";
        site(instruction.site);
        name(loop->induction);
        out << " in ";
        name(loop->lower);
        out << "..";
        name(loop->upper);
        out << " carry ";
        pairs(loop->carried);
        out << " capture ";
        names(loop->captures);
        out << " -> ";
        names(loop->outputs);
        out << " {\n";
        this->body(loop->body);
        out << "}\n";
        continue;
      } else if (const auto *loop = instruction.get<source::Loop>()) {
        out << "loop ";
        site(instruction.site);
        if (loop->count.kind == source::LoopCount::Kind::Constant)
          out << loop->count.value;
        else
          name(loop->count.value);
        out << " carry ";
        pairs(loop->carried);
        if (!loop->captures.empty()) {
          out << " capture ";
          names(loop->captures);
        }
        out << " -> ";
        names(loop->outputs);
        out << " {\n";
        this->body(loop->body);
        out << "}\n";
        continue;
      }
      out << ";\n";
    }
  }
  void function(const source::Function &function) {
    out << "fn ";
    name(function.name);
    arguments(function.arguments);
    out << " -> ";
    results(function.results);
    if (function.origin && (function.origin->definition != function.name ||
                            !function.origin->arguments.empty())) {
      out << " origin ";
      name(function.origin->definition);
      pairs(function.origin->arguments);
    }
    if (!function.body)
      out << " external;\n";
    else {
      out << " {\n";
      body(*function.body);
      out << "}\n";
    }
  }
  void genericFunction(const source::GenericFunction &function) {
    parameters = &function.parameters;
    out << "fn ";
    name(function.name);
    list(
        function.parameters,
        [&](const source::StaticParameter &parameter) {
          name(parameter.name);
          if (parameter.sort == "Type" || parameter.sort == "Nat")
            out << ": " << (parameter.sort == "Type" ? "Type" : "nat");
          else {
            out << ": domain ";
            name(parameter.sort);
          }
        },
        "<", ">");
    arguments(function.arguments);
    out << " -> ";
    results(function.results);
    if (!function.requirements.empty()) {
      out << " requires ";
      list(function.requirements, [&](const source::Requirement &requirement) {
        name(requirement.predicate);
        list(requirement.arguments, [&](StringRef value) { quoted(value); });
      });
    }
    out << " {\n";
    body(function.body);
    out << "}\n";
    parameters = nullptr;
  }
  void protocol(const source::Protocol &protocol) {
    out << "protocol ";
    name(protocol.name);
    out << " {\n";
    clause("roles", protocol.roles, true);
    clause("parameters", protocol.parameters);
    if (!protocol.arguments.empty()) {
      out << "inputs ";
      arguments(protocol.arguments);
      out << ";\n";
    }
    if (!protocol.results.empty()) {
      out << "outputs ";
      results(protocol.results);
      out << ";\n";
    }
    if (!protocol.dependencies.empty()) {
      out << "dependencies ";
      list(protocol.dependencies, [&](const source::Dependency &dependency) {
        name(dependency.name);
        out << ": ";
        name(dependency.protocol);
        pairs(dependency.agreements);
      });
      out << ";\n";
    }
    if (protocol.body)
      body(*protocol.body);
    else
      out << "external;\n";
    out << "}\n";
  }
  void module(const source::Module &module) {
    out << "carrier module {\n";
    for (const auto &definition : module.definitions)
      genericFunction(definition);
    for (const auto &configuration : module.configurations) {
      out << "configure ";
      name(configuration.name);
      out << " = ";
      name(configuration.base);
      list(configuration.arguments, [&](const auto &argument) {
        name(argument.first);
        out << " = ";
        quoted(argument.second);
      });
      if (!configuration.implementations.empty()) {
        out << " using ";
        pairs(configuration.implementations);
      }
      out << ";\n";
    }
    for (const auto &binding : module.bindings) {
      out << "bind ";
      name(binding.name);
      out << " = ";
      quoted(binding.application.contract);
      names(binding.application.arguments);
      if (!binding.application.implementation.empty()) {
        out << " using ";
        name(binding.application.implementation);
      }
      out << ";\n";
    }
    for (const auto &function : module.functions)
      this->function(function);
    for (const auto &root : module.roots) {
      out << "root ";
      name(root.name);
      out << " = ";
      name(root.service);
      out << " owners ";
      names(root.owners);
      out << ";\n";
    }
    for (const auto &protocol : module.protocols)
      this->protocol(protocol);
    for (const auto &instance : module.instances) {
      out << "instance ";
      name(instance.name);
      out << ": ";
      name(instance.protocol);
      out << " {\n";
      bindingClause("parameters", instance.parameters);
      bindingClause("dependencies", instance.dependencies);
      bindingClause("roles", instance.roles, true);
      out << "}\n";
    }
    for (const auto &entry : module.entries) {
      out << "entry ";
      name(entry.name);
      out << " = ";
      name(entry.instance);
      out << ";\n";
    }
    out << "}\n";
  }
  void references(const source::Assignments &values) {
    list(values, [&](const auto &pair) {
      name(pair.first);
      out << ' ';
      name(pair.second);
    });
  }
  void construction(const source::Construction &construction) {
    out << "construction ";
    name(construction.entry);
    if (construction.identity == source::Construction::Identity::Exact)
      out << " identity exact";
    out << " {\nproducer ";
    name(construction.producer);
    out << ";\nvalidator ";
    name(construction.validator);
    out << ";\n";
    for (const auto &binding : construction.publicBindings) {
      out << "public ";
      quoted(binding.name);
      out << " = ";
      references(binding.ports);
      out << ";\n";
    }
    out << "random ";
    name(construction.randomness);
    out << " at ";
    references(construction.draws);
    out << ";\naccept " << construction.acceptance << ";\nsuite ";
    quoted(construction.suite);
    out << ";\n}\n";
  }

public:
  explicit Printer(raw_ostream &out) : out(out) {}
  void run(const source::Content &content) {
    if (const auto *module = std::get_if<source::Module>(&content))
      this->module(*module);
    else if (const auto *construction =
                 std::get_if<source::Construction>(&content))
      this->construction(*construction);
  }
};
} // namespace

Expected<std::string> printProtocol(const source::Content &content) {
  if (std::holds_alternative<source::Participants>(content))
    return zkc::error("source-print-loss");
  if (auto e = checkSourceContent(content))
    return std::move(e);
  if (const auto *module = std::get_if<source::Module>(&content))
    if (!module->relations.empty() || !module->relationViews.empty())
      return zkc::error("source-print-loss");
  bool unsupported = false;
  auto checkBody = [&](const source::Body &body) {
    source::walk(body, [&](const source::Instruction &instruction) {
      if (instruction.get<source::Send>() ||
          instruction.get<source::Receive>() ||
          instruction.get<source::Release>() ||
          instruction.get<source::Incomplete>() ||
          instruction.get<source::VariantConstruct>() ||
          instruction.get<source::Match>())
        unsupported = true;
    });
  };
  if (const auto *module = std::get_if<source::Module>(&content)) {
    for (const auto &function : module->definitions)
      checkBody(function.body);
    for (const auto &function : module->functions)
      if (function.body)
        checkBody(*function.body);
    for (const auto &protocol : module->protocols)
      if (protocol.body)
        checkBody(*protocol.body);
  }
  if (unsupported)
    return zkc::error("source-print-loss");
  std::string text;
  raw_string_ostream out(text);
  Printer(out).run(content);
  auto tokens = lex(text, "<printer>");
  if (!tokens)
    return tokens.takeError();
  auto formatted = formatTokens(*tokens);
  if (!formatted)
    return formatted.takeError();
  // Check the final representation, including any formatter changes, against
  // exact common custody. Diagnostic spans are intentionally not serialized.
  if (std::holds_alternative<source::Module>(content)) {
    auto decoded = carrier::readCarrier(*formatted, "<printer>");
    if (!decoded) {
      consumeError(decoded.takeError());
      return zkc::error("source-print-loss");
    }
    if (source::encode(*decoded) != source::encode(content))
      return zkc::error("source-print-loss");
  } else {
    auto document =
        parseProtocolDocument(Input::withoutFile(*formatted, "<printer>"));
    if (!document) {
      consumeError(document.takeError());
      return zkc::error("source-print-loss");
    }
    if (source::encode(document->root()) != source::encode(content))
      return zkc::error("source-print-loss");
  }
  return formatted;
}

Expected<std::string> formatProtocol(StringRef text, StringRef filename) {
  if (classifyDocument(text) == SourceForm::CommonJSON) {
    auto document = parseProtocolDocument(text, filename);
    if (!document)
      return document.takeError();
    return printProtocol(document->root());
  }
  if (auto error = checkProtocolSyntax(text, filename))
    return std::move(error);
  auto tokens = lex(text, filename);
  if (!tokens)
    return tokens.takeError();
  return formatTokens(*tokens);
}
} // namespace zkc::frontend
