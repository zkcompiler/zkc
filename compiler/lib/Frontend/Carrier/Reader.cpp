#include "Reader.h"
#include "../Static/Structural.h"
#include "../Syntax/Grammar.h"
#include "../Syntax/Lexer.h"
#include "Spelling.h"
#include "llvm/ADT/StringSet.h"
#include <algorithm>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::frontend::carrier {
namespace {
// The carrier has explicit regions, operands and sites. These helpers decode
// records only: no expression grammar, name authorization or type checking.
class Reader {
  StringRef text, filename;
  ArrayRef<Token> tokens;
  size_t cursor = 0, lastEnd = 0, errorOffset = 0;
  std::string errorCode, message;
  std::map<std::string, std::string> parameterSorts;
  static constexpr size_t listLimit = 32768;
  static constexpr unsigned depthLimit = 64;

  const Token &token() const { return tokens[cursor]; }
  bool failed() const { return !errorCode.empty(); }
  void fail(StringRef code, const Twine &why) {
    failAt(token().offset, code, why);
  }
  void failAt(size_t offset, StringRef code, const Twine &why) {
    if (failed())
      return;
    errorOffset = offset;
    errorCode = code.str();
    message = why.str();
  }
  void advance() {
    lastEnd = token().offset + token().spelling.size();
    if (cursor + 1 < tokens.size())
      ++cursor;
    while (token().kind == TokenKind::Comment)
      ++cursor;
  }
  bool eat(StringRef spelling) {
    if (failed() || !token().is(spelling))
      return false;
    advance();
    return true;
  }
  void expect(StringRef spelling) {
    if (!eat(spelling))
      fail("source-syntax", "expected '" + spelling + "'");
  }
  bool bounded(unsigned depth) {
    if (depth <= depthLimit && !failed())
      return true;
    fail("source-depth", "carrier nesting exceeds 64 levels");
    return false;
  }
  std::string atom(bool number = false) {
    if (failed())
      return {};
    if (token().kind != TokenKind::Name &&
        token().kind != TokenKind::RawIdentifier &&
        token().kind != TokenKind::String &&
        !(number && token().kind == TokenKind::Number)) {
      fail("source-syntax", "expected an exact carrier name or string");
      return {};
    }
    if (token().kind == TokenKind::Name && grammar::reserved(token().value())) {
      fail("source-syntax", "an exact keyword name requires quotes or r#");
      return {};
    }
    std::string value = token().value().str();
    advance();
    return value;
  }
  std::string identifier() {
    if (token().kind != TokenKind::RawIdentifier &&
        (token().kind != TokenKind::Name ||
         grammar::reserved(token().value()))) {
      fail("source-syntax",
           "expected an identifier or raw identifier in a path");
      return {};
    }
    return atom();
  }
  template <typename T> T record(T value, size_t start) {
    value.location = source::Span{start, std::max(start, lastEnd) - start, 0};
    return value;
  }
  template <typename F> auto list(StringRef open, StringRef close, F element) {
    std::vector<decltype(element())> result;
    expect(open);
    if (eat(close))
      return result;
    while (!failed()) {
      if (result.size() == listLimit) {
        fail("source-limit", "carrier list exceeds 32768 entries");
        break;
      }
      result.push_back(element());
      if (eat(close))
        break;
      expect(",");
      if (eat(close))
        break;
    }
    return result;
  }
  source::Names names() {
    return list("(", ")", [&] { return atom(); });
  }
  source::Names values() {
    if (token().is("("))
      return names();
    if (token().is(";"))
      return {};
    return {atom()};
  }
  source::Assignments pairs() {
    return list("(", ")", [&] {
      auto key = atom();
      expect("=");
      return std::make_pair(std::move(key), atom(true));
    });
  }

  // Used solely to invert installed associated-type notation. Scope lookup is
  // deliberately first, even for a quoted binder equal to an installed ID.
  std::string sortOf(StringRef term, unsigned depth = 0) {
    if (depth > depthLimit)
      return {};
    if (auto found = parameterSorts.find(term.str());
        found != parameterSorts.end())
      return found->second;
    auto installed = protocol::installedIdentitySort(term);
    if (!installed.empty())
      return installed.str();
    auto [parent, member] = term.rsplit('.');
    if (parent.empty() || member.empty())
      return {};
    return protocol::associatedMemberSort(sortOf(parent, depth + 1), member)
        .str();
  }
  std::string term(unsigned depth = 0) {
    if (!bounded(depth))
      return {};
    bool exact = token().kind == TokenKind::String;
    auto root = atom(true);
    source::Names path{root};
    while (eat("::")) {
      if (path.size() == depthLimit) {
        fail("source-depth", "carrier path exceeds 64 segments");
        return {};
      }
      // An exact carrier binder may be the root; path members use the same
      // installed identifier grammar as the generated export metadata.
      path.push_back(identifier());
    }
    if (failed())
      return {};
    auto constructor = exact || (path.size() == 1 && parameterSorts.count(root))
                           ? StringRef{}
                           : typeConstructor(path);
    if (token().is("<")) {
      auto arguments = list("<", ">", [&] { return term(depth + 1); });
      if (constructor.empty()) {
        fail("source-syntax", "expected an installed carrier type export");
        return {};
      }
      for (const auto &family : protocol::sourceTypeFamilies()) {
        if (family.family != constructor || arguments.size() != 1)
          continue;
        auto element = splitLogical(arguments.front());
        if (element && element->constructor == family.elementConstructor)
          return logicalSpelling(family.resultConstructor, element->arguments);
      }
      return logicalSpelling(constructor, arguments);
    }
    if (!constructor.empty())
      return constructor.str();
    if (path.size() == 1)
      return root;
    for (size_t i = 1; i < path.size(); ++i) {
      auto sort = sortOf(root);
      for (const auto &associated : protocol::sourceAssociatedTypes()) {
        if (associated.sort == sort && associated.member == path[i]) {
          if (i + 1 != path.size()) {
            fail("source-syntax", "a carrier type cannot have another member");
            return {};
          }
          return logicalSpelling(associated.constructor, {root});
        }
      }
      root += "." + path[i];
    }
    return root;
  }
  std::vector<source::Parameter> arguments() {
    return list("(", ")", [&] {
      auto name = atom();
      expect(":");
      return source::Parameter{std::move(name), term()};
    });
  }
  source::Names results() {
    if (token().is("("))
      return list("(", ")", [&] { return term(); });
    return {term()};
  }
  std::string site() {
    expect("[");
    auto result = atom();
    expect("]");
    return result;
  }
  source::Names outputs() {
    if (!eat("let"))
      return {};
    auto result = values();
    expect("=");
    return result;
  }
  source::Body body(unsigned depth = 0) {
    source::Body result;
    if (!bounded(depth))
      return result;
    expect("{");
    bodyContents(result, depth);
    return result;
  }
  void bodyContents(source::Body &result, unsigned depth) {
    while (!failed() && !eat("}")) {
      if (result.size() == listLimit) {
        fail("source-limit", "carrier body exceeds 32768 instructions");
        break;
      }
      result.push_back(instruction(depth));
    }
  }
  source::Instruction instruction(unsigned depth) {
    const auto start = token().offset;
    source::Instruction result;
    bool region = false;
    if (eat("return")) {
      result.value = source::Return{values()};
    } else if (eat("yield")) {
      result.value = source::Yield{values()};
    } else if (eat("local")) {
      result.site = site();
      source::LocalCall call;
      call.role = atom();
      expect(":");
      call.outputs = outputs();
      call.callee = atom();
      call.inputs = names();
      result.value = std::move(call);
    } else if (eat("query")) {
      result.site = site();
      source::Query query;
      query.role = atom();
      expect(":");
      query.outputs = outputs();
      query.root = atom();
      query.inputs = names();
      result.value = std::move(query);
    } else if (eat("guard")) {
      result.site = site();
      source::Guard guard;
      guard.role = atom();
      expect(":");
      guard.condition = atom();
      result.value = std::move(guard);
    } else if (eat("pure")) {
      result.site = site();
      source::Pure pure;
      pure.role = atom();
      expect("capture");
      pure.captures = arguments();
      expect("->");
      pure.outputs = arguments();
      pure.body = body(depth + 1);
      result.value = std::move(pure);
      region = true;
    } else if (eat("message")) {
      result.site = site();
      source::Message message;
      message.schema = atom();
      expect(":");
      message.sender = atom();
      expect("(");
      message.input = atom();
      expect(")");
      expect("->");
      message.receiver = atom();
      expect("(");
      message.output = atom();
      expect(")");
      result.value = std::move(message);
    } else if (eat("invoke")) {
      result.site = site();
      source::ProtocolCall call;
      call.callee = atom();
      call.inputs = names();
      expect("->");
      call.outputs = names();
      result.value = std::move(call);
    } else if (eat("stop")) {
      result.site = site();
      auto role = atom();
      result.value = source::Stop{std::move(role), atom()};
    } else if (eat("if")) {
      result.site = site();
      source::Conditional branch;
      branch.condition = atom();
      expect("capture");
      branch.captures = names();
      expect("->");
      branch.outputs = names();
      branch.thenBody = body(depth + 1);
      expect("else");
      branch.elseBody = body(depth + 1);
      result.value = std::move(branch);
      region = true;
    } else if (eat("for")) {
      result.site = site();
      source::For loop;
      loop.induction = atom();
      expect("in");
      loop.lower = atom();
      expect("..");
      loop.upper = atom();
      expect("carry");
      loop.carried = pairs();
      expect("capture");
      loop.captures = names();
      expect("->");
      loop.outputs = names();
      loop.body = body(depth + 1);
      result.value = std::move(loop);
      region = true;
    } else if (eat("loop")) {
      result.site = site();
      source::Loop loop;
      loop.count.kind = token().kind == TokenKind::Number
                            ? source::LoopCount::Kind::Constant
                            : source::LoopCount::Kind::Parameter;
      loop.count.value = atom(true);
      expect("carry");
      loop.carried = pairs();
      if (eat("capture"))
        loop.captures = names();
      expect("->");
      loop.outputs = names();
      loop.body = body(depth + 1);
      result.value = std::move(loop);
      region = true;
    } else {
      if (!token().is("[")) {
        fail("source-syntax",
             "expected a carrier instruction with an explicit site");
        return result;
      }
      result.site = site();
      source::AlgorithmCall call;
      call.outputs = outputs();
      auto calleeOffset = token().offset;
      bool exact = token().kind == TokenKind::String;
      auto firstKind = token().kind;
      call.callee = atom();
      bool contract = false, staticArguments = false;
      while (eat("::")) {
        if (token().is("<")) {
          staticArguments = true;
          break;
        }
        if (exact ||
            (firstKind == TokenKind::Name && grammar::reserved(call.callee)))
          failAt(calleeOffset, "source-syntax",
                 "contract paths require identifier segments");
        contract = true;
        call.callee += "." + identifier();
        if (call.callee.size() > 255)
          fail("source-limit", "carrier operation path exceeds 255 bytes");
      }
      if (staticArguments)
        call.staticArguments = list("<", ">", [&] { return term(); });
      call.inputs = names();
      if (contract) {
        if (!operationContract(call.callee))
          failAt(calleeOffset, "source-syntax",
                 "unknown installed operation path");
        source::Operation operation{std::move(call.callee),
                                    std::move(call.staticArguments),
                                    {},
                                    std::move(call.inputs),
                                    std::move(call.outputs)};
        if (eat("attributes"))
          operation.attributes = names();
        result.value = std::move(operation);
      } else if (eat("attributes")) {
        result.value = source::Operation{
            std::move(call.callee), std::move(call.staticArguments), names(),
            std::move(call.inputs), std::move(call.outputs)};
      } else {
        // Exact names are classified in the complete common binding scope,
        // after forward declarations have been read. Qualified paths never
        // enter this lookup and cannot be captured by a dotted helper name.
        result.value = std::move(call);
      }
    }
    if (!region)
      expect(";");
    return record(std::move(result), start);
  }

  void function(source::Module &module, size_t start) {
    auto name = atom();
    if (token().is("<")) {
      source::GenericFunction function;
      function.name = std::move(name);
      function.parameters = list("<", ">", [&] {
        source::StaticParameter parameter;
        parameter.name = atom();
        expect(":");
        if (eat("domain"))
          parameter.sort = atom();
        else if (eat("nat"))
          parameter.sort = "Nat";
        else {
          expect("Type");
          parameter.sort = "Type";
        }
        parameterSorts.emplace(parameter.name, parameter.sort);
        return parameter;
      });
      function.arguments = arguments();
      expect("->");
      function.results = results();
      if (eat("requires")) {
        function.requirements = list("(", ")", [&] {
          size_t start = token().offset;
          source::Requirement requirement;
          requirement.predicate = atom();
          requirement.arguments = list("(", ")", [&] { return term(); });
          return record(std::move(requirement), start);
        });
      }
      function.body = body();
      module.definitions.push_back(record(std::move(function), start));
      parameterSorts.clear();
    } else {
      source::Function function;
      function.name = std::move(name);
      function.arguments = arguments();
      expect("->");
      function.results = results();
      function.origin = source::LogicalOrigin{function.name, {}};
      if (eat("origin")) {
        auto definition = atom();
        function.origin = source::LogicalOrigin{std::move(definition), pairs()};
      }
      if (eat("external"))
        expect(";");
      else
        function.body = body();
      module.functions.push_back(record(std::move(function), start));
    }
  }
  source::Protocol protocol(size_t start) {
    source::Protocol result;
    result.name = atom();
    expect("{");
    std::set<std::string> headers;
    while (!failed()) {
      if (!(token().is("roles") || token().is("parameters") ||
            token().is("inputs") || token().is("outputs") ||
            token().is("dependencies")))
        break;
      auto keyOffset = token().offset;
      auto key = atom();
      if (!headers.insert(key).second)
        failAt(keyOffset, "source-duplicate",
               "duplicate carrier protocol clause");
      if (key == "roles")
        result.roles = names();
      else if (key == "parameters")
        result.parameters = names();
      else if (key == "inputs")
        result.arguments = list("(", ")", [&] {
          auto role = atom();
          auto name = atom();
          expect(":");
          return source::OwnedParameter{std::move(name), std::move(role),
                                        term()};
        });
      else if (key == "outputs")
        result.results = list("(", ")", [&] {
          auto role = atom();
          return source::OwnedResult{std::move(role), term()};
        });
      else
        result.dependencies = list("(", ")", [&] {
          const auto offset = token().offset;
          source::Dependency dependency;
          dependency.name = atom();
          expect(":");
          dependency.protocol = atom();
          dependency.agreements = pairs();
          return record(std::move(dependency), offset);
        });
      expect(";");
    }
    if (!headers.count("roles"))
      fail("source-syntax",
           "carrier protocol requires an explicit roles clause");
    if (eat("external")) {
      expect(";");
      expect("}");
    } else {
      result.body.emplace();
      bodyContents(*result.body, 0);
    }
    return record(std::move(result), start);
  }
  source::ParameterBindings parameterBindings() {
    return list("(", ")", [&] {
      auto name = atom();
      expect("=");
      source::ParameterBinding value;
      if (eat("ingress")) {
        expect("(");
        source::FamilyIngress ingress;
        ingress.bound = atom(true);
        while (eat(",")) {
          if (ingress.selectors.size() == listLimit) {
            fail("source-limit", "carrier ingress exceeds 32768 selectors");
            break;
          }
          auto role = atom();
          expect("=");
          auto function = atom();
          ingress.selectors.push_back(
              {std::move(role), std::move(function), names()});
        }
        expect(")");
        value = std::move(ingress);
      } else
        value = atom(true);
      return std::make_pair(std::move(name), std::move(value));
    });
  }
  source::Instance instance(size_t start) {
    source::Instance result;
    result.name = atom();
    expect(":");
    result.protocol = atom();
    expect("{");
    std::set<std::string> headers;
    while (!failed() && !eat("}")) {
      if (!(token().is("parameters") || token().is("dependencies") ||
            token().is("roles"))) {
        fail("source-syntax", "expected a carrier instance clause");
        break;
      }
      auto keyOffset = token().offset;
      auto key = atom();
      if (!headers.insert(key).second)
        failAt(keyOffset, "source-duplicate",
               "duplicate carrier instance clause");
      if (key == "parameters")
        result.parameters = parameterBindings();
      else if (key == "dependencies")
        result.dependencies = pairs();
      else
        result.roles = pairs();
      expect(";");
    }
    if (!headers.count("roles"))
      fail("source-syntax",
           "carrier instance requires an explicit roles clause");
    return record(std::move(result), start);
  }
  void classifyCalls(source::Body &body, const StringSet<> &bindings) {
    source::walk(body, [&](source::Instruction &instruction) {
      if (auto *call = instruction.get<source::AlgorithmCall>();
          call && bindings.contains(call->callee)) {
        source::Operation operation{std::move(call->callee),
                                    std::move(call->staticArguments),
                                    {},
                                    std::move(call->inputs),
                                    std::move(call->outputs)};
        instruction.value = std::move(operation);
      }
    });
  }

public:
  Reader(StringRef text, StringRef filename, ArrayRef<Token> tokens)
      : text(text), filename(filename), tokens(tokens) {
    while (token().kind == TokenKind::Comment)
      ++cursor;
  }
  Expected<source::Content> run() {
    source::Module module;
    const auto start = token().offset;
    expect("carrier");
    expect("module");
    if (!token().is("{"))
      fail("source-carrier-authoring",
           "carrier modules have no authored profile");
    expect("{");
    size_t declarations = 0;
    while (!failed() && !eat("}")) {
      if (++declarations > listLimit) {
        fail("source-limit", "carrier module exceeds 32768 declarations");
        break;
      }
      const auto offset = token().offset;
      if (eat("fn"))
        function(module, offset);
      else if (eat("protocol"))
        module.protocols.push_back(protocol(offset));
      else if (eat("instance"))
        module.instances.push_back(instance(offset));
      else if (eat("entry")) {
        source::Entry entry;
        entry.name = atom();
        expect("=");
        entry.instance = atom();
        expect(";");
        module.entries.push_back(record(std::move(entry), offset));
      } else if (eat("root")) {
        source::Root root;
        root.name = atom();
        expect("=");
        root.service = atom();
        expect("owners");
        root.owners = names();
        expect(";");
        module.roots.push_back(record(std::move(root), offset));
      } else if (eat("bind")) {
        source::OperationBinding binding;
        binding.name = atom();
        expect("=");
        if (token().kind != TokenKind::String)
          fail("source-syntax",
               "a bind contract must be an exact quoted string");
        binding.application.contract = atom();
        binding.application.arguments =
            list("(", ")", [&] { return atom(true); });
        if (eat("using"))
          binding.application.implementation = atom();
        expect(";");
        module.bindings.push_back(record(std::move(binding), offset));
      } else if (eat("configure")) {
        source::Configuration configuration;
        configuration.name = atom();
        expect("=");
        configuration.base = atom();
        configuration.arguments = list("(", ")", [&] {
          auto name = atom();
          expect("=");
          return std::make_pair(std::move(name), term());
        });
        if (eat("using"))
          configuration.implementations = pairs();
        expect(";");
        module.configurations.push_back(
            record(std::move(configuration), offset));
      } else
        fail("source-carrier-authoring",
             "expected an exact common carrier declaration");
    }
    module = record(std::move(module), start);
    if (token().kind != TokenKind::End)
      fail("source-syntax", "unexpected input after carrier module");
    if (failed())
      return diagnostic(text, filename, errorOffset, errorCode, message);
    StringSet<> bindings;
    for (const auto &binding : module.bindings)
      bindings.insert(binding.name);
    for (auto &function : module.functions)
      if (function.body)
        classifyCalls(*function.body, bindings);
    for (auto &protocol : module.protocols)
      if (protocol.body)
        classifyCalls(*protocol.body, bindings);
    // Generic bodies name contracts by explicit paths. Their exact helper
    // names belong to the generic scope, not the concrete binding scope.
    return source::Content(std::move(module));
  }
};
} // namespace

Expected<source::Content> readCarrier(StringRef text, StringRef filename) {
  auto tokens = lex(text, filename);
  if (!tokens)
    return tokens.takeError();
  return Reader(text, filename, *tokens).run();
}
} // namespace zkc::frontend::carrier
