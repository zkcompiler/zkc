#include "Names.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Instantiation.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Document.h"
#include "zkc/Source/Resolution.h"
#include "zkc/Target/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <limits>
#include <tuple>

using namespace llvm;
using namespace zkc;
using namespace zkc::source;
using namespace zkc::frontend;
using A = json::Array;
using V = json::Value;

namespace {
unsigned checks = 0;
void require(bool condition, const Twine &message) {
  ++checks;
  if (!condition) {
    errs() << "source test: " << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> result) {
  if (!result) {
    errs() << "source test: " << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
void success(Error error) {
  if (error)
    require(false, "unexpected error: " + toString(std::move(error)));
  else
    require(true, "success");
}
void rejects(Error error, StringRef code) {
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code),
          "missing error: " + code + ": " + message);
}
template <typename T> void rejects(Expected<T> result, StringRef code) {
  require(!bool(result), "unexpected success");
  rejects(result.takeError(), code);
}

V encoded(const Document &document) { return encode(document.root()); }
V resolve(const Document &document, const Path &path) {
  V value = encoded(document);
  for (auto index : path) {
    const auto *array = value.getAsArray();
    require(array && index < array->size(), "test codec path in bounds");
    V next = (*array)[index];
    value = std::move(next);
  }
  return value;
}
std::optional<Span> span(const Document &document, const Path &path) {
  RecordMap records;
  encode(document.root(), &records);
  auto found = records.find(path);
  return found == records.end() ? std::nullopt : document.span(found->second);
}
void at(const Document &document, const Path &path, StringRef spelling) {
  auto location = span(document, path);
  require(bool(location), "node must have a span");
  require(document.text().find(spelling) == location->offset,
          "exact record offset");
  require(document.text().substr(location->offset, location->length) ==
              spelling,
          "exact extent excludes trailing comments/whitespace");
}
template <typename T> Instruction instruction(std::string site, T value) {
  Instruction out;
  out.site = std::move(site);
  out.value = std::move(value);
  return out;
}
void builderProbe() {
  // Independent hand-written text and C++ authoring of the same open generic
  // module, ordinary local body and multi-role protocol. No JSON builder.
  const char *text = R"pir(module {
    bind both = bool.and();
    fn Both(a: bool, b: bool) -> (bool) {
      [join] let c = both(a, b);
      return (c);
    }
    fn Scale<G: domain Group>(g: G::Element, k: G::Scalar::Element) -> (G::Element)
      requires (ScalarAction(G)) {
      [scale] let h = curve::scale::<G>(g, k);
      return (h);
    }
    configure Curve = Scale(G = bls12-381.g1);
    protocol Demo {
      roles (Alice, Bob);
      inputs (Alice g: "bls12-381.g1"::Element, Alice k: "bls12-381.fr"::Element,
              Alice a: bool, Alice b: bool);
      outputs (Bob "bls12-381.g1"::Element, Alice bool);
      local [scaled] Alice: let h = Curve(g, k);
      local [both] Alice: let c = Both(a, b);
      message [send] group: Alice(h) -> Bob(result);
      return (result, c);
    }
    instance demo: Demo { roles (Alice = Alice, Bob = Bob); }
    entry main = demo;
  })pir";
  Module module;
  module.bindings.push_back({{}, "both", "bool.and", {}, ""});
  Function both;
  both.name = "Both";
  both.arguments = {{"a", "bool"}, {"b", "bool"}};
  both.results = {"bool"};
  both.origin = LogicalOrigin{"Both", {}};
  both.body = Body{
      instruction("join", source::Operation{"both", {}, {}, {"a", "b"}, {"c"}}),
      instruction("", source::Return{{"c"}})};
  module.functions.push_back(std::move(both));
  GenericFunction scale;
  scale.name = "Scale";
  scale.parameters = {{"G", "Group"}};
  scale.requirements = {{{}, "ScalarAction", {"G"}}};
  scale.arguments = {{"g", "group:G"}, {"k", "field:G.Scalar"}};
  scale.results = {"group:G"};
  scale.body = {instruction("scale",
                            source::Operation{
                                "curve.scale", {"G"}, {}, {"g", "k"}, {"h"}}),
                instruction("", source::Return{{"h"}})};
  module.definitions.push_back(std::move(scale));
  module.configurations.push_back(
      {{}, "Curve", "Scale", {{"G", "bls12-381.g1"}}, {}});
  Protocol protocol;
  protocol.name = "Demo";
  protocol.roles = {"Alice", "Bob"};
  protocol.arguments = {{"g", "Alice", "group:bls12-381.g1"},
                        {"k", "Alice", "field:bls12-381.fr"},
                        {"a", "Alice", "bool"},
                        {"b", "Alice", "bool"}};
  protocol.results = {{"Bob", "group:bls12-381.g1"}, {"Alice", "bool"}};
  protocol.body = Body{
      instruction("scaled", LocalCall{"Alice", "Curve", {"g", "k"}, {"h"}}),
      instruction("both", LocalCall{"Alice", "Both", {"a", "b"}, {"c"}}),
      instruction("send", Message{"group", "Alice", "Bob", "h", "result"}),
      instruction("", source::Return{{"result", "c"}})};
  module.protocols.push_back(std::move(protocol));
  module.instances.push_back(
      {{}, "demo", "Demo", {}, {}, {{"Alice", "Alice"}, {"Bob", "Bob"}}});
  module.entries.push_back({{}, "main", "demo"});
  success(checkStructure(module));
  Document built(std::move(module));
  auto parsed = take(parseProtocolDocument(text, "probe.pir"));
  require(encoded(built) == encoded(parsed),
          "independent typed author equals text");
  success(checkProtocolDocument(built));
  success(checkProtocolDocument(parsed));
  require(encode(take(generic::elaborateLibrary(*built.module()))) ==
              encode(take(generic::elaborateLibrary(*parsed.module()))),
          "both frontends use the same specialization path");
  auto printed = take(printProtocol(built.root()));
  require(encoded(take(parseProtocolDocument(printed))) == encoded(built),
          "typed print/read correspondence");
  require(encoded(take(parseProtocolDocument(printJson(encoded(built))))) ==
              encoded(built),
          "codec correspondence");
  auto changed = *built.module();
  changed.definitions.front().body.front().get<source::Operation>()->callee =
      "uninstalled.operation";
  rejects(checkProtocolDocument(Document(changed)), "generic-operation");
  // The source model stays open to new operations while the installed registry
  // controls admission. No new AST variant is needed to express one.
  changed.definitions.front().body.front().get<source::Operation>()->callee =
      "curve.scale";
  changed.configurations.front().arguments.front().second =
      "reference.cyclic-2";
  require(changed.definitions.front().body.front().get<source::Operation>(),
          "generic operation variant");
}
void locations() {
  std::string text = R"pir(/* prefix */ module {
  configure Open = Scale(); // config before its definition
  fn Plain() -> () { return (); }
  fn Scale<G: domain Group>(g: G::Element, k: G::Scalar::Element) -> (G::Element)
    requires (ScalarAction(G)) {
    let h = curve::scale::<G>(g, k); /* trailing op comment */
    return (h);
  }
  fn Other<>() -> () { return (); }
  bind both = bool.and();
  protocol Demo {
    roles (Alice);
    loop 1 carry () -> () {
      loop [inner] 0 carry () -> () {
        local Alice: Plain(); // failure belongs here
        yield ();
      }
      yield ();
    }
    return ();
  }
  instance demo: Demo { roles (Alice = Alice); }
  entry main = demo;
} // suffix)pir";
  auto document = take(parseProtocolDocument(text, "locations.pir"));
  at(document, {2, 0}, "configure Open = Scale();");
  at(document, {3, 2, 0}, "fn Plain() -> () { return (); }");
  at(document, {1, 0, 6, 0}, "let h = curve::scale::<G>(g, k);");
  at(document, {1, 0, 6, 1}, "return (h);");
  at(document, {1, 1}, "fn Other<>() -> () { return (); }");
  at(document, {3, 1, 0}, "bind both = bool.and();");
  at(document, {3, 3, 0, 7, 0, 5, 0, 5, 0}, "local Alice: Plain();");
  at(document, {3, 4, 0}, "instance demo: Demo { roles (Alice = Alice); }");
  at(document, {3, 5, 0}, "entry main = demo;");
  auto rootSpan = span(document, Path{});
  require(rootSpan &&
              document.text().substr(rootSpan->offset, rootSpan->length) ==
                  StringRef(text).drop_front(13).drop_back(10),
          "root remapping extent");
  require(!span(document, Path{3}),
          "library inner codec envelope has no second semantic root");
  source::walk(document.root(), [&](const Node &node) {
    if (auto location = document.span(&node))
      require(location->offset <= text.size() &&
                  location->length <= text.size() - location->offset,
              "all origins in bounds");
  });
  auto invalid = *document.module();
  invalid.protocols.front()
      .body->front()
      .get<Loop>()
      ->body.front()
      .get<Loop>()
      ->body.front()
      .get<LocalCall>()
      ->callee = "Open";
  Document invalidDocument(std::move(invalid), text, "locations.pir");
  auto error = toString(checkProtocolDocument(invalidDocument));
  require(StringRef(error).contains("locations.pir:15:9:") &&
              StringRef(error).contains("generic-open-instance"),
          "nested generic location");
  for (const auto &[source, needle, code] :
       {std::tuple<const char *, const char *, const char *>{
            "module {\n fn Bad<F: domain Bogus>() -> () { return (); }\n}",
            "<stdin>:2:9:", "generic-declared-sort"},
        {"module {\n configure Bad = Missing();\n}",
         "<stdin>:2:2:", "source-name-unresolved"},
        {"module { fn Bad<>() -> () {\n missing::<>();\n return (); } }",
         "<stdin>:2:2:", "source-name-unresolved"}}) {
    success(checkProtocolSyntax(source));
    auto parsed = parseProtocolDocument(source);
    require(!parsed, "name resolution rejects invalid declarations");
    auto message = toString(parsed.takeError());
    require(StringRef(message).contains(needle) &&
                namesIdentifier(message, code),
            "generic record diagnostic");
  }
  auto jsonText = printJson(encoded(document));
  auto jsonDoc = take(parseProtocolDocument(jsonText, "locations.json"));
  const Path nested{3, 3, 0, 7, 0, 5, 0, 5, 0};
  at(jsonDoc, nested, printJson(resolve(document, nested)));
  require(encoded(jsonDoc) == encoded(document),
          "JSON spans do not change carrier");
  auto numeric =
      take(parseJson("[123456789012345678901, [\"x\"], false, null]"));
  require(take(natural((*numeric.getAsArray())[0])) == "123456789012345678901",
          "independent transport parser retains arbitrary precision");
  rejects(decode(numeric), "interactive-shape");
}

void ownershipAndBounds() {
  std::string borrowed(160, 'k');
  A entries{A{"entry", StringRef(borrowed), "absent"}};
  V input = A{"zkc.protocol/1", A{}, A{}, A{}, A{}, std::move(entries)};
  auto content = take(decode(input));
  borrowed.assign("changed");
  input = nullptr;
  auto &module = std::get<Module>(content);
  module.location = Span{0, 5};
  module.entries[0].location = Span{2, 2};
  Document document(std::move(content), "a\n\tb\n", "owned.pir");
  const auto *entry = &document.module()->entries.front();
  require(entry->name == std::string(160, 'k'),
          "codec owns borrowed strings before input destruction");
  auto shared = document;
  require(&shared.root() == &document.root(), "copies share immutable storage");
  document = Document(Module{});
  require(shared.span(entry).has_value() && entry->name.size() == 160,
          "borrow survives while a snapshot copy remains");
  Entry foreign = *entry;
  require(!shared.span(&foreign) && !shared.span(nullptr),
          "foreign/null references are not snapshot members");
  require(shared.lineColumn(0) == std::make_pair(1u, 1u) &&
              shared.lineColumn(1) == std::make_pair(1u, 2u) &&
              shared.lineColumn(2) == std::make_pair(2u, 1u) &&
              shared.lineColumn(4) == std::make_pair(2u, 3u) &&
              shared.lineColumn(std::numeric_limits<size_t>::max()) ==
                  std::make_pair(3u, 1u),
          "byte coordinates clamp at EOF");
  auto copy = *shared.module();
  copy.location = Span{1, std::numeric_limits<size_t>::max()};
  copy.entries[0].location = Span{2, 0};
  Document overflow(copy, "x");
  require(!overflow.span(overflow.module()) &&
              !overflow.span(&overflow.module()->entries[0]),
          "invalid metadata omitted without arithmetic overflow");
  require(encode(copy) == encode(*overflow.module()),
          "metadata excluded from portable source");
  Document unicode(Module{}, "\xc3\xa9\n");
  require(unicode.lineColumn(2) == std::make_pair(1u, 3u), "columns are bytes");
  copy.entries.front().name = "other";
  require(shared.module()->entries.front().name.size() == 160,
          "mutable copy cannot edit snapshot");
  Module invalid;
  invalid.entries.push_back({{}, "e", "absent"});
  rejects(checkProtocolDocument(Document(invalid)),
          "interactive-entry-instance");
  invalid.entries.front().name = std::string("bad\xff", 4);
  rejects(checkStructure(invalid), "source-string");
  Body body{instruction("", Yield{})};
  for (unsigned i = 0; i < 66; ++i) {
    Loop loop;
    loop.count.value = "0";
    loop.body = std::move(body);
    body = {instruction("loop" + std::to_string(i), std::move(loop))};
  }
  Protocol deep;
  deep.name = "Deep";
  deep.body = std::move(body);
  Module tooDeep;
  tooDeep.protocols.push_back(std::move(deep));
  rejects(checkStructure(tooDeep), "interactive-body");
  Module emptyLibrary;
  emptyLibrary.library = true;
  require(encode(take(decode(encode(emptyLibrary)))) == encode(emptyLibrary),
          "empty library envelope preserved");
}

void structuralBoundaries() {
  // Measure the exact escaped encoding, including UTF-8 and control bytes.
  source::Construction descriptor;
  descriptor.suite = "\n\\\"\001\xc3\xa9";
  constexpr size_t limit = 1024 * 1024;
  size_t bytes = printJson(encode(descriptor)).size();
  descriptor.suite.append(limit - bytes, 'x');
  require(printJson(encode(descriptor)).size() == limit,
          "test hits exact portable byte boundary");
  success(checkStructure(descriptor));
  descriptor.suite.push_back('x');
  rejects(checkStructure(descriptor), "source-limit");
  descriptor.suite.clear();
  descriptor.identity = static_cast<source::Construction::Identity>(99);
  rejects(checkStructure(descriptor), "source-model-shape");
  Participants projected;
  projected.stage = static_cast<Participants::Stage>(99);
  rejects(checkStructure(projected), "source-model-shape");
  projected.stage = Participants::Stage::Logical;
  Participant participant;
  participant.body = {instruction("stop", Stop{"unexpected_role", "reject"})};
  projected.participants.push_back(participant);
  rejects(checkStructure(projected), "source-model-shape");
  Loop loop;
  loop.count.kind = static_cast<LoopCount::Kind>(99);
  projected.participants.front().body = {instruction("bad", loop)};
  rejects(checkStructure(projected), "source-model-shape");
  Module module;
  Function function;
  function.name = "F";
  function.origin = LogicalOrigin{"F", {}};
  function.body = Body{instruction("not_serialized", source::Return{})};
  module.functions.push_back(function);
  rejects(checkStructure(module), "source-model-shape");
  module.functions.front().body = Body{
      instruction("op", source::Operation{"op", {"open_static"}, {}, {}, {}})};
  rejects(checkStructure(module), "source-model-shape");
  rejects(sourceSnapshot(module), "source-model-shape");
  module.functions.front().body = Body{instruction("", source::Return{})};
  const auto snapshot = take(sourceSnapshot(module));
  module.location = Span{5, 7};
  module.functions.front().location = Span{20, 30};
  require(take(sourceSnapshot(module)) == snapshot,
          "diagnostic origins do not enter source identity");
  const char *json =
      R"json(["zkc.library/1",[],[],["zkc.protocol/1",[],[],[],[],[]]])json";
  auto document = take(parseProtocolDocument(json));
  auto location = document.span(document.module());
  require(location && location->offset == 0 &&
              location->length == StringRef(json).size(),
          "library semantic root has one exact outer-envelope origin");
  RecordMap records;
  encode(document.root(), &records);
  require(records.count({}) == 1 && records.count({3}) == 0,
          "inner library codec envelope is not a second semantic node");
}

void malformedOriginLocation() {
  const char *text = R"json(["zkc.protocol/1", [], [
    ["function", "F", [], [], [["return", []]], []]
  ], [], [], []])json";
  rejects(parseProtocolDocument(text, "origin.json"), "origin.json:2:5:");
}

void syntaxBoundary() {
  for (StringRef text :
       {"", "// only a comment", "module", "module {", "module {} x",
        "module { fn F<>() -> () { op::<>(", "[", "[\"x\",]"}) {
    auto parsed = parseProtocolDocument(text);
    require(!bool(parsed), "incomplete document refused");
    consumeError(parsed.takeError());
    auto formatted = formatProtocol(text);
    require(!bool(formatted), "incomplete format refused");
    consumeError(formatted.takeError());
  }
  for (StringRef text : {"[]", "[null]", "[\"zkc.library/1\"]"}) {
    auto raw = take(parseJson(text));
    auto decoded = decode(raw);
    require(!decoded, "malformed JSON cannot become a typed document");
    consumeError(decoded.takeError());
  }
  const char *missing = "module { fn F<>() -> () {\n missing::<>(); // keep "
                        "me\n return (); } }";
  auto inspection = take(inspectProtocolSyntax(missing));
  const auto *syntax = inspection.getAsObject();
  require(syntax && syntax->getString("kind") == "syntax-inspection" &&
              syntax->getString("format") == "pir-text",
          "syntax inspection is explicitly distinct from common source");
  const auto *call = syntax->getObject("content")
                         ->getArray("functions")
                         ->front()
                         .getAsObject()
                         ->getArray("body")
                         ->front()
                         .getAsObject();
  require(call->getString("kind") == "unresolved-call" &&
              call->getString("callee") == "missing" &&
              call->getArray("staticArguments")->empty(),
          "unknown calls remain unresolved with explicit empty statics");
  success(checkProtocolSyntax(missing));
  auto formatted = take(formatProtocol(missing));
  require(StringRef(formatted).contains("// keep me") &&
              take(formatProtocol(formatted)) == formatted,
          "invalid semantics still format with tokens/comments");
  success(checkProtocolSyntax(formatted));
  rejects(parseProtocolDocument(missing), "source-name-unresolved");
  rejects(parseProtocolDocument(formatted), "source-name-unresolved");
  // Invalid common models remain expressible independently of text resolution.
  Module invalid;
  invalid.library = true;
  GenericFunction function;
  function.name = "F";
  function.body = {
      instruction("__site_0", source::Operation{"missing", {}, {}, {}, {}}),
      instruction("", source::Return{})};
  invalid.definitions.push_back(std::move(function));
  Document parsed(std::move(invalid));
  rejects(checkProtocolDocument(parsed), "generic-operation");
  auto json = printJson(encoded(parsed));
  auto decoded = take(parseProtocolDocument(json));
  require(encoded(decoded) == encoded(parsed),
          "JSON retains invalid common records");
  rejects(checkProtocolDocument(decoded), "generic-operation");
  rejects(formatProtocol(json), "generic-operation");
  for (StringRef argument : {"F-", "F--", "F_long-"}) {
    auto text =
        (Twine("module { fn f<") + argument + ": domain Field>(x: " + argument +
         "::Element) -> (" + argument + "::Element) requires (Field(" +
         argument + ")) { let y = field::add::<" + argument +
         " >(x, x); return (y); } }")
            .str();
    auto original = take(parseProtocolDocument(text));
    success(checkProtocolDocument(original));
    auto formatted = take(formatProtocol(text));
    require(encoded(take(parseProtocolDocument(formatted))) ==
                encoded(original),
            "formatting preserves a name ending in '-' before '>'");
    require(take(formatProtocol(formatted)) == formatted,
            "hyphen boundary formatting is idempotent");
    auto printed = take(printProtocol(original.root()));
    require(encoded(take(parseProtocolDocument(printed))) == encoded(original),
            "readable printer preserves the same lexical boundary");
  }

  rejects(parseProtocolDocument("[\"\\ud800\"]"), "source-string");
  rejects(parseProtocolDocument(std::string(1024 * 1024 + 1, ' ')),
          "source-limit");
  auto quoted = take(
      parseProtocolDocument("[\"zkc.protocol/1\", [], [], [], [], [[\"entry\", "
                            "\"\\ud83d\\ude00\", \"[,]\\\\\\\"\"]]]"));
  require(quoted.module()->entries.front().name == "\xf0\x9f\x98\x80",
          "JSON Unicode and escaped delimiters preserved");
}

void parserLimitsAndLocations() {
  // Interleaved generic and common declarations retain the exact locations
  // of their own records in the immutable document.
  std::string text = "module {\n";
  for (unsigned i = 0; i < 128; ++i) {
    auto suffix = std::to_string(i);
    text += "fn G" + suffix + "<>() -> () { return (); }\n";
    text += "configure C" + suffix + " = G" + suffix + "();\n";
    text += "fn F" + suffix + "() -> () external;\n";
  }
  text += "}";
  auto interleaved = take(parseProtocolDocument(text));
  for (unsigned i = 0; i < 128; ++i) {
    auto suffix = std::to_string(i);
    at(interleaved, {1, i}, "fn G" + suffix + "<>() -> () { return (); }");
    at(interleaved, {2, i}, "configure C" + suffix + " = G" + suffix + "();");
    at(interleaved, {3, 2, i}, "fn F" + suffix + "() -> () external;");
  }
  std::string entries;
  for (unsigned i = 0; i < 32768; ++i)
    entries += "entry e" + std::to_string(i) + " = i;";
  // Keep references source-well-formed while exercising the independent
  // per-section declaration bound. Name resolution now precedes common
  // emission.
  const std::string entryContext =
      "module { protocol P { roles (A); return (); } "
      "instance i: P { roles (A=A); } ";
  require(take(parseProtocolDocument(entryContext + entries + "}"))
                  .module()
                  ->entries.size() == 32768,
          "declaration bound inclusive");
  rejects(parseProtocolDocument(entryContext + entries + "entry e = i;}"),
          "source-limit");
  std::string body;
  for (unsigned i = 0; i < 32768; ++i)
    body += "return ();";
  // This exercises the parser bound, not semantic validity of unreachable
  // returns.
  success(checkProtocolSyntax("module { fn F<>() -> () {" + body + "}}"));
  rejects(parseProtocolDocument("module { fn F<>() -> () {" + body + "}}"),
          "source-control-return");
  rejects(parseProtocolDocument("module { fn F<>() -> () {" + body +
                                "return ();}}"),
          "source-limit");
  std::string loop = "yield ();";
  for (unsigned i = 0; i < 64; ++i)
    loop = "loop 0 carry () -> () {" + loop + "} yield ();";
  auto nested = "module { protocol P { roles (Alice); " + loop + "}}";
  // yield at top level is a semantic editing error, not an incomplete grammar.
  success(checkProtocolSyntax(nested));
  rejects(parseProtocolDocument(nested), "source-protocol-return");
  auto complete = loop.substr(0, loop.size() - StringRef("yield ();").size()) +
                  "return ();";
  auto deepest = take(parseProtocolDocument(
      "module { protocol P { roles (Alice); " + complete + "}}"));
  Path path{3, 0, 7, 0};
  for (unsigned i = 1; i < 64; ++i)
    path.insert(path.end(), {5, 0});
  require((*resolve(deepest, path).getAsArray())[1].getAsString() ==
              "__site_63",
          "anonymous paths at maximum body depth");
  rejects(parseProtocolDocument(
              "module { protocol P { roles (Alice); loop 0 carry () -> () {" +
              loop + "} return ();}}"),
          "source-depth");
  // A tiny deeply nested JSON spelling can otherwise allocate millions of
  // copied path components despite satisfying the portable byte/depth limits.
  std::string leaves;
  for (unsigned i = 0; i < 2100; ++i)
    leaves += (i ? ",[]" : "[]");
  std::string metadataHeavy =
      std::string(500, '[') + leaves + std::string(500, ']');
  require(bool(take(parseJson(metadataHeavy)).getAsArray()),
          "coordinate budget example is valid portable JSON syntax");
  rejects(parseProtocolDocument(metadataHeavy), "source-limit");
  std::string withinBudget =
      std::string(500, '[') + "[]" + std::string(500, ']');
  auto raw = take(parseJson(withinBudget));
  auto malformed = decode(raw);
  require(!malformed, "deep portable JSON is not a typed source module");
  consumeError(malformed.takeError());
}
} // namespace

int main() {
  builderProbe();
  locations();
  ownershipAndBounds();
  structuralBoundaries();
  malformedOriginLocation();
  syntaxBoundary();
  parserLimitsAndLocations();
  // A compact unused library must not allocate configurations x operation
  // maps. Each configuration references a shared declaration's coordinates.
  std::string many = "module { fn Many<>(x: bool) -> () {\n";
  for (unsigned i = 0; i < 1024; ++i)
    many += "[guard" + std::to_string(i) + "] control::require(x);\n";
  many += "return (); }\n";
  for (unsigned i = 0; i < 1024; ++i)
    many += "configure Alias" + std::to_string(i) + " = Many();\n";
  many += "}";
  auto compact =
      take(resolveProtocolSites(*take(parseProtocolDocument(many)).module()));
  require(
      compact.definitions.size() == 1024 &&
          compact.configurations.size() == 1024 && compact.functions.empty(),
      "configuration aliases share site storage without Cartesian expansion");
  source::Construction descriptor;
  descriptor.identity = source::Construction::Identity::Normalized;
  descriptor.entry = "main";
  descriptor.producer = "P";
  descriptor.validator = "V";
  descriptor.randomness = "coins";
  descriptor.draws = {{"Alias1023", "guard1023"}};
  descriptor.acceptance = "0";
  descriptor.suite = "merlin3.bls12-381.fr64be/1";
  auto selector = take(compact.descriptor(descriptor));
  require(selector.draws == Assignments{{"Alias1023", "site1023"}},
          "shared declaration lookup retains configuration identity");
  // Inspection is a returned artifact, so it must outlive the authoring
  // Document. LLVM JSON StringRef values alone do not own their storage.
  auto inspected = [] {
    auto document = take(parseProtocolDocument(
        "module { protocol IndependentlyOwnedProtocol { roles (Alice); "
        "stop [independently_owned_site] Alice reject; } }",
        "independently-owned-source-file.pir"));
    return take(zkc::inspectSource(document));
  }();
  const auto &occurrence =
      *inspected.getAsObject()->getArray("occurrences")->front().getAsObject();
  require(occurrence.getString("owner") == "IndependentlyOwnedProtocol" &&
              occurrence.getString("kind") == "stop" &&
              occurrence.getObject("location")->getString("file") ==
                  "independently-owned-source-file.pir",
          "inspection owns source metadata after Document destruction");
  outs() << "source document: " << checks
         << " builder, ownership, map and syntax checks\n";
}
