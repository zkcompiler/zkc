#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Inspection.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const char *prefix = R"(module m
domain F = field("bls12-381.fr")
type Fixed<T: Type + Copy + Drop, rows: nat> = builtin("oracle.table", T, rows)
type Table<T: Type + Copy + Drop> = builtin("oracle.table", T)
type Oracle<K: OracleKind> = builtin("oracle", K)
type Vec = builtin("vector", F)
type Word = Oracle<Fixed<F, rows = 16>>
)";
Expected<CheckedProject> check(StringRef code) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured =
      capture({{"m", std::string(prefix) + code.str(), "oracle.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
CheckedOriginal original(StringRef code) {
  auto project = take(check(code));
  take(inspectWrittenSource(project));
  return take(prepareOriginal(take(closeNativeRun(project, "m::Run"))));
}
unsigned occurrenceCount(StringRef text, StringRef value) {
  unsigned n = 0;
  while (text.contains(value)) {
    text = text.split(value).second;
    ++n;
  }
  return n;
}
} // namespace
int main() {
  Cases cases;
  cases.run("oracle calls and returns retain components under role mapping", [] {
    auto source = original(
        R"(pub protocol Relay roles(A, B)(word: Word @A -> B) -> Word @A -> B:
    return word

pub protocol Run roles(P, V)(word: Word @P -> V) -> F @V:
    received <- Relay(word) @(P, V)
    answer <- query received at 0
    return answer
)");
    require(source.bytes().contains("protocol.oracle_components") &&
                source.bytes().contains("protocol.oracle_input") &&
                source.bytes().contains("protocol.oracle_query"),
            "logical call ABI lost its data/anchor decomposition");
  });
  cases.run(
      "custody ports and repeated queries preserve every reached event", [] {
        auto source = original(R"(pub protocol Run roles(P, V)(
    word: Word @P -> V; position: index @V
) -> F @V:
    unused <- query word at position
    answer <- query word at position
    return answer
)");
        require(occurrenceCount(source.bytes(), "protocol.oracle_query") == 2,
                "query events were merged or dropped");
      });
  cases.run("sized delivery and query reuse the checked oracle semantics", [] {
    auto source = original(R"(pub protocol Run roles(P, V)(xs: Vec @P) -> F @V:
    word <- send xs from P to V as oracle<Fixed<F, 16>>
    answer <- query word at 0
    return answer
)");
    require(occurrenceCount(source.bytes(), "protocol.oracle_send") == 1 &&
                occurrenceCount(source.bytes(), "protocol.oracle_query") == 1,
            "delivery or query disappeared");
  });
  cases.run("dynamic delivery retains shared rows and unsigned bound", [] {
    auto source = original(R"(pub protocol Run roles(P, V)(
    xs: Vec @P; rows: index @(P, V)
) -> F @V:
    word <- send xs from P to V as oracle<Table<F>>(rows = rows) max 18446744073709551615
    answer <- query word at 0
    return answer
)");
    require(source.bytes().contains("18446744073709551615"),
            "dynamic maximum narrowed");
  });
  cases.run("holder data and shared shape remain distinct views", [] {
    auto source = original(
        R"(pub protocol Run roles(P, V)(word: Word @P -> V) -> index @(P, V):
    data = oracle.data(word)
    dynamic = oracle.forget_rows(word)
    rows = oracle::rows(dynamic)
    return rows
)");
    require(source.bytes().contains("protocol.oracle_contents") &&
                source.bytes().contains("protocol.oracle_shape") &&
                source.bytes().contains("protocol.oracle_forget_shape"),
            "an oracle view disappeared");
  });
  cases.run("dynamic port bounds are retained as authored shape attributes",
            [] {
              auto project = take(check(R"(#[shape(word.rows, bound = 32)]
pub protocol Run roles(P, V)(word: Oracle<Table<F>> @P -> V) -> F @V:
    answer <- query word at 0
    return answer
)"));
              auto written = take(inspectWrittenSource(project));
              require(written.find("oracle_shapes") != std::string::npos &&
                          written.find("oracle_shape") != std::string::npos,
                      "authored shape constraint was lost");
              take(prepareOriginal(take(closeNativeRun(project, "m::Run"))));
            });
  for (StringRef attribute :
       {"#[shape(missing.rows, bound = 32)]",
        "#[shape(word.columns, bound = 32)]", "#[shape(word.rows, value = 32)]",
        "#[shape(word.rows, bound = 32)]\n#[shape(word.rows, bound = 16)]"})
    cases.run("invalid shape attachment refuses: " + attribute, [&] {
      refuses(check((attribute + R"(
pub protocol Run roles(P, V)(word: Oracle<Table<F>> @P -> V) -> F @V:
    answer <- query word at 0
    return answer
)")
                        .str()),
              "source.oracle-shape");
    });
  cases.run("bounded sequence retains anchors through append and selection",
            [] {
              auto source = original(
                  R"(pub protocol Run roles(P, V)(word: Word @P -> V) -> F @V:
    empty = oracle.empty<Fixed<F, 16>, 4>() @(P, V)
    words <- oracle.append(empty, word)
    size = oracle.length(words)
    selected <- oracle.at(words, 0)
    answer <- query selected at 0
    return answer
)");
              for (auto op : {"oracle_sequence_empty", "oracle_sequence_append",
                              "oracle_sequence_at", "oracle_sequence_length"})
                require(source.bytes().contains(op),
                        "sequence operation disappeared");
            });
  cases.run("plain data cannot acquire oracle custody", [] {
    refuses(
        check(R"(pub protocol Run roles(P, V)(word: bool @P -> V) -> bool @V:
    return word
)"),
        "source.oracle-port");
  });
  for (StringRef source :
       {"def helper(value: bool @P) -> bool:\n    value\n",
        "local def helper(value: bool @P -> V) -> bool:\n    return value\n",
        "struct Record:\n    value: bool @P -> V\n",
        "enum Choice:\n    Some(bool @P)\n"})
    cases.run("ordinary declarations cannot discard role annotations: " +
                  source,
              [&] { refuses(check(source), "source.roles"); });
  cases.run("service classification cannot discard oracle custody", [] {
    refuses(
        check(R"(pub protocol Run roles(P, V)(coins: Random<F> @P -> V) -> F @V:
    value <- coins.draw()
    return value
)"),
        "source.oracle-port");
  });
  cases.run("oracle handles cannot become ordinary shared data", [] {
    refuses(check(R"(pub protocol Run roles(P, V)(word: Word @(P, V)) -> F @V:
    answer <- query word at 0
    return answer
)"),
            "source.oracle-port");
  });
  cases.run("query requires ordered binding", [] {
    refuses(check(R"(pub protocol Run roles(P, V)(word: Word @P -> V) -> F @V:
    answer = query word at 0
    return answer
)"),
            "syntax.line");
  });
  cases.run("custody requires a distinct holder", [] {
    refuses(check(R"(pub protocol Run roles(P, V)(word: Word @P -> P) -> F @P:
    answer <- query word at 0
    return answer
)"),
            "source.oracle-port");
  });
  for (auto [statement, code] :
       {std::pair{"answer: F @P <- query word at 0", "source.roles"},
        {"data: Vec @V = oracle.data(word)", "source.roles"},
        {"alias: Word @V = word", "source.oracle-role"},
        {"rows <- oracle.rows(word)", "source.action"},
        {"empty = oracle.empty<Fixed<F, 16>, 4>() @(P, V)\n    words = "
         "oracle.append(empty, word)",
         "source.action"}})
    cases.run(Twine("refuse incorrect oracle placement or order: ") + statement,
              [statement = statement, code = code] {
                refuses(check("pub protocol Run roles(P, V)(word: Word @P -> "
                              "V) -> bool @V:\n    " +
                              std::string(statement) + "\n    return true\n"),
                        code);
              });
  for (auto [statement, code] :
       {std::pair{"word <- send xs to V as oracle<Fixed<F, 16>>",
                  "source.oracle-role"},
        {"word <- send xs from P to V as oracle<Table<F>>",
         "source.oracle-shape"},
        {"word <- send xs from P to V as oracle<Fixed<F, 16>>(rows = rows) max "
         "16",
         "source.oracle-shape"}})
    cases.run(Twine("refuse malformed oracle delivery: ") + statement,
              [statement = statement, code = code] {
                refuses(check("pub protocol Run roles(P, V)(xs: Vec @P; rows: "
                              "index @(P, V)) -> bool @V:\n    " +
                              std::string(statement) + "\n    return true\n"),
                        code);
              });
  for (StringRef call : {"oracle.rows(word, word)", "oracle.rows(x = word)",
                         "oracle.rows<16>(word)", "oracle.unknown(word)"})
    cases.run("oracle syntax rejects malformed operation: " + call, [&] {
      refuses(
          check(
              (R"(pub protocol Run roles(P, V)(word: Word @P -> V) -> index @(P, V):
    rows = )" + call +
               "\n    return rows\n")
                  .str()),
          "source.oracle-action");
    });
  return cases.result();
}
