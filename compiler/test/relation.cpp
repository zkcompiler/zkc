#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::relation;

static void require(bool success, StringRef message) {
  if (!success) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> static T value(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
template <typename T> static void refuses(Expected<T> result, StringRef code) {
  require(!result, "expected rejection");
  require(toString(result.takeError()) == code, "wrong rejection");
}

int main() {
  // Public output z[1] and input z[2]; private z[3]. z[2]*z[3]=z[1].
  Constraint row{LinearForm{{2, "1"}}, LinearForm{{3, "1"}},
                 LinearForm{{1, "1"}}};
  auto relation = value(R1CS::create("koala-bear", 4, 1, 1, {row}));
  auto parsed = value(parseR1CSText(zkc::printJson(relation.encode())));
  require(value(decodeR1CS(parsed)).identity() == relation.identity(),
          "bounded text reader changed the relation");
  refuses(parseR1CSText(std::string(9, '[')), "relation-depth-limit");
  refuses(parseR1CSText("[\"" + std::string(1025, 'x') + "\"]"),
          "relation-string-limit");
  refuses(parseR1CSText("{}"), "relation-json");
  refuses(parseR1CSText(std::string(Limits::bytes + 1, ' ')),
          "relation-byte-limit");
  auto honest = value(evaluate(relation, {"21", "3"}, {"1", "21", "3", "7"}));
  require(honest.bound && honest.satisfied, "honest relation");
  require(honest.products[0] == std::vector<std::string>{"3"} &&
              honest.products[1] == std::vector<std::string>{"7"} &&
              honest.products[2] == std::vector<std::string>{"21"},
          "actual matrix views");
  auto zero = value(evaluate(relation, {"0", "0"}, {"0", "0", "0", "0"}));
  require(!zero.bound && !zero.satisfied, "unpinned ONE must not satisfy");
  auto swap = value(evaluate(relation, {"3", "21"}, {"1", "21", "3", "7"}));
  require(!swap.satisfied, "public layout must bind");
  auto falseWitness =
      value(evaluate(relation, {"21", "3"}, {"1", "21", "3", "8"}));
  require(falseWitness.bound && !falseWitness.satisfied,
          "false private witness");
  refuses(evaluate(relation, {"21"}, {"1", "21", "3", "7"}),
          "relation-assignment-shape");
  refuses(evaluate(relation, {"21", "3"}, {"1", "21", "3", "2130706433"}),
          "relation-coefficient");

  Constraint repeated{LinearForm{{2, "2"}, {3, "0"}, {2, "2130706432"}}, row[1],
                      row[2]};
  auto normalized = value(R1CS::create("koala-bear", 4, 1, 1, {repeated}));
  require(normalized.identity() == relation.identity(),
          "duplicate/zero normalization");
  auto duplicate = value(R1CS::create("koala-bear", 4, 1, 1, {row, row}));
  require(duplicate.identity() != relation.identity(), "ordered rows bind");
  require(duplicate.deduplicate().identity() == relation.identity(),
          "constraint deduplication");
  auto empty = value(R1CS::create("koala-bear", 1, 0, 0, {}));
  require(value(evaluate(empty, {}, {"1"})).satisfied, "empty relation");
  require(!value(evaluate(empty, {}, {"0"})).satisfied, "empty relation ONE");
  auto roundtrip = value(
      decodeR1CS(value(zkc::parseJson(zkc::printJson(relation.encode())))));
  require(roundtrip.identity() == relation.identity(), "canonical roundtrip");
  auto fieldChanged = value(R1CS::create("bls12-381.fr", 4, 1, 1, {row}));
  require(fieldChanged.identity() != relation.identity(), "field binds");
  auto publicChanged = value(R1CS::create("koala-bear", 4, 0, 2, {row}));
  require(publicChanged.identity() != relation.identity(),
          "public split binds");
  refuses(R1CS::create("unknown", 4, 1, 1, {row}), "relation-field");
  refuses(R1CS::create("koala-bear", 3, 1, 1, {row}), "relation-column");
  refuses(R1CS::create("koala-bear", 2, 1, 1, {}), "relation-dimension");
  row[0][0].coefficient = "01";
  refuses(R1CS::create("koala-bear", 4, 1, 1, {row}), "relation-coefficient");
  refuses(readR1CS("r1cs"), "relation-truncated");
  refuses(readR1CS("abcd"), "relation-magic");
  require(zkc::mlirNestingWithinLimit("\"" + std::string(200, '[') + "\""),
          "quoted delimiters do not consume parser depth");
  require(
      zkc::mlirNestingWithinLimit("//" + std::string(200, '{') + "\nmodule {}"),
      "comment delimiters do not consume parser depth");
  require(zkc::mlirNestingWithinLimit("(i1) -> tuple<i1>"),
          "function arrow is not an angle delimiter");
  require(!zkc::mlirNestingWithinLimit(std::string(65, '[')),
          "depth is bounded before parsing");
  outs() << "relation model controls passed\n";
}
