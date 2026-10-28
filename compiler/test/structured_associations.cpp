#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include <map>
#include <set>

using namespace llvm;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
using Path = std::vector<unsigned>;
Path child(Path parent, std::initializer_list<unsigned> suffix) {
  parent.insert(parent.end(), suffix.begin(), suffix.end());
  return parent;
}
const json::Value &at(const json::Value &value, ArrayRef<unsigned> path) {
  auto *current = &value;
  for (unsigned part : path) {
    auto *array = current->getAsArray();
    require(array && part < array->size(), "dangling structured coordinate");
    current = &(*array)[part];
  }
  return *current;
}
void blockRows(const json::Value &value, const Path &path,
               std::set<Path> &expected) {
  auto &block = *value.getAsArray();
  require(block[0].getAsString() == "block", "not a block");
  const auto &instructions = *block[1].getAsArray();
  for (unsigned i = 0; i < instructions.size(); ++i) {
    auto row = child(path, {1, i});
    expected.insert(row);
    const auto &regions = *(*instructions[i].getAsArray())[3].getAsArray();
    for (unsigned r = 0; r < regions.size(); ++r) {
      auto region = child(row, {3, r});
      expected.insert(region);
      blockRows((*regions[r].getAsArray())[2], child(region, {2}), expected);
    }
  }
  expected.insert(child(path, {2}));
}
std::set<Path> expectedRows(const json::Value &snapshot) {
  std::set<Path> expected;
  for (unsigned table : {4, 5, 6, 7, 8}) {
    const auto &rows = *at(snapshot, {table}).getAsArray();
    for (unsigned i = 0; i < rows.size(); ++i) {
      Path path{table, i};
      expected.insert(path);
      const auto &row = *rows[i].getAsArray();
      if (table == 4) {
        for (unsigned c = 0; c < row[3].getAsArray()->size(); ++c)
          expected.insert(child(path, {3, c}));
        expected.insert(child(path, {4}));
      } else if (table == 7 && row[0].getAsString() == "function") {
        blockRows(row[9], child(path, {9}), expected);
      }
    }
  }
  const auto &declarations = *at(snapshot, {10}).getAsArray();
  for (unsigned table : {0, 1})
    for (unsigned i = 0; i < declarations[table].getAsArray()->size(); ++i)
      expected.insert({10, table, i});
  return expected;
}
void coverage(StringRef original, const StructuredSource &source) {
  auto snapshot = take(json::parse(source.bytes));
  auto expected = expectedRows(snapshot);
  std::set<Path> actual;
  for (const auto &association : source.associations) {
    at(snapshot, association.row);
    require(actual.insert(association.row).second, "duplicate row association");
    require(association.original.has_value(),
            "written operation lost its range");
    const auto &range = *association.original;
    require(range.begin < range.end && range.end <= original.size(),
            "invalid original range");
    auto token = original.slice(range.begin, range.end);
    if (token.starts_with("\"") && token.ends_with("\""))
      token = token.drop_front().drop_back();
    StringRef operation = association.operation;
    require(token == operation || token == operation.rsplit('.').second,
            "range does not select the original operation name: " + token);
    auto prefix = original.take_front(range.begin);
    unsigned line = 1 + prefix.count('\n');
    auto last = prefix.rfind('\n');
    unsigned column =
        last == StringRef::npos ? range.begin + 1 : range.begin - last;
    require(range.line == line && range.column == column,
            "original line/column differs from the supplied bytes");
  }
  require(actual == expected, "row associations do not cover the emitted unit");
}
StructuredSource exportSource(StringRef bytes, StringRef symbol = "main") {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  return take(exportStructuredSource(bytes, symbol, context));
}
std::string read(StringRef path) {
  auto buffer = MemoryBuffer::getFile(path);
  require(bool(buffer), "fixture could not be read: " + path);
  return (*buffer)->getBuffer().str();
}
std::string simple() {
  return R"(module { "protocol.module"() ({
"protocol.func"() ({ ^entry(%flag:i1):
  "protocol.return"(%flag) : (i1)->() loc("misleading-file":700:9)
}) {sym_name="main",origin=["main",[]],function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })";
}
} // namespace
int main() {
  Cases cases;
  for (StringRef fixture : {"finite/total-state.mlir", "finite/unit-state.mlir",
                            "structured-source/loops-and-captures.mlir",
                            "structured-source/nested-controls.mlir",
                            "structured-source/math-operations.mlir",
                            "structured-source/shared-fold.mlir",
                            "structured-source/open-components.mlir",
                            "structured-source/realization-finite.mlir",
                            "structured-source/realization-projection.mlir"})
    cases.run(fixture, [&] {
      auto bytes =
          read((Twine(ZKC_ASSOCIATION_FIXTURES) + "/" + fixture).str());
      auto symbol =
          fixture.ends_with("loops-and-captures.mlir") ? "entry" : "main";
      auto source = exportSource(bytes, symbol);
      coverage(bytes, source);
      require(source.bytes == exportSource(bytes, symbol).bytes,
              "association retention changed export bytes");
    });
  cases.run(
      "lexical coordinates ignore loc annotations and follow whitespace", [] {
        auto original = simple();
        auto source = exportSource(original);
        coverage(original, source);
        auto shifted = "\n  " + original;
        auto later = exportSource(shifted);
        coverage(shifted, later);
        require(source.associations.size() == later.associations.size(),
                "whitespace changed association coverage");
        for (auto [left, right] :
             llvm::zip_equal(source.associations, later.associations)) {
          require(left.row == right.row && left.operation == right.operation &&
                      left.derivation == right.derivation,
                  "whitespace changed the row selected");
          require(right.original->begin == left.original->begin + 3 &&
                      right.original->line == left.original->line + 1,
                  "associations did not follow the actual bytes");
        }
        auto first = take(json::parse(source.bytes));
        auto second = take(json::parse(later.bytes));
        require((*first.getAsArray())[2] != (*second.getAsArray())[2],
                "different original bytes kept the same identity");
        (*second.getAsArray())[2] = (*first.getAsArray())[2];
        require(first == second, "whitespace changed the logical snapshot");
      });
  cases.run(
      "scoped regions and derived computations retain different origins", [] {
        auto original = read(ZKC_ASSOCIATION_FIXTURES
                             "/structured-source/nested-controls.mlir");
        auto source = exportSource(original);
        auto snapshot = take(json::parse(source.bytes));
        bool region = false, computation = false;
        for (const auto &association : source.associations) {
          if (association.derivation ==
              StructuredSourceDerivation::Computation) {
            require(association.row.size() == 2 && association.row[0] == 7,
                    "computation points outside the definition table");
            require(association.operation == "exec.fold" ||
                        association.operation == "exec.collect" ||
                        association.operation == "exec.compute",
                    "computation lost its actual producing operation");
            computation = true;
          }
          if (association.derivation ==
                  StructuredSourceDerivation::ScopedExecution &&
              association.operation == "func.func") {
            const auto *row = at(snapshot, association.row).getAsArray();
            require(row && row->size() == 3 && (*row)[0].getAsArray(),
                    "closed region origin does not select its emitted region");
            region = true;
          }
        }
        require(region && computation,
                "scoped and derived coverage was not exercised");
      });
  cases.run("row origins join the checked source correspondence", [] {
    using namespace zkc::language;
    auto capture = take(zkc::language::capture({{"associate",
                                                 R"(
      module associate;
      protocol Run roles(P)(flag:bool@P)->(ok:bool@P) {
        return(ok=flag);
      }
    )",
                                                 {}}}));
    auto project = take(analyze(capture).checkedProject());
    auto entry = take(closeSubject(project, "associate::Run"));
    auto original = take(prepareOriginal(entry));
    auto source = exportSource(original.bytes(), entry.protocol().symbol);
    coverage(original.bytes(), source);
    std::map<std::pair<unsigned, unsigned>, std::vector<Span>> byPosition;
    for (const auto &location : original.locations())
      byPosition[{location.line, location.column}].push_back(location.source);
    unsigned joined = 0;
    for (const auto &association : source.associations) {
      const auto &range = *association.original;
      auto found = byPosition.find({range.line, range.column});
      if (found != byPosition.end()) {
        require(!found->second.empty(), "source association was empty");
        ++joined;
      }
    }
    require(joined >= 2,
            "declaration and body did not join checked source spans");
  });
  return cases.result();
}
