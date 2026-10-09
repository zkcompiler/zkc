#include "zkc/Contracts/RingExpression.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include <string>

// Test transport only. Each consumer admits the same raw candidate
// independently.
int main() {
  std::string line;
  while (std::getline(std::cin, line)) {
    auto expression = zkc::ring::readExpressionText(line);
    if (!expression) {
      llvm::consumeError(expression.takeError());
      llvm::outs() << "{\"accepted\":false}\n";
      continue;
    }
    llvm::json::Array facts;
    for (const auto &fact : expression->facts())
      facts.push_back(llvm::json::Array{fact.field, fact.degree, fact.depth});
    llvm::outs() << zkc::printJson(
                        llvm::json::Object{{"accepted", true},
                                           {"arena", expression->encode()},
                                           {"identity", expression->identity()},
                                           {"facts", std::move(facts)}})
                 << '\n';
  }
}
