#ifndef ZKC_CLAIMS_CLAIMS_H
#define ZKC_CLAIMS_CLAIMS_H

#include "zkc/Source/Model.h"
#include "llvm/Support/JSON.h"

namespace zkc::claims {
struct Kind {
  std::string name;
  source::Names types;
  std::string meaning;
};
struct Claim {
  std::string name, kind;
  source::Names values;
};
struct Terminal {
  std::string claim, guard;
};
struct Law {
  std::string name, premise;
};
struct Rule {
  std::string name, law, invocation, callee;
  source::Names inputs, outputs, guards, premises;
  std::string conclusion;
};
/// Caller authority, supplied independently of the candidate. A body digest
/// proves correspondence only; every Law is an explicit caller trust premise.
struct Contract {
  std::string sourceDigest, entry, validator;
  std::vector<Kind> kinds;
  std::vector<Claim> claims;
  source::Names required;
  std::vector<Terminal> terminals;
  std::vector<Law> laws;
  std::vector<Rule> rules;
};
struct Certificate {
  std::string sourceDigest, contractDigest;
  source::Names steps;
};
llvm::Expected<Contract> decodeContract(const llvm::json::Value &);
llvm::json::Value encode(const Contract &);
llvm::Expected<Certificate> decodeCertificate(const llvm::json::Value &);
llvm::json::Value encode(const Certificate &);

/// Admit the actual original source and report expanded invocation/value/guard
/// coordinates. Does not evaluate mathematical values or prove body laws.
llvm::Expected<llvm::json::Value> inspect(const source::Module &,
                                          llvm::StringRef entry);
llvm::Expected<Certificate> derive(const source::Module &, const Contract &);
llvm::Error check(const source::Module &, const Contract &,
                  const Certificate &);
} // namespace zkc::claims
#endif
