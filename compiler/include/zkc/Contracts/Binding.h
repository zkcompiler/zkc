#ifndef ZKC_CONTRACTS_BINDING_H
#define ZKC_CONTRACTS_BINDING_H

#include <string>
#include <utility>
#include <vector>

namespace zkc::protocol {
/// A closed application of an installed operation contract. Symbol names and
/// source locations belong to the declaration that contains this value.
struct BindingApplication {
  std::string contract;
  std::vector<std::string> arguments;
  std::string implementation;
};
using Assignments = std::vector<std::pair<std::string, std::string>>;

/// Named application of an installed contract, optionally physically selected.
struct OperationBinding {
  std::string name;
  BindingApplication application;
};
} // namespace zkc::protocol

#endif
