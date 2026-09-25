#ifndef ZKC_CONTRACTS_BINDING_H
#define ZKC_CONTRACTS_BINDING_H

#include <string>
#include <vector>

namespace zkc::protocol {
/// A closed application of an installed operation contract. Symbol names and
/// source locations belong to the declaration that contains this value.
struct BindingApplication {
  std::string contract;
  std::vector<std::string> arguments;
  std::string implementation;
};
} // namespace zkc::protocol

#endif
