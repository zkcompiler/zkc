#ifndef ZKC_FRONTEND_MODEL_LIBRARIES_H
#define ZKC_FRONTEND_MODEL_LIBRARIES_H
#include "zkc/Frontend/Library.h"
namespace zkc::frontend::model {
/// Immutable checked judgments retained for inspection, including a prefix of
/// successful judgments when subsequent elaboration fails. No generated syntax
/// or emission state is retained here.
struct LibraryReport {
  struct Association {
    std::string name, kind, subject;
  };
  std::vector<Association> associations;
  std::vector<std::pair<std::string, library::Interface>> interfaces;
  std::vector<std::pair<std::string, library::CheckedBody>> clients;
  std::vector<std::pair<std::string, library::CheckedComponent>> components;
  std::vector<std::pair<std::string, library::CheckedBody>> componentBodies;
  std::vector<std::pair<std::string, library::LinkedProgram>> links;
};
} // namespace zkc::frontend::model
#endif
