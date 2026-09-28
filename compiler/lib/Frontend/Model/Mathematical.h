#ifndef ZKC_FRONTEND_MODEL_MATHEMATICAL_H
#define ZKC_FRONTEND_MODEL_MATHEMATICAL_H
#include "zkc/Mathematical/Placement.h"

namespace zkc::frontend::model {
struct MathematicalLocation {
  uint32_t step;
  std::optional<uint32_t> node;
  std::optional<source::Span> location;
  bool terminal = false;
};
/// Elaboration output, before canonical admission and role placement. These
/// locations explain the captured raw graph; they confer no semantic authority.
struct MathematicalInput {
  mathematical::raw::Subject source;
  mathematical::Installation installation;
  mathematical::PlacementNames names;
  std::vector<MathematicalLocation> locations;
};
} // namespace zkc::frontend::model
#endif
