#ifndef ZKC_FRONTEND_MODEL_BODY_H
#define ZKC_FRONTEND_MODEL_BODY_H

#include "zkc/Frontend/Module.h"

namespace zkc::frontend::model {
/// Resolved calls retain declaration identity at the instruction itself.
/// Static arguments and local SSA operands follow the admitted operation
/// contract.
struct Call {
  enum class Kind { Operation, Algorithm, Local, Protocol };
  Kind kind;
  DeclId target;
  source::Names inputs, outputs, staticArguments, attributes;
  std::string role;
};

struct Instruction;
using Body = std::vector<Instruction>;
struct Loop {
  source::LoopCount count;
  source::Assignments carried;
  source::Names captures;
  Body body;
  source::Names outputs;
};
struct Conditional {
  std::string condition;
  source::Names captures;
  Body thenBody, elseBody;
  source::Names outputs;
};
struct For {
  std::string induction, lower, upper;
  source::Assignments carried;
  source::Names captures;
  Body body;
  source::Names outputs;
};
struct MatchArm {
  std::string alternative;
  source::Names payload;
  Body body;
};
struct Match {
  std::string input;
  source::Names captures;
  std::vector<MatchArm> arms;
  source::Names outputs;
};
struct Instruction : source::Node {
  using Value =
      std::variant<Call, source::Message, source::Return, source::Yield,
                   source::Stop, source::Release, source::VariantConstruct,
                   Loop, Conditional, For, Match>;
  std::string site;
  Value value;
};
} // namespace zkc::frontend::model
#endif
