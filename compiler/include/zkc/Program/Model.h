#ifndef ZKC_PROGRAM_MODEL_H
#define ZKC_PROGRAM_MODEL_H

#include "zkc/Contracts/Binding.h"

#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace zkc::program {

using Names = std::vector<std::string>;

struct Parameter {
  std::string name;
  std::string type;
};

// Records alone do not establish binding or executable admission.
struct Operation {
  std::string callee;
  Names attributes;
  Names inputs;
  Names outputs;
};
struct LocalCall {
  std::string callee;
  Names inputs;
  Names outputs;
};
/// Internal role-free, acyclic local.apply before native helper expansion.
/// This record is never admitted by the participant-program codec.
struct LocalApply {
  std::string callee;
  Names inputs;
  Names outputs;
};
struct Send {
  std::string schema;
  std::string peer;
  std::string input;
};
struct Receive {
  std::string schema;
  std::string peer;
  std::string output;
  std::string type;
};
struct ServiceQuery {
  std::string port, method;
  Names inputs, outputs;
};
struct ServicePort {
  std::string name, contract;
  uint64_t inputIndex = 0;
};
struct BooleanConstant {
  std::string output;
  bool value = false;
};
struct Release {
  Names values;
};
struct Return {
  Names values;
};
struct ReturnIf {
  std::string condition;
  Names values, continuations;
};
struct Yield {
  Names values;
};
struct Stop {
  std::string reason;
};

struct Instruction;
using Body = std::vector<Instruction>;
struct LoopCount {
  std::string value;
  uint64_t maximum = 0;
  std::string induction = {};
};
struct Loop {
  LoopCount count;
  protocol::Assignments carried;
  Names captures;
  Body body;
  Names outputs;
};

/// Role-local structured control. Regions have explicit captures and yield
/// their ordered results; protocol interaction remains outside these regions.
struct Conditional {
  std::string condition;
  Names captures;
  Body thenBody, elseBody;
  Names outputs;
};
struct For {
  std::string induction, lower, upper;
  protocol::Assignments carried;
  Names captures;
  Body body;
  Names outputs;
  bool conditional = false;
};

struct VariantConstruct {
  std::string type, alternative;
  Names payload;
  std::string output;
};
struct MatchArm {
  std::string alternative;
  Names payload;
  Body body;
};
struct Match {
  std::string input;
  Names captures;
  std::vector<MatchArm> arms;
  Names outputs;
};

struct Instruction {
  using Value = std::variant<Operation, LocalCall, Send, Receive, Return, Yield,
                             Stop, Loop, Release, LocalApply, Conditional, For,
                             VariantConstruct, Match, ServiceQuery,
                             BooleanConstant, ReturnIf>;
  std::string site; // Empty for return/yield/release; scoped to its definition
                    // otherwise.
  Value value;

  template <typename T> const T *get() const { return std::get_if<T>(&value); }
  template <typename T> T *get() { return std::get_if<T>(&value); }
  llvm::StringRef kind() const;
  bool isTerminator() const;
};

struct LogicalOrigin {
  std::string definition;
  protocol::Assignments arguments;
};
struct Function {
  std::string name;
  std::vector<Parameter> arguments;
  Names results;
  Body body;
  std::optional<LogicalOrigin> origin; // Required callable provenance.
};
/// Reconstructed native local callable definitions. This is an internal
/// structural view of Protocol IR, never an authored source carrier.
struct LocalDefinitions {
  std::vector<protocol::OperationBinding> bindings;
  std::vector<Function> functions;
};

/// A projected participant with ordered local actions and service ports.
struct Participant {
  std::vector<ServicePort> services;
  std::string name;
  std::string instance;
  std::string role;
  std::vector<Parameter> arguments;
  Names results;
  Body body;
};
struct ParticipantEntry {
  std::string name;
  protocol::Assignments participants;
};
struct Participants {
  enum class Stage { Logical, Physical };
  Stage stage = Stage::Logical;
  std::vector<protocol::OperationBinding> bindings;
  std::vector<Function> functions;
  std::vector<Participant> participants;
  std::vector<ParticipantEntry> entries;
};

void walk(const Body &, llvm::function_ref<void(const Instruction &)>);
void walk(Body &, llvm::function_ref<void(Instruction &)>);

} // namespace zkc::program
#endif
