#ifndef ZKC_LANGUAGE_FORMALSOURCE_H
#define ZKC_LANGUAGE_FORMALSOURCE_H

#include "zkc/Syntax/Syntax.h"
#include "llvm/Support/Error.h"
#include <variant>

namespace zkc::language::detail {
struct Work;
/// An authored node reference, independent of any concrete parser's arena.
struct FormalNodeId {
  uint32_t index;
};
struct FormalReference {
  std::string name;
};
struct FormalLiteral {
  enum class Kind { Natural, Boolean, String } kind;
  std::string spelling;
};
struct FormalHole {};
struct FormalSequence {
  enum class Kind {
    Group,
    Tuple,
    Array,
    Block,
    Parameters,
    StaticParameters,
    Effects,
    Constraints,
    Result,
    Fields
  } kind;
  std::vector<FormalNodeId> elements;
};
struct FormalArgument {
  enum class Purpose {
    Ordinary,
    Statement,
    Witness,
    Parameter
  } purpose = Purpose::Ordinary;
  bool ghost = false;
  std::optional<FormalNodeId> label, type, value;
};
struct FormalApplication {
  enum class Kind { Call, Static, Index, Record, Delimited } kind;
  std::optional<FormalNodeId> function;
  std::vector<FormalNodeId> arguments;
  std::string notation;
};
struct FormalMember {
  FormalNodeId base, member;
  bool qualified = false;
};
struct FormalOperator {
  enum class Kind { Prefix, Postfix, Infix } kind;
  std::string symbol;
  std::vector<FormalNodeId> operands;
};
struct FormalRoles {
  // An ordinary role list and holder/receiver custody are distinct
  // constructors.
  std::optional<FormalNodeId> holder;
  std::vector<FormalNodeId> participants;
};
struct FormalAvailability {
  FormalNodeId value, roles;
};
struct FormalDeclaration {
  enum class Kind {
    Specification,
    Relation,
    GhostFunction,
    OracleFunction,
    Law
  } kind;
  bool isPublic = false;
  std::optional<FormalNodeId> name, parameters, inputs, roles, result,
      constraints, effects, body, subject;
};
struct FormalClause {
  enum class Kind {
    Requires,
    Ensures,
    Target,
    Reduces,
    Request,
    Alias,
    Law
  } kind;
  std::optional<FormalNodeId> label;
  FormalNodeId value;
  std::optional<FormalNodeId> residual;
};
struct FormalImport {
  bool isPublic = false, lean = false;
  FormalNodeId module;
  std::optional<FormalNodeId> alias;
  std::vector<FormalNodeId> members;
};
struct FormalBinding {
  FormalNodeId pattern, value;
  std::optional<FormalNodeId> type;
  bool mutableBinding = false, ordered = false, update = false;
};
struct FormalReturn {
  FormalNodeId value;
};
struct FormalGuard {
  FormalNodeId condition;
  std::optional<FormalNodeId> roles;
};
struct FormalIf {
  FormalNodeId condition, consequent;
  std::optional<FormalNodeId> alternative;
};
struct FormalMatch {
  FormalNodeId value, cases;
};
struct FormalCase {
  FormalNodeId pattern, body;
};
struct FormalFor {
  FormalNodeId index, lower, upper, body;
  std::optional<FormalNodeId> roles, maximum;
};
struct FormalSend {
  FormalNodeId value;
  std::optional<FormalNodeId> sender;
  std::vector<FormalNodeId> receivers;
};
struct FormalQuery {
  FormalNodeId handle, position;
};
struct FormalQuantifier {
  bool existential;
  FormalNodeId variable, type, body;
};
struct FormalLambda {
  std::vector<FormalNodeId> parameters;
  FormalNodeId body;
};
struct FormalReduction {
  std::string symbol;
  std::vector<std::pair<FormalNodeId, FormalNodeId>> bindings;
  std::optional<FormalNodeId> filter;
  FormalNodeId body;
};
struct FormalAttribute {
  FormalNodeId name;
  std::vector<FormalNodeId> arguments;
};
using FormalValue =
    std::variant<FormalReference, FormalLiteral, FormalHole, FormalSequence,
                 FormalArgument, FormalApplication, FormalMember,
                 FormalOperator, FormalRoles, FormalAvailability,
                 FormalDeclaration, FormalClause, FormalImport, FormalBinding,
                 FormalReturn, FormalGuard, FormalIf, FormalMatch, FormalCase,
                 FormalFor, FormalSend, FormalQuery, FormalQuantifier,
                 FormalLambda, FormalReduction, FormalAttribute>;
struct FormalNode {
  source::Span span;
  FormalValue value;
};
/// Frozen authored facts. Names are unresolved, omissions remain optional, and
/// no field asserts a type, property meaning, proof, or executable behavior.
struct FormalSource {
  FormalNodeId root;
  std::vector<FormalNode> nodes;
};
llvm::Expected<std::shared_ptr<const FormalSource>>
readFormalSource(const syntax::Snapshot &, syntax::NodeId, Work &);
} // namespace zkc::language::detail
#endif
