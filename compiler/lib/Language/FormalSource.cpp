#include "FormalSource.h"
#include "State.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
class Reader {
  using K = syntax::Kind;
  using Id = syntax::NodeId;
  const syntax::Snapshot &tree;
  Work &work;
  FormalSource source;
  K kind(Id id) const { return tree.node(id).kind; }
  ArrayRef<Id> children(Id id) const { return tree.children(id); }
  Error fail(Id id, StringRef reason) const {
    return failure("source.formal-syntax", reason, tree.span(id));
  }
  StringRef head(Id id) const {
    for (auto token : tree.tokens().slice(tree.node(id).firstToken,
                                          tree.node(id).lastToken -
                                              tree.node(id).firstToken))
      if (!token.trivia() && !token.synthetic())
        return tree.text(token);
    return {};
  }
  StringRef between(Id left, Id right) const {
    for (unsigned i = tree.node(left).lastToken;
         i < tree.node(right).firstToken; ++i) {
      auto token = tree.tokens()[i];
      if (!token.trivia() && !token.synthetic())
        return tree.text(token);
    }
    return {};
  }
  Expected<std::string> spelling(Id id) {
    std::string result;
    const auto &node = tree.node(id);
    if (auto error =
            work.charge(node.lastToken - node.firstToken, tree.span(id)))
      return error;
    for (auto token :
         tree.tokens().slice(node.firstToken, node.lastToken - node.firstToken))
      if (!token.trivia() && !token.synthetic())
        result += tree.text(token).str();
    return result;
  }
  Expected<std::vector<FormalNodeId>> list(ArrayRef<Id> nodes) {
    std::vector<FormalNodeId> result;
    for (auto node : nodes) {
      auto projected1 = read(node);
      if (!projected1)
        return projected1.takeError();
      auto value = std::move(*projected1);
      result.push_back(value);
    }
    return result;
  }
  Expected<FormalValue> value(Id id) {
    auto nodes = children(id);
    auto arity = [&](size_t minimum, size_t maximum) -> Error {
      return nodes.size() >= minimum && nodes.size() <= maximum
                 ? Error::success()
                 : fail(id, "invalid authored formal node shape");
    };
    switch (kind(id)) {
    case K::Name: {
      auto projected2 = spelling(id);
      if (!projected2)
        return projected2.takeError();
      auto name = std::move(*projected2);
      return FormalReference{std::move(name)};
    }
    case K::Literal: {
      auto projected3 = spelling(id);
      if (!projected3)
        return projected3.takeError();
      auto literal = std::move(*projected3);
      auto category =
          literal == "true" || literal == "false" ? FormalLiteral::Kind::Boolean
          : StringRef(literal).starts_with('"') ? FormalLiteral::Kind::String
                                                : FormalLiteral::Kind::Natural;
      return FormalLiteral{category, std::move(literal)};
    }
    case K::Hole:
      return FormalHole{};
    case K::Group:
    case K::Tuple:
    case K::Array:
    case K::Suite:
    case K::Parameters:
    case K::StaticParameters:
    case K::Effects:
    case K::Where:
    case K::Result: {
      using S = FormalSequence::Kind;
      auto tag = kind(id) == K::Group              ? S::Group
                 : kind(id) == K::Array            ? S::Array
                 : kind(id) == K::Suite            ? S::Block
                 : kind(id) == K::Parameters       ? S::Parameters
                 : kind(id) == K::StaticParameters ? S::StaticParameters
                 : kind(id) == K::Effects          ? S::Effects
                 : kind(id) == K::Where            ? S::Constraints
                 : kind(id) == K::Result           ? S::Result
                                                   : S::Tuple;
      auto projected4 = list(nodes);
      if (!projected4)
        return projected4.takeError();
      auto elements = std::move(*projected4);
      return FormalSequence{tag, std::move(elements)};
    }
    case K::Argument:
    case K::Parameter: {
      if (auto error = arity(1, 3))
        return error;
      FormalArgument result;
      result.ghost = head(id) == "ghost";
      using P = FormalArgument::Purpose;
      result.purpose = head(id) == "statement"   ? P::Statement
                       : head(id) == "witness"   ? P::Witness
                       : head(id) == "parameter" ? P::Parameter
                                                 : P::Ordinary;
      if (nodes.size() == 1) {
        if (kind(id) == K::Parameter) {
          auto projected6 = read(nodes[0]);
          if (!projected6)
            return projected6.takeError();
          result.label = std::move(*projected6);
        } else {
          auto projected7 = read(nodes[0]);
          if (!projected7)
            return projected7.takeError();
          result.value = std::move(*projected7);
        }
      } else {
        auto projected8 = read(nodes[0]);
        if (!projected8)
          return projected8.takeError();
        result.label = std::move(*projected8);
        if (kind(id) == K::Parameter && between(nodes[0], nodes[1]) == ":") {
          auto projected9 = read(nodes[1]);
          if (!projected9)
            return projected9.takeError();
          result.type = std::move(*projected9);
          if (nodes.size() == 3) {
            auto projected10 = read(nodes[2]);
            if (!projected10)
              return projected10.takeError();
            result.value = std::move(*projected10);
          }
        } else {
          if (nodes.size() != 2)
            return fail(id, "argument has more than one value");
          auto projected11 = read(nodes[1]);
          if (!projected11)
            return projected11.takeError();
          result.value = std::move(*projected11);
        }
      }
      return result;
    }
    case K::Call:
    case K::StaticApply:
    case K::Index:
    case K::Record:
    case K::Delimited: {
      using A = FormalApplication::Kind;
      if (kind(id) == K::Call && nodes.size() == 1) {
        auto end = tree.node(id).lastToken;
        if (!end)
          return fail(id, "postfix operator has no spelling");
        std::string symbol;
        for (unsigned i = tree.node(nodes[0]).lastToken; i < end; ++i) {
          auto token = tree.tokens()[i];
          if (!token.synthetic() && !token.trivia())
            symbol += tree.text(token).str();
        }
        auto projected12 = list(nodes);
        if (!projected12)
          return projected12.takeError();
        auto operands = std::move(*projected12);
        return FormalOperator{FormalOperator::Kind::Postfix, std::move(symbol),
                              std::move(operands)};
      }
      FormalApplication result;
      result.kind = kind(id) == K::StaticApply ? A::Static
                    : kind(id) == K::Index     ? A::Index
                    : kind(id) == K::Record    ? A::Record
                    : kind(id) == K::Delimited ? A::Delimited
                                               : A::Call;
      if (kind(id) == K::Delimited) {
        result.notation = head(id).str();
        auto projected13 = list(nodes);
        if (!projected13)
          return projected13.takeError();
        result.arguments = std::move(*projected13);
      } else {
        if (auto error = arity(2, 2))
          return error;
        auto projected15 = read(nodes[0]);
        if (!projected15)
          return projected15.takeError();
        result.function = std::move(*projected15);
        auto projected16 = list(children(nodes[1]));
        if (!projected16)
          return projected16.takeError();
        result.arguments = std::move(*projected16);
      }
      return result;
    }
    case K::Projection: {
      if (auto error = arity(2, 2))
        return error;
      auto projected18 = read(nodes[0]);
      if (!projected18)
        return projected18.takeError();
      auto base = std::move(*projected18);
      auto projected19 = read(nodes[1]);
      if (!projected19)
        return projected19.takeError();
      auto member = std::move(*projected19);
      return FormalMember{base, member, between(nodes[0], nodes[1]) == "::"};
    }
    case K::Prefix:
    case K::Binary: {
      if (auto error = arity(kind(id) == K::Prefix ? 1 : 2,
                             kind(id) == K::Prefix ? 1 : 2))
        return error;
      auto symbol =
          kind(id) == K::Prefix ? head(id) : between(nodes[0], nodes[1]);
      auto projected21 = list(nodes);
      if (!projected21)
        return projected21.takeError();
      auto operands = std::move(*projected21);
      return FormalOperator{kind(id) == K::Prefix ? FormalOperator::Kind::Prefix
                                                  : FormalOperator::Kind::Infix,
                            symbol.str(), std::move(operands)};
    }
    case K::Roles: {
      FormalRoles result;
      auto names = nodes;
      if (names.size() == 1 && kind(names[0]) == K::Roles)
        names = children(names[0]);
      if (names.size() >= 2 && between(names[0], names[1]) == "->") {
        auto projected22 = read(names[0]);
        if (!projected22)
          return projected22.takeError();
        result.holder = std::move(*projected22);
        names = names.drop_front();
      }
      for (auto name : names) {
        if (kind(name) == K::Argument) {
          if (children(name).size() != 1)
            return fail(name, "role must be a bare name");
          name = children(name)[0];
        }
        auto projected23 = read(name);
        if (!projected23)
          return projected23.takeError();
        auto role = std::move(*projected23);
        result.participants.push_back(role);
      }
      return result;
    }
    case K::RoleType: {
      if (auto error = arity(2, 2))
        return error;
      auto projected25 = read(nodes[0]);
      if (!projected25)
        return projected25.takeError();
      auto term = std::move(*projected25);
      auto projected26 = read(nodes[1]);
      if (!projected26)
        return projected26.takeError();
      auto roles = std::move(*projected26);
      return FormalAvailability{term, roles};
    }
    case K::Spec:
    case K::Relation:
    case K::Definition:
    case K::OracleDefinition: {
      FormalDeclaration result;
      using D = FormalDeclaration::Kind;
      result.kind = kind(id) == K::Spec               ? D::Specification
                    : kind(id) == K::Relation         ? D::Relation
                    : kind(id) == K::OracleDefinition ? D::OracleFunction
                                                      : D::GhostFunction;
      result.isPublic = head(id) == "pub";
      bool named = kind(id) != K::Spec;
      if (kind(id) == K::Spec) {
        // Only header keywords are consulted; no parser kind is exported.
        const auto &node = tree.node(id);
        unsigned seen = 0;
        for (auto token : tree.tokens().slice(
                 node.firstToken, node.lastToken - node.firstToken)) {
          if (token.synthetic() || token.trivia())
            continue;
          if (seen++ == (result.isPublic ? 2u : 1u)) {
            named = tree.text(token) != "for";
            break;
          }
        }
      }
      unsigned at = 0;
      if (named) {
        if (auto error = arity(1, SIZE_MAX))
          return error;
        auto projected28 = read(nodes[at++]);
        if (!projected28)
          return projected28.takeError();
        result.name = std::move(*projected28);
      }
      for (; at < nodes.size(); ++at) {
        auto node = nodes[at];
        std::optional<FormalNodeId> *field = nullptr;
        switch (kind(node)) {
        case K::StaticParameters:
          field = &result.parameters;
          break;
        case K::Parameters:
          field = &result.inputs;
          break;
        case K::Roles:
          field = &result.roles;
          break;
        case K::Result:
          field = &result.result;
          break;
        case K::Where:
          field = &result.constraints;
          break;
        case K::Effects:
          field = &result.effects;
          break;
        case K::Suite:
          field = &result.body;
          break;
        default:
          if (kind(id) == K::Spec)
            field = &result.subject;
          else
            return fail(node, "unsupported formal declaration field");
        }
        if (*field)
          return fail(node, "duplicate formal declaration field");
        auto projected29 = read(node);
        if (!projected29)
          return projected29.takeError();
        *field = std::move(*projected29);
      }
      if (kind(id) == K::Spec && !result.subject)
        return fail(id, "specification has no subject");
      return result;
    }
    case K::Requires:
    case K::Ensures:
    case K::Target:
    case K::Reduces:
    case K::Request:
    case K::GoalAlias:
    case K::Law: {
      using C = FormalClause::Kind;
      FormalClause result;
      result.kind = kind(id) == K::Requires    ? C::Requires
                    : kind(id) == K::Ensures   ? C::Ensures
                    : kind(id) == K::Target    ? C::Target
                    : kind(id) == K::Reduces   ? C::Reduces
                    : kind(id) == K::Request   ? C::Request
                    : kind(id) == K::GoalAlias ? C::Alias
                                               : C::Law;
      unsigned operands = kind(id) == K::Reduces ? 2 : 1;
      if (auto error = arity(operands, operands + 1))
        return error;
      unsigned at = 0;
      if (nodes.size() > operands) {
        auto projected31 = read(nodes[at++]);
        if (!projected31)
          return projected31.takeError();
        result.label = std::move(*projected31);
      }
      auto projected32 = read(nodes[at++]);
      if (!projected32)
        return projected32.takeError();
      result.value = std::move(*projected32);
      if (at < nodes.size()) {
        auto projected33 = read(nodes[at]);
        if (!projected33)
          return projected33.takeError();
        result.residual = std::move(*projected33);
      }
      return result;
    }
    case K::Use: {
      if (auto error = arity(1, 3))
        return error;
      FormalImport result;
      result.isPublic = head(id) == "pub";
      // Native imports are projected by the ordinary import reader. This
      // constructor retains explicit Lean discovery requests only.
      result.lean = true;
      auto projected35 = read(nodes[0]);
      if (!projected35)
        return projected35.takeError();
      result.module = std::move(*projected35);
      for (auto child : nodes.drop_front()) {
        if (kind(child) == K::Parameters) {
          auto projected36 = list(children(child));
          if (!projected36)
            return projected36.takeError();
          result.members = std::move(*projected36);
        } else {
          auto projected37 = read(child);
          if (!projected37)
            return projected37.takeError();
          result.alias = std::move(*projected37);
        }
      }
      return result;
    }
    case K::Binding:
    case K::ActionBinding:
    case K::Update: {
      if (auto error = arity(2, 3))
        return error;
      auto projected39 = read(nodes[0]);
      if (!projected39)
        return projected39.takeError();
      auto pattern = std::move(*projected39);
      auto projected40 = read(nodes.back());
      if (!projected40)
        return projected40.takeError();
      auto term = std::move(*projected40);
      FormalBinding result{pattern,
                           term,
                           {},
                           head(id) == "mut",
                           kind(id) == K::ActionBinding,
                           kind(id) == K::Update};
      if (nodes.size() == 3) {
        auto projected41 = read(nodes[1]);
        if (!projected41)
          return projected41.takeError();
        result.type = std::move(*projected41);
      }
      return result;
    }
    case K::Return: {
      if (auto error = arity(1, 1))
        return error;
      auto projected43 = read(nodes[0]);
      if (!projected43)
        return projected43.takeError();
      auto term = std::move(*projected43);
      return FormalReturn{term};
    }
    case K::Guard: {
      if (auto error = arity(1, 2))
        return error;
      auto projected45 = read(nodes.back());
      if (!projected45)
        return projected45.takeError();
      auto term = std::move(*projected45);
      FormalGuard result{term, {}};
      if (nodes.size() == 2) {
        auto projected46 = read(nodes[0]);
        if (!projected46)
          return projected46.takeError();
        result.roles = std::move(*projected46);
      }
      return result;
    }
    case K::If: {
      if (auto error = arity(2, 3))
        return error;
      auto projected48 = read(nodes[0]);
      if (!projected48)
        return projected48.takeError();
      auto condition = std::move(*projected48);
      auto projected49 = read(nodes[1]);
      if (!projected49)
        return projected49.takeError();
      auto consequent = std::move(*projected49);
      FormalIf result{condition, consequent, {}};
      if (nodes.size() == 3) {
        auto projected50 = read(nodes[2]);
        if (!projected50)
          return projected50.takeError();
        result.alternative = std::move(*projected50);
      }
      return result;
    }
    case K::Match: {
      if (auto error = arity(2, 2))
        return error;
      auto projected52 = read(nodes[0]);
      if (!projected52)
        return projected52.takeError();
      auto term = std::move(*projected52);
      auto projected53 = read(nodes[1]);
      if (!projected53)
        return projected53.takeError();
      auto cases = std::move(*projected53);
      return FormalMatch{term, cases};
    }
    case K::Case: {
      if (auto error = arity(2, 2))
        return error;
      auto projected55 = read(nodes[0]);
      if (!projected55)
        return projected55.takeError();
      auto pattern = std::move(*projected55);
      auto projected56 = read(nodes[1]);
      if (!projected56)
        return projected56.takeError();
      auto body = std::move(*projected56);
      return FormalCase{pattern, body};
    }
    case K::For: {
      if (auto error = arity(4, 6))
        return error;
      auto projected58 = read(nodes[0]);
      if (!projected58)
        return projected58.takeError();
      auto index = std::move(*projected58);
      auto projected59 = read(nodes[1]);
      if (!projected59)
        return projected59.takeError();
      auto lower = std::move(*projected59);
      auto projected60 = read(nodes[2]);
      if (!projected60)
        return projected60.takeError();
      auto upper = std::move(*projected60);
      auto projected61 = read(nodes.back());
      if (!projected61)
        return projected61.takeError();
      auto body = std::move(*projected61);
      FormalFor result{index, lower, upper, body, {}, {}};
      for (auto child : nodes.drop_front(3).drop_back()) {
        if (kind(child) == K::Roles) {
          auto projected62 = read(child);
          if (!projected62)
            return projected62.takeError();
          result.roles = std::move(*projected62);
        } else {
          auto projected63 = read(child);
          if (!projected63)
            return projected63.takeError();
          result.maximum = std::move(*projected63);
        }
      }
      return result;
    }
    case K::Send: {
      if (auto error = arity(2, SIZE_MAX))
        return error;
      auto projected65 = read(nodes[0]);
      if (!projected65)
        return projected65.takeError();
      auto term = std::move(*projected65);
      FormalSend result{term, {}, {}};
      unsigned at = 1;
      if (between(nodes[0], nodes[1]) == "from") {
        auto projected66 = read(nodes[at++]);
        if (!projected66)
          return projected66.takeError();
        result.sender = std::move(*projected66);
      }
      auto projected67 = list(nodes.drop_front(at));
      if (!projected67)
        return projected67.takeError();
      result.receivers = std::move(*projected67);
      return result;
    }
    case K::Query: {
      if (auto error = arity(2, 2))
        return error;
      auto projected69 = read(nodes[0]);
      if (!projected69)
        return projected69.takeError();
      auto handle = std::move(*projected69);
      auto projected70 = read(nodes[1]);
      if (!projected70)
        return projected70.takeError();
      auto position = std::move(*projected70);
      return FormalQuery{handle, position};
    }
    case K::Quantifier: {
      if (auto error = arity(3, 3))
        return error;
      auto projected72 = read(nodes[0]);
      if (!projected72)
        return projected72.takeError();
      auto variable = std::move(*projected72);
      auto projected73 = read(nodes[1]);
      if (!projected73)
        return projected73.takeError();
      auto type = std::move(*projected73);
      auto projected74 = read(nodes[2]);
      if (!projected74)
        return projected74.takeError();
      auto body = std::move(*projected74);
      return FormalQuantifier{head(id) == "∃", variable, type, body};
    }
    case K::Lambda: {
      if (auto error = arity(2, SIZE_MAX))
        return error;
      auto projected76 = list(nodes.drop_back());
      if (!projected76)
        return projected76.takeError();
      auto parameters = std::move(*projected76);
      auto projected77 = read(nodes.back());
      if (!projected77)
        return projected77.takeError();
      auto body = std::move(*projected77);
      return FormalLambda{std::move(parameters), body};
    }
    case K::Reduction: {
      if (auto error = arity(3, SIZE_MAX))
        return error;
      auto projected79 = read(nodes.back());
      if (!projected79)
        return projected79.takeError();
      auto body = std::move(*projected79);
      FormalReduction result{head(id).str(), {}, {}, body};
      auto bindings = nodes.drop_back();
      if (bindings.size() % 2) {
        auto projected80 = read(bindings.back());
        if (!projected80)
          return projected80.takeError();
        result.filter = std::move(*projected80);
        bindings = bindings.drop_back();
      }
      for (unsigned i = 0; i < bindings.size(); i += 2) {
        auto projected81 = read(bindings[i]);
        if (!projected81)
          return projected81.takeError();
        auto pattern = std::move(*projected81);
        auto projected82 = read(bindings[i + 1]);
        if (!projected82)
          return projected82.takeError();
        auto domain = std::move(*projected82);
        result.bindings.emplace_back(pattern, domain);
      }
      return result;
    }
    case K::Attribute: {
      if (auto error = arity(1, 2))
        return error;
      auto projected84 = read(nodes[0]);
      if (!projected84)
        return projected84.takeError();
      auto name = std::move(*projected84);
      FormalAttribute result{name, {}};
      if (nodes.size() == 2) {
        auto projected85 = list(children(nodes[1]));
        if (!projected85)
          return projected85.takeError();
        result.arguments = std::move(*projected85);
      }
      return result;
    }
    default:
      return fail(id, "this formal form has no authored projection");
    }
  }
  Expected<FormalNodeId> read(Id id) {
    if (auto error = work.charge(1, tree.span(id)))
      return error;
    if (kind(id) == K::ExpressionStatement || kind(id) == K::Else) {
      if (children(id).size() != 1)
        return fail(id, "invalid formal wrapper");
      return read(children(id)[0]);
    }
    auto projected86 = value(id);
    if (!projected86)
      return projected86.takeError();
    auto projected = std::move(*projected86);
    FormalNodeId result{uint32_t(source.nodes.size())};
    source.nodes.push_back({tree.span(id), std::move(projected)});
    return result;
  }

public:
  Reader(const syntax::Snapshot &tree, Work &work) : tree(tree), work(work) {}
  Expected<std::shared_ptr<const FormalSource>> run(Id id) {
    auto projected87 = read(id);
    if (!projected87)
      return projected87.takeError();
    auto root = std::move(*projected87);
    source.root = root;
    return std::make_shared<const FormalSource>(std::move(source));
  }
};
} // namespace
Expected<std::shared_ptr<const FormalSource>>
readFormalSource(const syntax::Snapshot &tree, syntax::NodeId id, Work &work) {
  if ((tree.status() != syntax::Status::Complete &&
       tree.status() != syntax::Status::Partial) ||
      tree.headersOnly())
    return failure("source.formal-syntax",
                   "formal projection requires complete parsed source",
                   tree.span(id));
  return Reader(tree, work).run(id);
}
} // namespace zkc::language::detail
