module

public import Zkc.Frontend.Syntax.Tree

@[expose] public section

set_option autoImplicit false

/-!
# The span of every node

A constructor that only chooses between other productions has the span of the node it holds.
-/

namespace Zkc.Frontend.Syntax

def Path.span : Path → Span
  | .path span _ => span

/-- The name of a path of one segment without static arguments. -/
def Path.plainName? : Path → Option Name
  | .path _ #[.segment _ name none] => some name
  | _ => none

def Expr.span : Expr → Span
  | .ifExpr span .. | .orExpr span .. | .andExpr span .. | .notExpr span .. | .compare span ..
  | .sum span .. | .product span .. | .unary span .. | .power span .. | .field span ..
  | .method span .. | .position span .. | .index span .. | .slice span .. | .trueLiteral span
  | .falseLiteral span | .path span .. | .call span .. | .record span .. | .unit span
  | .paren span .. | .tuple span .. | .list span .. | .repetition span .. | .comprehension span ..
  | .recordUpdate span .. | .binderForm span .. | .innerProduct span .. | .boolType span
  | .natType span | .rationalType span | .indexType span .. | .nonzeroType span .. => span
  | .number value => value.span
  | .byteString value => value.span

def TypeExpr.span : TypeExpr → Span
  | .bool span | .nat span | .rational span | .index span _ | .nonzero span _
  | .sequence span .. | .tuple span _ | .path span _ => span

def Pattern.span : Pattern → Span
  | .name value => value.span
  | .wildcard span | .tuple span _ | .record span .. => span

def Holders.span : Holders → Span
  | .role value => value.span
  | .roles span _ => span

def EventStmt.span : EventStmt → Span
  | .bound span .. | .application span .. => span

def Stmt.span : Stmt → Span
  | .binding span .. | .mutDecl span .. | .update span .. | .«open» span .. | .guard span ..
  | .«if» span .. | .«match» span .. | .«for» span .. | .empty span => span
  | .eventStmt value => value.span

def Case.span : Case → Span
  | .«case» span .. => span

def TypeDecl.span : TypeDecl → Span
  | .type span .. | .specType span .. => span

def Member.span : Member → Span
  | .typeMember span .. | .natMember span .. | .moduleMember span .. | .defMember span .. => span
  | .protocolMember value => value.span
  | .lawMember value => value.span

def Clause.span : Clause → Span
  | .requires span .. | .ensures span .. | .invariant span .. | .reduces span .. | .proves span ..
  | .through span .. | .knowledge span .. | .zeroKnowledge span .. | .charge span .. => span

def SchemeLine.span : SchemeLine → Span
  | .construction span _ | .prover span _ | .offline span _ | .ideal span _ | .context span ..
  | .commit span .. | .pin span .. | .grind span .. | .retry span .. | .samples span _
  | .layout span .. => span

def Adjust.span : Adjust → Span
  | .carry span _ | .recover span .. => span

def Section.span : Section → Span
  | .«section» span .. => span

def Module.span : Module → Span
  | .«module» span .. => span

def Item.span : Item → Span
  | .use value => value.span
  | .«section» value => value.span
  | .«module» value => value.span
  | .interface value => value.span
  | .typeDecl value => value.span
  | .struct value => value.span
  | .enum value => value.span
  | .«def» value => value.span
  | .oracleDef value => value.span
  | .protocol value => value.span
  | .relation value => value.span
  | .contract value => value.span
  | .scheme value => value.span
  | .goal value => value.span
  | .law value => value.span
  | .staticName value => value.span

def ModuleItem.span : ModuleItem → Span
  | .item value => value.span
  | .moduleMember value => value.span
  | .memberDef value => value.span

end Zkc.Frontend.Syntax
