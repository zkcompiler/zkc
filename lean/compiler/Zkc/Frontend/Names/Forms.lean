module

public import Zkc.Frontend.Names.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Forms

What the lowering reads off the form of what it lowers, without resolving anything: the
operators, the folds and the reasons of the syntax as those of the lowered form; whether a name
of a loop's index stands in a static position of the body (TY10); the site name and the parts of
an event (EV3); and, on a lowered term, whether it is a size (TY2) or a static condition (TY9) by
its form.
-/

namespace Zkc.Frontend.Names

open Syntax

def operatorOfCompare : CompareOperator → Operator
  | .equal => .equal | .notEqual => .notEqual | .less => .less | .lessEqual => .lessEqual
  | .greater => .greater | .greaterEqual => .greaterEqual

def operatorOfSum : SumOperator → Operator
  | .add => .add | .subtract => .subtract | .concatenate => .concatenate

def operatorOfProduct : ProductOperator → Operator
  | .multiply => .multiply | .divide => .divide | .remainder => .remainder

def foldOf : BinderOperator → Fold
  | .sum => .sum | .product => .product | .all => .all | .any => .any

mutual
  /-- Whether a name stands in a static position of an expression: a size of a type, a static
  argument, a bound of a slice (TY10). -/
  partial def staticUseIn (name : String) (inStatic : Bool) : Syntax.Expr → Bool
    | .path _ path => inStatic && path.plainName?.any (·.text == name) || pathStaticUse name path
    | .call _ callee args => pathStaticUse name callee || callStaticUse name inStatic args
    | .slice _ target lower upper =>
      staticUseIn name inStatic target || (lower.any (staticUseIn name true)) ||
        (upper.any (staticUseIn name true))
    | .ifExpr _ a b c => staticUseIn name inStatic a || staticUseIn name inStatic b ||
        staticUseIn name inStatic c
    | .orExpr _ a b | .andExpr _ a b | .compare _ _ a b | .sum _ _ a b | .product _ _ a b
    | .power _ a b | .innerProduct _ _ a b | .index _ a b =>
      staticUseIn name inStatic a || staticUseIn name inStatic b
    | .notExpr _ a | .unary _ a | .paren _ a | .field _ a _ | .position _ a _ =>
      staticUseIn name inStatic a
    | .method _ target _ staticArgs args =>
      staticUseIn name inStatic target || staticArgsUse name staticArgs ||
        callStaticUse name inStatic args
    | .record _ type fields => pathStaticUse name type || fields.any fun
        | .fieldInit _ _ (some value) => staticUseIn name inStatic value
        | .fieldInit _ _ none => false
    | .tuple _ components => components.any fun (.component _ _ value) => staticUseIn name inStatic value
    | .list _ elements => elements.any (staticUseIn name inStatic)
    | .repetition _ element count => staticUseIn name inStatic element || staticUseIn name true count
    | .comprehension _ element _ (.domain _ start stop) filter =>
      staticUseIn name inStatic element || staticUseIn name inStatic start ||
        stop.any (staticUseIn name inStatic) || filter.any (staticUseIn name inStatic)
    | .recordUpdate _ value fields =>
      staticUseIn name inStatic value || fields.any fun (.fieldUpdate _ _ v) => staticUseIn name inStatic v
    | .binderForm _ _ _ _ (.domain _ start stop) body =>
      staticUseIn name inStatic start || stop.any (staticUseIn name inStatic) ||
        staticUseIn name inStatic body
    | .indexType _ size => staticUseIn name true size
    | .nonzeroType _ type => typeStaticUse name type
    | _ => false

  partial def pathStaticUse (name : String) : Path → Bool
    | .path _ segments => segments.any fun (.segment _ _ args) => staticArgsUse name args

  partial def staticArgsUse (name : String) : Option StaticArgs → Bool
    | some (.staticArgs _ args) => args.any fun
      | .term _ _ term | .spec _ _ term => staticUseIn name true term
      | .inferred .. => false
    | none => false

  partial def callStaticUse (name : String) (inStatic : Bool) : CallArgs → Bool
    | .callArgs _ arguments witnesses => (arguments ++ witnesses.getD #[]).any fun
      | .positional _ value | .named _ _ value | .spec _ _ value => staticUseIn name inStatic value

  partial def typeStaticUse (name : String) : TypeExpr → Bool
    | .index _ size => staticUseIn name true size
    | .nonzero _ type => typeStaticUse name type
    | .sequence _ element size => typeStaticUse name element || size.any (staticUseIn name true)
    | .tuple _ fields => fields.any fun (.tupleField _ _ type) => typeStaticUse name type
    | .path _ path => pathStaticUse name path
    | .bool _ | .nat _ | .rational _ => false

  partial def stmtStaticUse (name : String) : Syntax.Stmt → Bool
    | .binding _ _ type _ value | .mutDecl _ _ type _ value =>
      type.any (typeStaticUse name) || staticUseIn name false value
    | .update _ _ value | .guard _ _ value _ => staticUseIn name false value
    | .eventStmt (.bound _ _ _ type _ event) => type.any (typeStaticUse name) || eventStaticUse name event
    | .eventStmt (.application _ _ application) =>
      pathStaticUse name application.callee || callStaticUse name false application.args
    | .«open» _ _ claims => claims.any fun claim => staticUseIn name false claim.handle
    | .«if» _ condition thenSuite elseBranch =>
      staticUseIn name false condition || thenSuite.any (stmtStaticUse name) ||
        match elseBranch with
        | some (.suite _ statements) => statements.any (stmtStaticUse name)
        | some (.elseIf statement) => stmtStaticUse name statement
        | none => false
    | .«match» _ scrutinee cases =>
      staticUseIn name false scrutinee || cases.any fun (.«case» _ _ body) => body.any (stmtStaticUse name)
    | .«for» _ _ (.domain _ start stop) collected body =>
      staticUseIn name false start || stop.any (staticUseIn name false) ||
        body.any (stmtStaticUse name) || (collected.getD #[]).any (staticUseIn name false ·.value)
    | .empty _ => false

  partial def eventStaticUse (name : String) : Syntax.Event → Bool
    | .send _ payload _ _ oracle => staticUseIn name false payload || oracle.any (staticUseIn name true)
    | .draw _ type _ _ | .sample _ type => typeStaticUse name type
    | .query _ handle _ positions _ => staticUseIn name false handle || staticUseIn name false positions
    | .attempt _ => false
    | .application application =>
      pathStaticUse name application.callee || callStaticUse name false application.args
end

def reasonOf : Option Syntax.Reason → Zkc.Core.Reason
  | some (.abort _) => .abort
  | some (.refused _) => .refused
  | some (.exhausted _) => .exhausted
  | _ => .reject

/-- The site name of an event: its binder when it is one name, otherwise `#[site(…)]`. -/
def siteName (site : Option SiteAttr) (pattern : Option Pattern) : Option String :=
  match pattern, site with
  | some (.name name), _ => some name.text
  | _, some siteAttribute => some siteAttribute.name.text
  | _, _ => none

/-- The parts of an event (EV3): one per receiver of a send to several, otherwise one. -/
def eventParts : Syntax.Event → Array String
  | .send _ _ _ receivers _ => if receivers.size ≤ 1 then #["value"] else receivers.map (s!"to {·.text}")
  | _ => #["value"]

/-- Whether a lowered term is a size by its form (TY2): numerals and static naturals with
`+ - * / ^` and `log2( )`. A path is a static natural unless it names an alternative or a function
of the fixed table; a local name is one when its binder is in `statics`: a static name or the index
of a range typed per iteration. -/
partial def sizeForm (statics : Std.HashSet LocalId) : Lowered.Expr → Bool
  | .number .. => true
  | .operator _ .add #[a, b] | .operator _ .subtract #[a, b] | .operator _ .multiply #[a, b]
  | .operator _ .divide #[a, b] | .operator _ .power #[a, b] => sizeForm statics a && sizeForm statics b
  | .call _ (.reference _ segments) #[.positional _ argument] none =>
    segments.any (fun (.segment step _ _) => step == .sizeOperator) && sizeForm statics argument
  | .local _ binder => statics.contains binder
  | .reference (.reference _ segments) =>
    !segments.isEmpty && !segments.any fun (.segment step _ _) =>
      match step with
      | .alternative .. | .bareAlternative _ | .fixed _ | .«local» => true
      | _ => false
  | _ => false

/-- Whether a lowered condition is static by its form (TY9): comparisons of sizes, and the
literals of `bool`, under `not`, `and` and `or`. -/
partial def staticCondition (statics : Std.HashSet LocalId) : Lowered.Expr → Bool
  | .operator _ .not #[inner] => staticCondition statics inner
  | .conditional _ .and a b _ | .conditional _ .or a _ b =>
    staticCondition statics a && staticCondition statics b
  | .operator _ .equal #[a, b] | .operator _ .notEqual #[a, b] | .operator _ .less #[a, b]
  | .operator _ .lessEqual #[a, b] | .operator _ .greater #[a, b]
  | .operator _ .greaterEqual #[a, b] => sizeForm statics a && sizeForm statics b
  | .bool .. => true
  | _ => false

end Zkc.Frontend.Names
