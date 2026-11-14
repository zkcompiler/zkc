module

public import Zkc.Frontend.Typed.Tree
public import Zkc.Frontend.Semantics.Rows

@[expose] public section

set_option autoImplicit false

/-!
# Whether code can stop

A role stops at a guard and nowhere else (GU1). So an expression can stop when it calls a
function that can, and a function can stop when its body has a guard or calls a function that
can (FN2). An operation of the core applied outside its domain does not stop: the admission of
the core refuses a program in which it could be.

This is a property of a subtree and of the functions it calls. It is computed where it is
asked for, from whether each callee can stop, and no table holds it.

Beside it stands the other reason why an expression is evaluated only where the source lets
it be: it applies an operation that has a domain. The right operand of `and` and of `or` that
can stop or applies such an operation is evaluated in a region of a local `if` on the left
operand; any other is an operand of the boolean operation of the core (§4.2). A choice between
the two forms is a function of the tree, so that every reader of the tree makes the same one.
-/

namespace Zkc.Frontend.Typed

mutual
  /-- Whether an expression can stop, given whether each function instance can. -/
  partial def Expr.canStop (callee : InstanceId → Bool) : Expr → Bool
    | .literal .. | .staticValue .. | .local .. => false
    | .apply _ applied arguments =>
      (match applied with
        | .instance inst => callee inst
        | _ => false) || arguments.any (Expr.canStop callee)
    | .construct _ _ parts => parts.any (Expr.canStop callee)
    | .project _ target _ _ => target.canStop callee
    | .convert _ _ value _ => value.canStop callee
    | .conditional _ _ condition onTrue onFalse =>
      condition.canStop callee || onTrue.canStop callee || onFalse.canStop callee
    | .block _ statements result => statements.any (Stmt.canStop callee) || result.canStop callee
    | .error _ evaluated => evaluated.any (Expr.canStop callee)

  /-- Whether a statement of local code can stop. -/
  partial def Stmt.canStop (callee : InstanceId → Bool) : Stmt → Bool
    | .guard .. => true
    | .bind _ _ value _ | .unpack _ _ value _ | .update _ _ value _ => value.canStop callee
    | .if _ condition onTrue onFalse _ =>
      condition.canStop callee || onTrue.any (Stmt.canStop callee) || onFalse.any (Stmt.canStop callee)
    | .match _ scrutinee _ _ cases _ =>
      scrutinee.canStop callee || cases.any fun (.case _ _ _ body) => body.any (Stmt.canStop callee)
    | .for _ (.loop _ domain _ body) _ =>
      (match domain with
        | .range start stop _ => start.canStop callee || stop.canStop callee
        | .collection source _ _ => source.canStop callee) ||
      (match body with
        | .uniform statements values =>
          statements.any (Stmt.canStop callee) || values.any (Expr.canStop callee)
        | .stepped iterations => iterations.any fun (.iteration _ statements values) =>
            statements.any (Stmt.canStop callee) || values.any (Expr.canStop callee)
        | .empty .. => false)
    | .scope _ body => body.any (Stmt.canStop callee)
    | .event .. | .error .. => false
end

/-- The request for a row of the tree: its name and its static arguments as a row reads them. -/
def RowRef.request (row : RowRef) : Typing.RowRequest :=
  { name := row.name
    statics := row.statics.filterMap fun
      | .type type => some (Typing.RowStatic.type type)
      | .natural value => some (.nat value)
      | .«module» _ => none }

/-- Whether a row asked for is restricted: it is applied on its domain. -/
def rowRestricted (request : Typing.RowRequest) : Bool :=
  match Typing.rowOf? request with
  | some row => (row.kind matches .restricted _)
  | none => false

/-- Whether a conversion applies an operation that has a domain: a refining operation, or the
read of each element of a collection. -/
partial def Conversion.hasDomain : Conversion → Bool
  | .sized | .bounded | .nonzero | .elements _ => true
  | .components inner => inner.any fun
    | some conversion => conversion.hasDomain
    | none => false
  | .andThen first _ second => first.hasDomain || second.hasDomain
  | _ => false

mutual
  /-- Whether an expression applies an operation that has a domain, in it or in a region of
  it: an operation of the core with a domain, a conversion that applies one, a restricted row.
  `bound` says whether a function instance is bound to a restricted row. A function with a
  body applies its operations on their domains, or stops. -/
  partial def Expr.hasDomain (bound : InstanceId → Bool) : Expr → Bool
    | .literal .. | .staticValue .. | .local .. => false
    | .apply _ applied arguments =>
      (match applied with
        | .operation operation => operation.hasDomain
        | .row row => rowRestricted row.request
        | .boundRow row => (row.kind matches .restricted _)
        | .instance inst => bound inst
        | _ => false) || arguments.any (Expr.hasDomain bound)
    | .construct _ _ parts => parts.any (Expr.hasDomain bound)
    | .project _ target _ _ => target.hasDomain bound
    | .convert _ conversion value _ => conversion.hasDomain || value.hasDomain bound
    | .conditional _ _ condition onTrue onFalse =>
      condition.hasDomain bound || onTrue.hasDomain bound || onFalse.hasDomain bound
    | .block _ statements result => statements.any (Stmt.hasDomain bound) || result.hasDomain bound
    | .error _ evaluated => evaluated.any (Expr.hasDomain bound)

  /-- Whether a statement of local code applies an operation that has a domain. A loop over a
  collection reads its elements, and a range with a run-time bound subtracts its bounds. -/
  partial def Stmt.hasDomain (bound : InstanceId → Bool) : Stmt → Bool
    | .guard _ condition _ _ => condition.hasDomain bound
    | .bind _ _ value _ | .unpack _ _ value _ | .update _ _ value _ => value.hasDomain bound
    | .if _ condition onTrue onFalse _ =>
      condition.hasDomain bound || onTrue.any (Stmt.hasDomain bound) ||
        onFalse.any (Stmt.hasDomain bound)
    | .match _ scrutinee _ _ cases _ =>
      scrutinee.hasDomain bound || cases.any fun (.case _ _ _ body) => body.any (Stmt.hasDomain bound)
    | .for _ (.loop _ domain _ body) _ =>
      (match domain with
        | .range _ _ (some _) => false
        | .range _ _ none | .collection .. => true) ||
      (match body with
        | .uniform statements values =>
          statements.any (Stmt.hasDomain bound) || values.any (Expr.hasDomain bound)
        | .stepped iterations => iterations.any fun (.iteration _ statements values) =>
            statements.any (Stmt.hasDomain bound) || values.any (Expr.hasDomain bound)
        | .empty .. => false)
    | .scope _ body => body.any (Stmt.hasDomain bound)
    | .event .. | .error .. => false
end

/-- What a reader of a body asks of the function instances that the body applies. -/
structure Callees where
  /-- Whether a function instance can stop (FN2). -/
  stops : InstanceId → Bool
  /-- Whether a function instance is bound to a restricted row. -/
  restricted : InstanceId → Bool

instance : Inhabited Callees := ⟨{ stops := fun _ => false, restricted := fun _ => false }⟩

/-- Whether the evaluation of an expression can fail to give a value: it can stop, or it applies
an operation that has a domain. -/
def Expr.canFail (callees : Callees) (expr : Expr) : Bool :=
  expr.canStop callees.stops || expr.hasDomain callees.restricted

/-! ## `and` and `or` (§4.2, TY9) -/

/-- `not x` at a node. -/
def negation (info : Info) (inner : Expr) : Expr :=
  .apply { info with type := .bool } (.operation .boolNot) #[inner]

/-- `a and b` (`conjunction`) or `a or b` at a node. -/
def logic (info : Info) (conjunction : Bool) (a b : Expr) : Expr :=
  let info := { info with type := ClosedType.bool }
  if conjunction then .conditional info .and a b (.literal info (.bool false))
  else .conditional info .or a (.literal info (.bool true)) b

/-- The operands of an expression that is a conjunction (`conjunction`) or a disjunction, a
negation moved inward: `not (x or y)` is the conjunction of `not x` and `not y`. With them, the
node of the `and` or the `or`. -/
def operands? (expr : Expr) (conjunction : Bool) : Option (Info × Expr × Expr) :=
  match expr, conjunction with
  | .conditional info .and x y _, true => some (info, x, y)
  | .conditional info .or x _ y, false => some (info, x, y)
  | .apply notInfo (.operation .boolNot) #[negated], _ =>
    match negated, conjunction with
    | .conditional info .or x _ y, true => some (info, negation notInfo x, negation notInfo y)
    | .conditional info .and x y _, false => some (info, negation notInfo x, negation notInfo y)
    | _, _ => none
  | _, _ => none

/-- Whether an `and` or an `or` is a local `if` on its left operand rather than the boolean
operation of the core: its right operand can fail, or its left operand is such an `and` (an
`or`), with which it is grouped to the right so that the right operand has the facts of
both. -/
partial def isChoice (callees : Callees) : Expr → Bool
  | .conditional _ .and a b _ =>
    b.canFail callees || ((operands? a true).any fun (inner, x, y) => isChoice callees (logic inner true x y))
  | .conditional _ .or a _ b =>
    b.canFail callees || ((operands? a false).any fun (inner, x, y) => isChoice callees (logic inner false x y))
  | _ => false

/-- Whether a condition has an `and` or an `or` that is a local `if`, under `and`, `or` and
`not`. -/
partial def hasChoice (callees : Callees) : Expr → Bool
  | expr@(.conditional _ .and a b _) | expr@(.conditional _ .or a _ b) =>
    isChoice callees expr || hasChoice callees a || hasChoice callees b
  | .apply _ (.operation .boolNot) #[inner] => hasChoice callees inner
  | _ => false

/-- How a condition with an `and` or an `or` that is a local `if` is taken one operand at a
time (TY9): a conjunction and a disjunction by their operands, a negation moved inward. -/
inductive Split where
  | conjunction (first second : Expr)
  | disjunction (first second : Expr)
  | condition (condition : Expr)

/-- The split of a condition, when it is one. -/
def split? : Expr → Option Split
  | .conditional _ .and a b _ => some (.conjunction a b)
  | .conditional _ .or a _ b => some (.disjunction a b)
  | .apply notInfo (.operation .boolNot) #[inner] =>
    match inner with
    | .conditional info .or a _ b => some (.condition (logic info true (negation notInfo a) (negation notInfo b)))
    | .conditional info .and a b _ => some (.condition (logic info false (negation notInfo a) (negation notInfo b)))
    | .apply _ (.operation .boolNot) #[x] => some (.condition x)
    | _ => none
  | _ => none

/-- Whether the body of a function can stop (FN2). -/
def FunctionBody.canStop (callee : InstanceId → Bool) (body : FunctionBody) : Bool :=
  body.statements.any (Stmt.canStop callee) || body.result.canStop callee

end Zkc.Frontend.Typed
