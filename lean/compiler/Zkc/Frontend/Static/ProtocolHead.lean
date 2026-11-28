module

public import Zkc.Frontend.Static.Types

public section
namespace Zkc.Frontend.Static.ProtocolHead

/-- Closed fragments use the same evaluator, class checks and instance table as applications. -/
structure Evaluation where
  value : Env → Lowered.Expr → Option Class → CompileM StaticValue
  asType : Lowered.Expr → Option Lowered.TypeTerm
  interface : Env → Lowered.Reference → CompileM AppliedInterface
  arguments : DeclarationId → Array Lowered.StaticArgument → Syntax.Span →
    CompileM (Array (Lowered.Expr × Class))
  text : Env → Syntax.Span → CompileM String

/-- Missing parameters of this head's own scope correspond by position in the two heads. -/
structure Side where
  env : Env
  scope : Option ScopeId

private def Side.isVariable (side : Side) (ref : ParameterRef) : Bool :=
  side.scope == some ref.scope && !side.env.values.contains ref

private def Side.isOpen (side : Side) (expr : Lowered.Expr) : Bool :=
  side.scope.isSome && expr.references.any fun (.reference _ segments) =>
    segments.any fun
      | .segment (.parameter ref) _ _ => side.isVariable ref
      | _ => false

private inductive Constructor where
  | index | nonzero | sequence | tuple | interface (id : DeclarationId)
  deriving BEq, Inhabited

/-- Exact affine sizes, free binders, injective type constructors and closed leaves.
An unsupported open subterm carries the text needed to explain an incomplete comparison. -/
private inductive Form where
  | closed (value : StaticValue)
  | size (constant : Nat) (coefficients : Std.TreeMap Nat Nat)
  | parameter (index : Nat)
  | node (kind : Constructor) (children : Array Form)
  | operation (op : Operator) (left right : Form) (term : String)
  | unknown (term : String)
  deriving Inhabited

private partial def closedType : ClosedType → Form
  | .index n => .node .index #[.size n {}]
  | .nonzero t => .node .nonzero #[closedType t]
  | .seq t n => .node .sequence (#[closedType t] ++ n.toArray.map (.size · {}))
  | .tuple ts _ => .node .tuple (ts.map closedType)
  | t => .closed (.type t)

private def closed : StaticValue → Form
  | .type t => closedType t
  | .natural n => .size n {}
  | v => .closed v

/-- An independent mismatch decides a conjunction even when another component is still open. -/
private def both : Except String Bool → Except String Bool → Except String Bool
  | .ok false, _ | _, .ok false => .ok false
  | .ok true, r | r, .ok true => r
  | .error x, .error _ => .error x

private partial def equal (a b : Form) : Except String Bool := do
  match a, b with
  | .unknown term, _ | _, .unknown term => throw term
  | .operation op x y text, .operation op' u v _ =>
    if op == op' then
      if let .ok true := both (equal x u) (equal y v) then return true
    throw text
  | .operation _ _ _ text, _ | _, .operation _ _ _ text => throw text
  | .closed x, .closed y => return x == y
  | .size x xs, .size y ys => return x == y && xs == ys
  | .parameter i, .parameter j => return i == j
  | .node k xs, .node l ys =>
    unless k == l && xs.size == ys.size do return false
    return ← (xs.zip ys).foldl (init := .ok true) fun r (x, y) => both r (equal x y)
  | _, _ => return false

/-- Normalize affine arithmetic on naturals. Subtraction needs a nonnegative
result for every assignment of the free parameters (TY2). -/
private def arithmetic (op : Operator) (a b : Form)
    (place : Syntax.Span) (text : CompileM String) : CompileM Form := do
  -- Total operations also admit congruence. Partial size operations need their TY2 side conditions.
  let congruence := fun () => do
    if [.add, .multiply, .power].contains op then return Form.operation op a b (← text)
    return .unknown (← text)
  let .size x xs := a | return ← congruence ()
  let .size y ys := b | return ← congruence ()
  if op == .add then
    return .size (x + y) (ys.foldl (init := xs) fun m i n => m.insert i (m.getD i 0 + n))
  if op == .subtract && y ≤ x && ys.all (fun i n => n ≤ xs.getD i 0) then
    let difference := ys.foldl (init := xs) fun m i n =>
      let coefficient := m.getD i 0 - n
      if coefficient == 0 then m.erase i else m.insert i coefficient
    return .size (x - y) difference
  if op == .multiply && (xs.isEmpty || ys.isEmpty) then
    let (factor, coeffs) := if xs.isEmpty then (x, ys) else (y, xs)
    if factor == 0 then return .size 0 {}
    let scaled ← coeffs.foldlM (init := {}) fun (m : Std.TreeMap Nat Nat) i n => do
      return m.insert i (← staticProduct place text factor n)
    return .size (← staticProduct place text x y) scaled
  congruence ()

/-- Only closed fragments enter ordinary evaluation. In particular a wait there propagates
even if the opposite head, or a sibling of the fragment, contains a free parameter. -/
private partial def term (ev : Evaluation) (side : Side) (expr : Lowered.Expr)
    (cls : Option Class := none) : CompileM Form := withStaticEvaluation do
  unless side.isOpen expr do return closed (← ev.value side.env expr cls)
  let place := expr.span
  let text := ev.text side.env place
  spendStatic place text
  let unknown := fun () => do return Form.unknown (← text)
  if let .reference (.reference _ #[.segment (.parameter ref) none none]) := expr then
    if side.isVariable ref then
      let found ← parameterClass ref
      if cls.any (· != found) then
        refuse "GR5" place s!"the parameter `{← text}` has the wrong static class here"
      if found == .natural then return .size 0 ((∅ : Std.TreeMap Nat Nat).insert ref.index 1)
      return .parameter ref.index
  if cls != some .natural && cls != some .«module» then
    if let some t := ev.asType expr then
      let type (t : Lowered.TypeTerm) := term ev side (.type t) (some .type)
      match t with
      | .reference ref =>
        if expr matches .type _ then return ← term ev side (.reference ref) (some .type)
      | .sequence _ elem count =>
        let elem ← type elem
        let size ← count.mapM (term ev side · (some .natural))
        return .node .sequence (#[elem] ++ size.toArray)
      | .index _ n => return .node .index #[← term ev side n (some .natural)]
      | .tuple _ ts _ => return .node .tuple (← ts.mapM type)
      | .nonzero _ t => return .node .nonzero #[← type t]
      | _ => pure ()
  if cls.isNone || cls == some .natural then
    if let .operator _ op #[a, b] := expr then
      return ← arithmetic op (← term ev side a (some .natural))
        (← term ev side b (some .natural)) place text
  unknown ()

/-- The ordinary evaluator handles import specialization, inherited parameters and owner
reads for closed bounds. For open applications we handle a top-level interface with every
deployed argument explicit. The shared segment binder assigns named and positional arguments. -/
private def applied (ev : Evaluation) (side : Side) (ref : Lowered.Reference) : CompileM Form := do
  unless side.isOpen (.reference ref) do
    let (id, args) ← ev.interface side.env ref
    return .node (.interface id) (args.map closed)
  let .reference place segments := ref
  let unknown := fun () => do return Form.unknown (← ev.text side.env place)
  let some (.segment (.declaration id) (some args) none) := segments.back? | return ← unknown ()
  let program ← program
  -- A qualified or imported name may start with the declaration of its file module.
  unless segments.pop.all (fun
    | .segment (.declaration prefixId) none _ =>
      (program.declarations[prefixId]?).any (·.kind == .fileModule)
    | _ => false) do return ← unknown ()
  let decl ← declaration id
  let params := deployedParameters program decl
  unless decl.kind == .interface && (program.namespaces[decl.namespace]?).any (·.parent.isNone) &&
      params.all (fun (r, _) => some r.scope == decl.ownScope && !side.env.values.contains r) &&
      args.all (fun | .term .. => true | _ => false) do return ← unknown ()
  let args ← ev.arguments id args place
  return .node (.interface id) (← args.mapM fun (e, cls) => term ev side e (some cls))

/-- Remember the first unresolved open equality while still checking independent components.
Interrupts from the evaluation of closed fragments propagate directly. -/
abbrev CheckM := StateT (Option String) CompileM

def check (action : CheckM Unit) : CompileM Unit := do
  let (_, reason) ← action.run none
  if let some why := reason then throw (.waiting why)

def requireEqual (site : Syntax.Span) (label part : String)
    (comparison : CompileM (Except String Bool)) : CheckM Unit := do
  match ← comparison with
  | .ok true => pure ()
  | .ok false => refuse "SP8" site s!"{label}: the {part} differs"
  | .error text =>
    let reason := s!"{label}: equality of the open protocol head ({part}) at `{text}`"
    modify fun old => old.orElse fun _ => some reason

def sameTerm (ev : Evaluation) (left right : Side) (a b : Lowered.Expr) (cls : Option Class) :
    CompileM (Except String Bool) := do
  return equal (← term ev left a cls) (← term ev right b cls)

def sameSorts (ev : Evaluation) (left right : Side) (a b : Array Lowered.SortTerm) :
    CompileM (Except String Bool) := do
  unless a.size == b.size do return .ok false
  let mut result := Except.ok true
  for (x, y) in a.zip b do
    match x, y with
    | .nat _, .nat _ | .linear _, .linear _ => pure ()
    | .reference r, .reference s =>
      result := both result (equal (← applied ev left r) (← applied ev right s))
    | _, _ => return .ok false
  return result

end Zkc.Frontend.Static.ProtocolHead
