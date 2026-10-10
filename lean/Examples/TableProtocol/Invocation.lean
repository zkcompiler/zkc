import Examples.TableProtocol.Format

/-! Bounded external inputs for execution of the checked table interpretation.
Values are ordered, named and decoded independently of native storage. -/

set_option autoImplicit false
namespace TableProtocol
open Lean Zkc.Source Zkc.Polynomial Zkc.Polynomial.Table

private def natural (json : Json) : Except String Nat :=
  (Format.natural json).mapError Format.Error.code
private def array (json : Json) : Except String (List Json) :=
  (Format.array json).mapError Format.Error.code

def scalar (d : Domain) (json : Json) : Except String (Field d) := do
  let n ← natural json
  match d with
  | .two => if n < 2 then return n else throw "noncanonical-scalar"
  | .seven => if n < 7 then return n else throw "noncanonical-scalar"

def scalars (d : Domain) (json : Json) : Except String (List (Field d)) := do
  (← array json).mapM (scalar d)

private def table (d : Domain) (n : Nat) (origin cells : Json) :
    Except String (Table (Field d) n) := do
  if n > 12 then throw "input-rank-limit"
  let origin ← natural origin
  let cells ← scalars d cells
  match admit n origin cells with
  | none => throw "invalid-table-shape"
  | some t => return t

def decodeValue : (ty : Ty) → Json → Except String (Value ty)
  | .boolean, json => json.getBool?.mapError (fun _ => "expected-boolean")
  | .digest, json => natural json
  | .scalar d, json => scalar d json
  | .point d, json => scalars d json
  | .table d n, json => do
    match ← array json with
    | [originJson, cells] => table d n originJson cells
    | _ => throw "invalid-table-shape"
  | .residual d n, json => do
    match ← array json with
    | [originJson, cells, coordinates] =>
      let t ← table d n originJson cells
      let coordinates ← scalars d coordinates
      if bound : coordinates.length ≤ n then return ⟨t, coordinates, bound⟩
      else throw "invalid-residual-shape"
    | _ => throw "invalid-residual-shape"
  | .summary, json => do
    match ← array json with
    | [a, b, n] => return (← scalar .two a, ← scalar .seven b, ← natural n)
    | _ => throw "invalid-summary"

def scalarJson : (d : Domain) → Field d → Json
  | .two, x => toJson x.val
  | .seven, x => toJson x.val
def valueJson : (ty : Ty) → Value ty → Json
  | .boolean, x => toJson x
  | .digest, n => toJson n
  | .scalar d, x => scalarJson d x
  | .point d, xs => .arr (xs.map (scalarJson d)).toArray
  | .table d _, t => .arr #[toJson t.origin, .arr (t.cells.map (scalarJson d)).toArray]
  | .residual d _, v =>
    .arr #[toJson v.root.origin, .arr (v.root.cells.map (scalarJson d)).toArray,
      .arr (v.coordinates.map (scalarJson d)).toArray]
  | .summary, (a,b,n) => .arr #[toJson a.val, toJson b.val, toJson n]

def suppliedInput (json : Json) : Except String (SuppliedInput Value) := do
  match ← array json with
  | [name, ty, value] =>
    let name ← name.getStr?.mapError (fun _ => "expected-string")
    let ty ← types.decode ty |>.mapError Format.Error.code
    return ⟨name, ty, ← decodeValue ty value⟩
  | _ => throw "invalid-input"

def decodeState (json : Json) : Except String Protocol.State := do
  match ← array json with
  | [two, seven, writes, sent, tape] =>
    let messages ← (← array sent).mapM fun pair => do
      match ← array pair with
      | [a,b] => return (← scalar .seven a, ← scalar .seven b)
      | _ => throw "invalid-message"
    return ⟨⟨← scalar .two two, ← scalar .seven seven, ← natural writes⟩,
      messages, ← scalars .seven tape⟩
  | _ => throw "invalid-state"

def stateJson (state : Protocol.State) : Json := .arr #[
  toJson state.base.two.val, toJson state.base.seven.val, toJson state.base.writes,
  .arr (state.sent.map (fun (a,b) => .arr #[toJson a.val, toJson b.val])).toArray,
  .arr (state.tape.map (fun x => toJson x.val)).toArray]

def traceJson : Protocol.Trace → Json
  | .base event => .arr #[.str "write", .str (domainName event.domain), toJson event.value]
  | .sent a b => .arr #[.str "sent", toJson a, toJson b]
  | .drawn r => .arr #[.str "drawn", toJson r]

end TableProtocol
