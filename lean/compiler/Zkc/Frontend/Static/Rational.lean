module

public import Zkc.Frontend.Static.Evaluate
public import Init.Data.Rat.Basic

@[expose] public section
namespace Zkc.Frontend.Static

/-- Close arithmetic in a rational context. Static references use the ordinary instance
environment. Powers share the resource limits on static integer powers. -/
partial def evalRational (env : Env) (expr : Lowered.Expr) : CompileM Rat := withStaticEvaluation do
  let subject := sourceText env expr.span
  spendStatic expr.span subject
  let binary (op : Rat → Rat → Rat) (a b : Lowered.Expr) := do
    let x ← evalRational env a
    let y ← evalRational env b
    spendStatic expr.span subject (sizeCost x.num.natAbs + sizeCost x.den + sizeCost y.num.natAbs + sizeCost y.den)
    return op x y
  match expr with
  | .operator _ .add #[a,b] => binary (· + ·) a b
  | .operator _ .subtract #[a,b] => binary (· - ·) a b
  | .operator _ .negate #[a] => return -(← evalRational env a)
  | .operator _ .multiply #[a,b] => binary (· * ·) a b
  | .operator _ .divide #[a,b] => binary (· / ·) a b
  | .operator sp .power #[base,exponent] =>
    let q ← evalRational env base
    let e ← evalRational env exponent
    unless e.den == 1 do refuse "TY8" exponent.span "the exponent of a rational must be an integer"
    let n := e.num.natAbs
    let num ← staticPower sp subject q.num.natAbs n
    let den ← staticPower sp subject q.den n (written := false)
    let signed : Int := if q.num < 0 && n % 2 == 1 then -(num : Int) else num
    let value := Rat.divInt signed den
    return if e.num < 0 then value.inv else value
  | .operator sp .remainder _ => refuse "TY8" sp "remainder is defined only on naturals"
  | _ => return (← evalSize env expr : Nat)

end Zkc.Frontend.Static
