import Zkc.Source.RegionEncoding
import Zkc.Source.Format

/-! An independently selected region grammar. Its additional `bind` constructor
is not accepted as part of the existing `finite-source-1` format. -/

set_option autoImplicit false
namespace Zkc.Source.RegionFormat
open Lean Format
variable {Ty Op : Type}

def encode (types : Codec Ty) (operations : Codec Op) : RawRegion Ty Op → Json
  | .ret index => .arr #[.str "return", toJson index]
  | .stop reason => .arr #[.str "stop", stop.encode reason]
  | .letOp op arguments next =>
    .arr #[.str "apply", operations.encode op, toJson arguments, encode types operations next]
  | .branch condition yes no =>
    .arr #[.str "if", toJson condition, encode types operations yes, encode types operations no]
  | .iterate count acc initial body next =>
    .arr #[.str "repeat", toJson count, types.encode acc, toJson initial,
      encode types operations body, encode types operations next]
  | .bind result body next =>
    .arr #[.str "bind", types.encode result, encode types operations body, encode types operations next]

def decode (types : Codec Ty) (operations : Codec Op) :
    Nat → Json → Except Error (RawRegion Ty Op)
  | 0, _ => .error .depthLimit
  | depth + 1, json => do
    match ← array json with
    | [.str "return", index] => return .ret (← natural index)
    | [.str "stop", reason] => return .stop (← stop.decode reason)
    | [.str "apply", op, arguments, next] =>
      return .letOp (← operations.decode op) (← (← array arguments).mapM natural)
        (← decode types operations depth next)
    | [.str "if", condition, yes, no] =>
      return .branch (← natural condition) (← decode types operations depth yes)
        (← decode types operations depth no)
    | [.str "repeat", count, acc, initial, body, next] =>
      return .iterate (← natural count) (← types.decode acc) (← natural initial)
        (← decode types operations depth body) (← decode types operations depth next)
    | [.str "bind", result, body, next] =>
      return .bind (← types.decode result) (← decode types operations depth body)
        (← decode types operations depth next)
    | _ => .error .shape

end Zkc.Source.RegionFormat
