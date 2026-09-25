import Tools.Interactive.Syntax

set_option autoImplicit false

namespace Tools.Interactive.Encode
open Lean (Json)

def pairs {α β : Type} (left : α → Json) (right : β → Json) (values : List (α × β)) : Json :=
  .arr (values.map fun (a, b) => .arr #[left a, right b]).toArray

end Tools.Interactive.Encode
