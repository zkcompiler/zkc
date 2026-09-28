import Zkc.Source.Mathematical.Outlining

set_option autoImplicit false
namespace Examples.Mathematical.Outlining
open Zkc.Source.Mathematical.Outlining

abbrev queries : PIR.Signature := ⟨Unit, fun _ => Nat⟩

def outlined : PIR.Proc (signature queries queries) Nat :=
  .call (.introduced ()) fun pureResult =>
    .call (.original ()) fun serviceReply => .done (pureResult + serviceReply)

theorem fold_keeps_genuine_query :
    fold (I := queries) (P := queries) (fun _ => 6) outlined =
      .call () (fun serviceReply => .done (6 + serviceReply)) := rfl

def arbitrary : PIR.Handler (signature queries queries) Nat String
  | .introduced _, state => ⟨.returned 17, state + 1, ["introduced"]⟩
  | .original _, state => ⟨.returned 17, state + 1, ["original"]⟩

def genuine : PIR.Handler queries Nat String :=
  fun _ state => ⟨.returned 17, state + 1, ["original"]⟩

example : outlined.run arbitrary 0 = ⟨.returned 34, 2, ["introduced", "original"]⟩ := rfl
example : (fold (I := queries) (P := queries) (fun _ => 6) outlined).run genuine 0 = ⟨.returned 23, 1, ["original"]⟩ := rfl

/-- The raw local-call reply cannot replace the mathematical evaluator. -/
example : (outlined.run arbitrary 0).outcome ≠
    ((fold (I := queries) (P := queries) (fun _ => 6) outlined).run genuine 0).outcome := by decide

end Examples.Mathematical.Outlining
