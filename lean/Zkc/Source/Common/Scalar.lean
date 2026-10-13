module

public import Zkc.Source.Common.Vocabulary
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Field.Basic

@[expose] public section

/-! An explicitly selected scalar/module interpretation of the nominal source.

Every field tag is interpreted in F and every group tag in G. Concrete clients
must fix their domain assignment: this parameterization does not assert that
different native domains are isomorphic or that their implementations conform.
Services contain concrete handles and have no built-in random semantics.
-/

set_option autoImplicit false

namespace Zkc.Source.Common.Native

abbrev ScalarValue (F G : Type) : Ty → Type
  | .boolean => Bool
  | .field _ => F
  | .group _ => G
  | .service _ => Nat

abbrev scalarMeaning (F G : Type) [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] : Mathematical.Meaning language where
  Value := ScalarValue F G
  operation
    | .fieldConstant _ n, .nil => n
    | .fieldAdd _, .cons a (.cons b .nil) => a + b
    | .fieldSubtract _, .cons a (.cons b .nil) => a - b
    | .fieldMultiply _, .cons a (.cons b .nil) => a * b
    | .fieldEqual _, .cons a (.cons b .nil) => decide (a = b)
    | .groupIdentity _, .nil => 0
    | .groupAdd _, .cons a (.cons b .nil) => a + b
    | .groupScale _ _, .cons g (.cons f .nil) => f • g
    | .groupEqual _, .cons a (.cons b .nil) => decide (a = b)
    | .booleanConstant b, .nil => b
    | .booleanAnd, .cons a (.cons b .nil) => a && b
    | .booleanOr, .cons a (.cons b .nil) => a || b
    | .booleanXor, .cons a (.cons b .nil) => xor a b
    | .booleanEqual, .cons a (.cons b .nil) => a == b
    | .booleanNotEqual, .cons a (.cons b .nil) => a != b
    | .select _, .cons c (.cons a (.cons b .nil)) => if c then a else b

end Zkc.Source.Common.Native
