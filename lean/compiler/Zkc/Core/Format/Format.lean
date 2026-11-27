module

public import Zkc.Core.Program.Vocabulary

@[expose] public section

/-!
Formats: how a value is written as bytes and read back, and the codecs of a model.
-/

namespace Zkc.Core

/-! ## Formats -/

/-- A format of a type: how a value is written as bytes and read back. -/
structure Format (A : Type) where
  write : A → List Nat
  read : List Nat → Option (A × List Nat)

/-- The laws of a canonical format on values satisfying `valid`:
1. every element written for a valid value is a byte (`< 256`);
2. what is written for a valid value reads back and leaves what follows;
3. every successful read produces a valid value whose written bytes are an exact prefix. -/
structure Format.Lawful {A : Type} (valid : A → Prop) (f : Format A) : Prop where
  bytes : ∀ a, valid a → ∀ b, b ∈ f.write a → b < 256
  reads : ∀ a rest, valid a → f.read (f.write a ++ rest) = some (a, rest)
  written : ∀ bytes a rest, f.read bytes = some (a, rest) → valid a ∧ bytes = f.write a ++ rest

/-- The formats of the nominal carriers of a model, with their laws on valid carrier values:
what a model gives for its values to be written and read. A model of mathematical objects need
not have them. -/
structure Codecs {V : Vocabulary} (M : Model V) where
  format : ∀ key, Format (M.Carrier key)
  lawful : ∀ key, (format key).Lawful (M.valid key)

end Zkc.Core
