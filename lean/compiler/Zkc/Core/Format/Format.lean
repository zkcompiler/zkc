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

/-- The two laws of a format: what is written reads back and leaves what follows; what
reads is what was written. -/
structure Format.Lawful {A : Type} (f : Format A) : Prop where
  reads : ∀ a rest, f.read (f.write a ++ rest) = some (a, rest)
  written : ∀ bytes a rest, f.read bytes = some (a, rest) → bytes = f.write a ++ rest

/-- The formats of the nominal carriers of a model, with their laws: what a model gives for
its values to be written and read. A model of mathematical objects need not have them. -/
structure Codecs {V : Vocabulary} (M : Model V) where
  format : ∀ key statics, Format (M.Carrier key statics)
  lawful : ∀ key statics, (format key statics).Lawful

end Zkc.Core
