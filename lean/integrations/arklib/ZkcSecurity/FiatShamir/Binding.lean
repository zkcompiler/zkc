module

public import ZkcSecurity.FiatShamir.Interface
public import Zkc.Construction.Binding

@[expose] public section

/-! Binding codecs and the typed public-value binding event.

Exact statement determination (`Typed.Determined`) asks that the initial
transcript of a statement, followed by any events, identify the statement. It
quantifies over every statement the prover can output, malformed ones included
(for example a raw vector whose length is not `2 ^ count`), so a codec that
discharges it must be injective and prefix-free on the whole statement type,
not only on well-formed statements.

- The typed public-value binding event `Zkc.Construction.PublicBinding Scalar`
  is the application context with a row (`Zkc.Construction.Row`) of the
  statement's typed public values (`Zkc.Construction.PublicValue`): scalars,
  vectors whose length is part of the value, indices with their bounds, and
  counts. Equal events have equal rows by constructor injectivity. These are
  binding representations; validity and canonical order are established
  separately, which keeps malformed values representable.
- `BindingCodec Stmt E` is an injective, prefix-free encoding of statements
  as initial histories of events `E`; it discharges `Typed.Determined`
  (`BindingCodec.determined`).
- `BindingCodec.single` binds a statement as one typed public-value binding
  event, through any injective embedding of binding events into the transcript
  events; it is prefix-free because every statement's history has one event.
  `determined_single` is the resulting determination lemma: it needs only that
  the embedding and the statement's row are injective.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open Zkc.Construction (PublicValue Row PublicBinding)

/-- A binding codec: an encoding of every statement, malformed ones included,
as an initial transcript history, injective and prefix-free. -/
structure BindingCodec (Stmt E : Type) where
  encode : Stmt → List E
  injective : Function.Injective encode
  /-- No statement's history is a proper prefix of another's. -/
  prefixFree : ∀ statement other (rest : List E), encode statement ++ rest = encode other → rest = []

variable {Stmt E Scalar : Type}

/-- An injective, prefix-free codec determines the statement from its initial
history followed by any events. -/
theorem BindingCodec.determined (codec : BindingCodec Stmt E) : Typed.Determined codec.encode := by
  intro statement other rest otherRest same
  rcases List.append_eq_append_iff.mp same with ⟨middle, longer, -⟩ | ⟨middle, longer, -⟩
  · have empty := codec.prefixFree statement other middle longer.symm
    subst empty
    exact codec.injective (by simpa using longer.symm)
  · have empty := codec.prefixFree other statement middle longer.symm
    subst empty
    exact codec.injective (by simpa using longer)

/-- The codec that binds a statement as one typed public-value binding event of
the application context and the statement's canonical row. -/
def BindingCodec.single (bind : PublicBinding Scalar → E) (bindInjective : Function.Injective bind)
    (context : String) (row : Stmt → Row Scalar) (rowInjective : Function.Injective row) :
    BindingCodec Stmt E where
  encode statement := [bind ⟨context, row statement⟩]
  injective statement other same := by
    simp only [List.cons.injEq, and_true] at same
    exact rowInjective (congrArg PublicBinding.row (bindInjective same))
  prefixFree statement other rest same := by
    simpa using congrArg List.length same

/-- Exact statement determination from constructor injectivity: when binding
events embed injectively into the transcript events and a statement's canonical
row determines the statement, the one-event initial histories determine the
statement. -/
theorem determined_single (bind : PublicBinding Scalar → E)
    (bindInjective : Function.Injective bind) (context : String) (row : Stmt → Row Scalar)
    (rowInjective : Function.Injective row) :
    Typed.Determined fun statement : Stmt => [bind ⟨context, row statement⟩] :=
  (BindingCodec.single bind bindInjective context row rowInjective).determined

end ZkcSecurity.FiatShamir
