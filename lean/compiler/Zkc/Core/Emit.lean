module

public import Zkc.Core.Region

public section

/-! Emitting operations into a region that a step rewrites.

A step that replaces one operation by several builds them in order and continues with
the rest of the old region in the context they leave. Three pieces of data describe
that, and none is a function over the body:

- `Extends Δ Δ'` says that `Δ'` is `Δ` with values bound later: a count and an erased
  fact. A reference and a `Mapping` into `Δ` become ones into `Δ'` by adding the count.
  Extensions compose by adding counts, so a sequence of emitted operations needs no
  equation between contexts.
- `Emitted dialect Δ results` is a short sequence of operations in the context `Δ`:
  the context it leaves, the extension, the operations as a function from the rest of
  the region, and the values it produced.
- `Renaming.toAll` binds the results of an old operation to values of the new context.
-/

set_option autoImplicit false

namespace Zkc.Source

/-- `Δ'` is `Δ` under `count` later bindings. -/
structure Extends {α : Type} (Δ Δ' : List α) where
  count : Nat
  shifts : ∀ index : Nat, Δ'[index + count]? = Δ[index]?
  counted : Δ'.length = Δ.length + count

namespace Extends

variable {α : Type} {Δ Δ' Δ'' : List α}

def refl (Δ : List α) : Extends Δ Δ := ⟨0, fun _ => rfl, rfl⟩

@[expose] def bindAll (Δ added : List α) : Extends Δ (Zkc.Source.bindAll Δ added) :=
  ⟨added.length, getElem?_bindAll_old added Δ, length_bindAll added Δ⟩

@[expose] def trans (first : Extends Δ Δ') (second : Extends Δ' Δ'') : Extends Δ Δ'' :=
  ⟨first.count + second.count,
    fun index => by rw [← Nat.add_assoc, second.shifts, first.shifts],
    by rw [second.counted, first.counted, Nat.add_assoc]⟩

end Extends

/-- A value of a context, in an extension of the context. -/
@[expose] def Var.extend {α : Type} {Δ Δ' : List α} {ty : α} (reference : Var Δ ty) (grows : Extends Δ Δ') :
    Var Δ' ty :=
  ⟨reference.index + grows.count, (grows.shifts reference.index).trans reference.valid⟩

theorem Var.extend_bindAll {α : Type} {Δ : List α} {ty : α} (reference : Var Δ ty)
    (added : List α) : reference.extend (Extends.bindAll Δ added) = reference.weaken added := rfl

theorem atLevel?_extends {β : Type} {Δ Δ' : List β} (grows : Extends Δ Δ') {depth level : Nat}
    {entry : β} (found : atLevel? Δ depth level = some entry) :
    atLevel? Δ' (depth + grows.count) level = some entry := by
  unfold atLevel? at found ⊢
  split at found
  · rename_i below
    have position : depth + grows.count - 1 - level = (depth - 1 - level) + grows.count := by omega
    have below' : level < depth + grows.count := by omega
    simp only [below', ↓reduceIte, position, grows.shifts]
    exact found
  · cases found

namespace Mapping

variable {α β : Type} {R : α → β → Prop} {Γ : List α} {Δ Δ' : List β}

/-- The same map into an extension of the new context. -/
def extend (map : Mapping R Γ Δ) (grows : Extends Δ Δ') : Mapping R Γ Δ' :=
  ⟨map.levels, map.depth + grows.count, by rw [map.counted, grows.counted],
    fun index source found => by
      obtain ⟨level, at_, image⟩ := map.sound index source found
      exact ⟨level, at_, fun target related => atLevel?_extends grows (image target related)⟩⟩

/-- The image under an extended map is the extended image. -/
theorem apply_extend (map : Mapping R Γ Δ) (grows : Extends Δ Δ') {source : α} {target : β}
    (reference : Var Γ source) (related : R source target) :
    (map.extend grows).apply reference related = (map.apply reference related).extend grows := by
  apply Var.ext
  have found := map.level_sound reference related
  unfold atLevel? at found
  split at found
  · rename_i below
    show map.depth + grows.count - 1 - map.level reference.index =
      map.depth - 1 - map.level reference.index + grows.count
    omega
  · cases found

end Mapping

namespace Renaming

variable {Ty : Type}

/-- The same renaming into an extension of the new context. -/
@[expose] def extend {Γ Δ Δ' : List Ty} (map : Renaming Γ Δ) (grows : Extends Δ Δ') : Renaming Γ Δ' :=
  Mapping.extend map grows

/-- The results of an old operation, renamed to given values of the new context. -/
def toAll : {Γ Δ : List Ty} → Renaming Γ Δ → {results : List Ty} → Operands Δ results →
    Renaming (bindAll Γ results) Δ
  | _, _, map, _, .nil => map
  | _, _, map, _, .cons image rest => toAll (map.to image) rest

/-- The renaming of the inputs of a closed region to themselves. -/
@[expose] def identity (inputs : List Ty) : Renaming (bindAll [] inputs) (bindAll [] inputs) :=
  Renaming.keepAll (Mapping.start (Δ := ([] : List Ty)) 0 rfl) inputs

end Renaming

namespace Operands

variable {Ty : Type}

/-- The values bound last, in binding order. -/
@[expose] def newest : (added : List Ty) → {Γ : List Ty} → Operands (bindAll Γ added) added
  | [], _ => .nil
  | ty :: rest, Γ => .cons ((Var.here : Var (ty :: Γ) ty).weaken rest) (newest rest)

/-- Operands in an extension of their context. -/
@[expose] def extend {Δ Δ' : List Ty} (grows : Extends Δ Δ') :
    {types : List Ty} → Operands Δ types → Operands Δ' types
  | _, .nil => .nil
  | _, .cons reference rest => .cons (reference.extend grows) (extend grows rest)

end Operands

namespace Regions

variable {dialect : Dialect}

/-- The first of several closed regions. -/
@[expose] def head {inputs outputs : List dialect.Ty} {rest : List (List dialect.Ty × List dialect.Ty)} :
    Regions dialect ((inputs, outputs) :: rest) → Region dialect (bindAll [] inputs) outputs
  | .cons body _ => body

/-- The later ones. -/
@[expose] def tail {inputs outputs : List dialect.Ty} {rest : List (List dialect.Ty × List dialect.Ty)} :
    Regions dialect ((inputs, outputs) :: rest) → Regions dialect rest
  | .cons _ tail => tail

end Regions

/-- A sequence of operations emitted in the context `Δ` that produces `results`: the
context it leaves, the extension from `Δ`, the operations before any rest of a region,
and the produced values. -/
structure Emitted (dialect : Dialect) (Δ : List dialect.Ty) (results : List dialect.Ty) where
  context : List dialect.Ty
  grows : Extends Δ context
  wrap : {out : List dialect.Ty} → Region dialect context out → Region dialect Δ out
  values : Operands context results

namespace Emitted

variable {dialect : Dialect} {Δ : List dialect.Ty}

/-- One operation; its results are the produced values. -/
@[expose] def operation (op : dialect.Op) (arguments : Operands Δ (dialect.arguments op))
    (bodies : Regions dialect (dialect.regions op)) : Emitted dialect Δ (dialect.results op) :=
  ⟨bindAll Δ (dialect.results op), .bindAll Δ _, fun next => .letOp op arguments bodies next,
    .newest _⟩

/-- A sequence, then a second one in the context the first leaves. The produced values
are given by the caller, in the context the second leaves. -/
@[expose] def andThen {first second results : List dialect.Ty} (before : Emitted dialect Δ first)
    (after : Emitted dialect before.context second)
    (values : Operands after.context results) : Emitted dialect Δ results :=
  ⟨after.context, before.grows.trans after.grows, fun next => before.wrap (after.wrap next), values⟩

end Emitted

end Zkc.Source
