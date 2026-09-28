import Zkc.Source.Mathematical.Raw

/-! An explicit injective binding from local role positions to module roles.
Availability sets are canonicalized by port admission; this object retains the
written positional binding, which may be non-monotone.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.RoleResolution

structure Binding where
  roles : List Nat
  injective : roles.Nodup

def Binding.participants (binding : Binding) : List Nat := binding.roles.mergeSort (· ≤ ·)

structure Use (binding : Binding) where
  source : Raw.Reference .role
  role : Nat
  selected : binding.roles[source.index]? = some role

def resolve (binding : Binding) (source : Raw.Reference .role) :
    StateT Nat (Except String) { result : Use binding // result.source = source } := do
  let cost := min (source.index + 1) (binding.roles.length + 1)
  let available ← get
  if cost > available then throw "role-resource"
  set (available - cost)
  match selected : binding.roles[source.index]? with
  | none => throw "role-scope"
  | some role => return ⟨⟨source, role, selected⟩, rfl⟩

/-- The module-role context is allocated only after charging its cardinality. -/
def initialChecked (count : Nat) : StateT Nat (Except String)
    { binding : Binding // binding.roles = List.range count } := do
  let remaining ← get
  if count > remaining then throw "role-resource"
  set (remaining - count)
  return ⟨⟨List.range count, List.nodup_range⟩, rfl⟩

def initial (count : Nat) : StateT Nat (Except String) Binding :=
  (initialChecked count).map Subtype.val

structure Selection (parent : Binding) (source : List (Raw.Reference .role)) where
  uses : List (Use parent)
  erasure : uses.map Use.source = source

def Selection.values {parent source} (selection : Selection parent source) : List Nat :=
  selection.uses.map Use.role

theorem Selection.lookups {parent source} (selection : Selection parent source) :
    selection.values.map some = source.map (fun reference => parent.roles[reference.index]?) := by
  conv => rhs; rw [← selection.erasure]
  simp only [Selection.values, List.map_map, List.map_inj_left]
  intro use _
  exact use.selected.symm

theorem Selection.values_unique {parent source} (first second : Selection parent source) :
    first.values = second.values :=
  (List.map_inj_right (fun _ _ same => Option.some.inj same)).mp (first.lookups.trans second.lookups.symm)

theorem Selection.length {parent source} (selection : Selection parent source) :
    selection.values.length = source.length := by
  have length := congrArg List.length selection.erasure
  simpa [Selection.values] using length

theorem Selection.member {parent source} (selection : Selection parent source)
    {role : Nat} (member : role ∈ selection.values) : role ∈ parent.roles := by
  obtain ⟨use, _, same⟩ := List.mem_map.mp member
  subst role
  exact List.mem_of_getElem? use.selected

theorem Selection.image {parent source} (selection : Selection parent source) (role : Nat) :
    role ∈ selection.values ↔ ∃ reference ∈ source, parent.roles[reference.index]? = some role := by
  constructor
  · intro member
    obtain ⟨use, included, same⟩ := List.mem_map.mp member
    subst role
    refine ⟨use.source, ?_, use.selected⟩
    rw [← selection.erasure]
    exact List.mem_map.mpr ⟨use, included, rfl⟩
  · rintro ⟨reference, member, lookup⟩
    rw [← selection.erasure] at member
    obtain ⟨use, included, same⟩ := List.mem_map.mp member
    subst reference
    have equal := Option.some.inj (use.selected.symm.trans lookup)
    exact List.mem_map.mpr ⟨use, included, equal⟩

def select (parent : Binding) : (source : List (Raw.Reference .role)) →
    StateT Nat (Except String) (Selection parent source)
  | [] => return ⟨[], rfl⟩
  | first :: rest => do
      let first ← resolve parent first
      let rest ← select parent rest
      return ⟨first.val :: rest.uses, by simp [first.property, rest.erasure]⟩

structure Composed (parent : Binding) (arity : Nat) (source : List (Raw.Reference .role)) where
  selection : Selection parent source
  length : selection.values.length = arity
  injective : selection.values.Nodup

def Composed.binding {parent arity source} (composed : Composed parent arity source) : Binding :=
  ⟨composed.selection.values, composed.injective⟩

/-- Positional bindings may be non-monotone. Their image is injective, and
cannot introduce a role absent from the caller's actual binding. -/
def compose (parent : Binding) (arity : Nat) (source : List (Raw.Reference .role)) :
    StateT Nat (Except String) (Composed parent arity source) := do
  let remaining ← get
  let cost := source.length * (source.length + 1)
  if cost > remaining then throw "role-resource"
  set (remaining - cost)
  if length : source.length = arity then
    let selection ← select parent source
    if injective : selection.values.Nodup then
      return ⟨selection, selection.length.trans length, injective⟩
    else throw "role-alias"
  else throw "role-arity"

theorem Composed.member {parent arity source} (composed : Composed parent arity source)
    {role : Nat} (member : role ∈ composed.binding.roles) : role ∈ parent.roles :=
  composed.selection.member member

end Zkc.Source.Mathematical.RoleResolution
