module

public import Std.Data.HashMap
public import Zkc.Frontend.Semantics.Program

@[expose] public section

set_option autoImplicit false

/-!
# Closed types and static values

A static value is a closed type, a number, or a module at its own arguments (SP7). In an
instance nothing is symbolic: every size is a number, an alias is its definition, and two types
are equal when they are the same value (TY3). A record or a variant type is the number of its
instance, so equality and hashing do not look inside declarations.
-/

namespace Zkc.Frontend

abbrev InstanceId := Nat

mutual
  /-- A closed type of source. -/
  inductive ClosedType where
    | bool
    | nat
    /-- In specification items only. -/
    | rational
    | index (bound : Nat)
    | nonzero (field : ClosedType)
    /-- `[T; n]` with a size, `[T]` without. -/
    | seq (element : ClosedType) (size : Option Nat)
    /-- The components and, for each, the name the type writes for it. -/
    | tuple (components : Array ClosedType) (names : Array (Option String))
    /-- A type of the vocabulary: its row and static arguments. Two declarations that bind one
    row declare one type. -/
    | nominal (row : String) (arguments : Array StaticValue)
    | record («instance» : InstanceId)
    | «variant» («instance» : InstanceId)
    /-- A `spec type`. -/
    | specification («instance» : InstanceId)
    /-- The fresh type that a type member of a module parameter is in the opaque typing
    (SP12): one per parameter, member and static arguments of the member. `module` is the module
    instance that the parameter stands for in the opaque typing, which names the parameter;
    `sorts` are those of the bound that the interface writes on the member, and take no part in
    equality. -/
    | «opaque» («module» : InstanceId) (member : String) (arguments : Array StaticValue)
        (sorts : Array String)

  inductive StaticValue where
    | type (type : ClosedType)
    | natural (value : Nat)
    /-- A module at its own arguments: the instance of its declaration. -/
    | «module» («instance» : InstanceId)
end

mutual
  partial def ClosedType.beq : ClosedType → ClosedType → Bool
    | .bool, .bool | .nat, .nat | .rational, .rational => true
    | .index a, .index b => a == b
    | .nonzero a, .nonzero b => ClosedType.beq a b
    | .seq a m, .seq b n => m == n && ClosedType.beq a b
    | .tuple a m, .tuple b n =>
        m == n && a.size == b.size && (a.zip b).all fun (x, y) => ClosedType.beq x y
    | .nominal r a, .nominal s b =>
        r == s && a.size == b.size && (a.zip b).all fun (x, y) => StaticValue.beq x y
    | .record a, .record b | .variant a, .variant b | .specification a, .specification b => a == b
    | .opaque p m a _, .opaque q n b _ =>
        p == q && m == n && a.size == b.size && (a.zip b).all fun (x, y) => StaticValue.beq x y
    | _, _ => false

  partial def StaticValue.beq : StaticValue → StaticValue → Bool
    | .type a, .type b => ClosedType.beq a b
    | .natural a, .natural b => a == b
    | .module a, .module b => a == b
    | _, _ => false
end

instance : BEq ClosedType := ⟨ClosedType.beq⟩
instance : BEq StaticValue := ⟨StaticValue.beq⟩

/-- The hash of a natural, over all of it. The hash that Lean gives a natural reads its low 64
bits only, so two sizes that agree modulo 2^64 would meet in every table keyed by a type or a
static value. -/
partial def naturalHash (value : Nat) : UInt64 :=
  if value < 18446744073709551616 then Hashable.hash value
  else mixHash (Hashable.hash (value % 18446744073709551616)) (naturalHash (value / 18446744073709551616))

mutual
  partial def ClosedType.hash : ClosedType → UInt64
    | .bool => 1
    | .nat => 2
    | .rational => 3
    | .index bound => mixHash 4 (naturalHash bound)
    | .nonzero field => mixHash 5 (ClosedType.hash field)
    | .seq element size =>
        mixHash 6 (mixHash (ClosedType.hash element) ((size.map naturalHash).getD 0))
    | .tuple components names =>
        components.foldl (init := mixHash 7 (Hashable.hash names)) fun hash component =>
          mixHash hash (ClosedType.hash component)
    | .nominal row arguments =>
        arguments.foldl (init := mixHash 8 (Hashable.hash row)) fun hash argument =>
          mixHash hash (StaticValue.hash argument)
    | .record «instance» => mixHash 9 (Hashable.hash «instance»)
    | .variant «instance» => mixHash 10 (Hashable.hash «instance»)
    | .specification «instance» => mixHash 11 (Hashable.hash «instance»)
    | .opaque «module» member arguments _ =>
        arguments.foldl
          (init := mixHash 12 (mixHash (Hashable.hash «module») (Hashable.hash member)))
          fun hash argument => mixHash hash (StaticValue.hash argument)

  partial def StaticValue.hash : StaticValue → UInt64
    | .type type => mixHash 13 (ClosedType.hash type)
    | .natural value => mixHash 14 (naturalHash value)
    | .module «instance» => mixHash 15 (Hashable.hash «instance»)
end

instance : Hashable ClosedType := ⟨ClosedType.hash⟩
instance : Hashable StaticValue := ⟨StaticValue.hash⟩

instance : Inhabited ClosedType := ⟨.bool⟩
instance : Inhabited StaticValue := ⟨.natural 0⟩

/-- The empty tuple. -/
def ClosedType.unit : ClosedType := .tuple #[] #[]

/-- The values of the static parameters in scope at a place of an instance. -/
abbrev StaticEnvironment := Std.HashMap ParameterRef StaticValue

end Zkc.Frontend
