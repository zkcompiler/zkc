import Zkc.Source.Mathematical.Raw

/-! Canonical opaque attributes at the semantic admission boundary.

Serialized readers already enforce unsigned UTF-8 key order. This check keeps
that requirement when a consumer constructs raw values directly, so operational
keys cannot distinguish different object orderings of one canonical encoding.
The caller charges the finite tree before checking it or invoking a registry.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.AttributeAdmission

def utf8Less (left right : String) : Bool :=
  decide (List.Lex (fun x y : UInt8 => x.toNat < y.toNat) left.toUTF8.toList right.toUTF8.toList)

mutual
  def canonical : Raw.Attribute → Bool
    | .boolean _ => true
    | .natural value => value < Static.limit
    | .string value => value.toUTF8.validateUTF8
    | .array values => canonicalValues values
    | .object fields => canonicalFields none fields
  def canonicalValues : List Raw.Attribute → Bool
    | [] => true
    | first :: rest => canonical first && canonicalValues rest
  def canonicalFields (previous : Option String) : List (String × Raw.Attribute) → Bool
    | [] => true
    | (key, value) :: rest =>
        key.toUTF8.validateUTF8 && (previous.all fun prior => utf8Less prior key) &&
          canonical value && canonicalFields (some key) rest
end

/-- Charge tree nodes, scalar bytes and key comparisons before registry code
sees the attribute. The depth bound protects direct raw callers; serialized
subjects have the stricter enclosing codec depth bound already. -/
def charge {E : Type} (resource : E) : Nat → Raw.Attribute → StateT Nat (Except E) Unit
  | 0, _ => throw resource
  | fuel + 1, value => do
      let remaining ← get
      if remaining = 0 then throw resource
      set (remaining - 1)
      match value with
      | .boolean _ => pure ()
      | .natural number =>
          -- Count the integer representation before asking for decimal text.
          let cost := number.log2 / 8 + 1
          let remaining ← get
          if cost > remaining then throw resource
          set (remaining - cost)
      | .string text =>
          let remaining ← get
          if text.utf8ByteSize > remaining then throw resource
          set (remaining - text.utf8ByteSize)
      | .array values =>
          for value in values do charge resource fuel value
      | .object fields =>
          for (key, value) in fields do
            let remaining ← get
            -- Each key participates in at most two adjacent comparisons,
            -- and UTF-8 validation traverses it once more.
            let cost := 1 + 3 * key.utf8ByteSize
            if cost > remaining then throw resource
            set (remaining - cost)
            charge resource fuel value

end Zkc.Source.Mathematical.AttributeAdmission
