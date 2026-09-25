# Named inputs and role stores

This profile binds ordered string-named declarations to their actual supplied
values and defines the corresponding role-local reads.

## Declarations and supplied values

Fix source sorts `Ty` with decidable equality and a value interpretation
`V : Ty → Type`. The selected named binder uses strings for names and roles.
Its records are:

```text
Access = shared | privateTo(role)
Kind   = argument | capture

Declaration = (name : String, type : Ty, access : Access, kind : Kind)
Supplied    = (name : String, type : Ty, value : V type)
```

For an ordered declaration list `D`, let `types D` be the list of its sorts in
the same order. Successful binding returns `Values V (types D)`, which supplies
the [program environment](../../language/programs.md#contexts-and-values).

The consumer fixes `D` independently of the supplier. A supplied record contains
its actual name, sort and value; it cannot redefine the expected access or kind.
Different declarations have different names. Equal values and repeated uses of
a bound variable are allowed; duplicate declaration names are not.

## Exact ordered binding

For actor `ρ`, declarations `D` and supplied records `xs`, the binder
`bindInputs ρ D xs` returns either an input error or the heterogeneous values.
Success requires all of the following:

1. Declaration names are pairwise distinct.
2. `D` and `xs` have equal lengths.
3. Each corresponding pair has the same name and source sort.
4. Every declaration is shared or private to `ρ`.

The returned value at each position is the actual value from that supplied
position. Equality of sorts permits dependent transport to the expected value
type; it performs no conversion between distinct interpreted fields or other
sorts. Neither a name lookup that reorders records nor a same-sort substitution
of another value satisfies this binding rule.

Let `suppliedFromValues D values` pair each declaration's name and sort with
the corresponding returned value. Successful binding satisfies:

```text
bindInputs ρ D xs = ok values
  ⇒ suppliedFromValues D values = xs.
```

This is equality of the complete supplied list, including actual values, order
and multiplicity. An empty declaration list binds exactly an empty supplied
list. A capture unused by the body is still required by `D`.

The selected binder first scans for duplicate declaration names. It then
processes corresponding record pairs from the head: it checks role access,
then name, then sort, and binds the remaining pairs before constructing the
returned value list. Empty/nonempty list mismatches produce missing or extra
input errors. In the duplicate scan, the first declaration whose name appears
again in the remaining list is the reported duplicate.

Its error cases are:

| Error | Meaning |
|---|---|
| `duplicateDeclaration(name)` | A declaration name is repeated |
| `wrongRole(name)` | The declaration belongs to another role |
| `missingInput(name)` | A required declaration has no supplied record |
| `unexpectedInput(name)` | A supplied record remains after all declarations |
| `wrongName(expected, actual)` | Corresponding names differ |
| `wrongType(name)` | The supplied sort differs from the declared sort |

These are logical input errors before a body is executed. They are distinct
from a runtime [stopped execution](../../core/execution.md#outcomes). An external
format determines their concrete encoding and any boundary conversion.

Access labels alone do not authenticate the supplier, physical principal,
buffer ownership or contents of external storage. An adapter using those facts
MUST establish their connection to the actual supplied values.

The record reifier is mathematical. It does not define public disclosure or a
wire encoding.

## Typed role stores

For the named binder, a store maps a name and requested sort to an optional
value of that sort:

```text
Store V = (name : String) → (τ : Ty) → Option (V τ)
World   = (shared : Store V,
           privateInputs : String → Store V,
           hidden : H)
```

The parameter `H` is the hidden component type. It is separate from the shared
and per-role stores. For actor `ρ`, declaration `d` and world `w`, reading is:

```text
read ρ d w =
  if d.access = shared then require d.name (w.shared d.name d.type)
  else if d.access = privateTo ρ then
    require d.name (w.privateInputs ρ d.name d.type)
  else error (wrongRole d.name)

require name (some value) = ok value
require name none         = error (missingInput name)
```

Here `require` is the local store read's error operation, parameterized by
`d.name`. It does not create a runtime call or a stopped execution. A missing
value remains absent; it cannot become a present zero. A store is indexed by
both name and sort, so absence at one sort is not repaired by a value at another.

`collect ρ D w` reads declarations in order and constructs a supplied record for
each successful read, retaining that declaration's name, sort and actual value.
It stops at the first read error. Local binding is:

```text
bindLocal ρ D w =
  let xs ← collect ρ D w
  bindInputs ρ D xs
```

Collection precedes named binding. Therefore an unavailable or forbidden read
can fail before the duplicate-name check is reached. The two stages have the
same exact-value obligation on success; they need not report the same first
error for every malformed input situation.

The homogeneous expression frontend has a separately specified
[positional reader](expressions.md#positional-inputs). Its positions and optional
absence result are that profile's interpretation of inputs.

## Equal permitted views

For the typed world, define:

```text
SameView ρ w v ⇔
  w.shared = v.shared ∧
  w.privateInputs ρ = v.privateInputs ρ.
```

Store equality is pointwise equality at every name and sort, including whether
a value is present. The definition does not equate the hidden components or
another actor's private store.

For fixed actor and declarations, equal permitted views give equal read,
collection and binding results, including input errors. Define a local run by:

```text
runLocal M h ρ D p w s =
  let values ← bindLocal ρ D w
  ok (run h (⟦p⟧M (get values)) s)
```

Here `p : Program L (types D) τ`, `M` is its interpretation with `M.Value = V`,
`h` is its handler, and `s` its initial runtime state. The result is an input error or a complete
execution. For these same operands on both sides:

```text
SameView ρ w v ⇒
  runLocal M h ρ D p w s = runLocal M h ρ D p v s.
```

This law varies the input world while fixing the source, interpretation,
handler and initial runtime state. If a handler or initial state also changes
with hidden information, the corresponding execution claim needs its own
[handler and state relation](../../core/observations.md#handler-replacement).
