module

public import Zkc.Frontend.Syntax.Printer
public import Zkc.Frontend.Semantics.Static

@[expose] public section

set_option autoImplicit false

/-!
# Messages

A message is kept as its parts until it is shown: the words of the rule, and between them the
pieces of the program it is about (source text, a closed type, a static value, an instance, a
number, a name, roles). A part that names something of the program is rendered when the message
is, by a renderer that knows the names: the name a program gives a row of the vocabulary, the
way source writes an instance. So a message can be built before those names exist, compared and
filtered by what it is about, and shown differently by different tools.

A part that stands for a piece of the program is shown between backquotes. Inside `code`, which
is a piece of source that the message composes (`guard length(xs) == 8`), the parts are shown
bare and the whole is quoted once.
-/

namespace Zkc.Frontend

open Syntax

mutual
  /-- One part of a message. -/
  inductive MessagePart where
    /-- Words of the message. -/
    | text (text : String)
    /-- Source text as it was written. -/
    | source (text : String)
    /-- An expression of the tree, printed as source writes it. -/
    | expr (expr : Expr)
    /-- A type as written. -/
    | typeExpr (type : TypeExpr)
    | type (type : ClosedType)
    | value (value : StaticValue)
    /-- A number of the message: a bound, a size, a count. It is shown bare. -/
    | number (value : Nat)
    /-- A local or declared name. -/
    | name (name : String)
    | «instance» (id : InstanceId)
    /-- A declaration at values, for an instance that has no number yet. -/
    | instantiation (declaration : DeclarationId) (arguments : Array StaticValue)
    | declaration (id : DeclarationId)
    /-- Roles of a roster, by name, shown bare: `P, V`. -/
    | roles (names : Array String)
    /-- Source that the message composes: its parts bare, the whole quoted once. -/
    | code (inner : Message)

  /-- A message: its parts in order. -/
  inductive Message where
    | parts (parts : Array MessagePart)
end

instance : Inhabited MessagePart := ⟨.text ""⟩
instance : Inhabited Message := ⟨.parts #[]⟩

namespace Message

def empty : Message := .parts #[]

def toParts : Message → Array MessagePart
  | .parts items => items

def ofPart (part : MessagePart) : Message := .parts #[part]

def ofText (text : String) : Message := ofPart (.text text)

def append (first second : Message) : Message := .parts (first.toParts ++ second.toParts)

instance : Append Message := ⟨append⟩

/-- Source that the message composes, quoted once. -/
def code (inner : Message) : Message := ofPart (.code inner)

/-- The messages joined by a separator. -/
def joinWith (separator : String) (messages : Array Message) : Message := Id.run do
  let mut result := empty
  for index in [0:messages.size] do
    if index != 0 then result := result ++ ofText separator
    result := result ++ messages[index]!
  return result

end Message

/-- What can stand in a message. -/
class ToMessage (α : Type) where
  toMessage : α → Message

export ToMessage (toMessage)

instance : ToMessage Message := ⟨id⟩
instance : ToMessage String := ⟨Message.ofText⟩
instance : ToMessage Nat := ⟨fun value => .ofPart (.number value)⟩
instance : ToMessage ClosedType := ⟨fun type => .ofPart (.type type)⟩
instance : ToMessage StaticValue := ⟨fun value => .ofPart (.value value)⟩
instance : ToMessage Expr := ⟨fun expr => .ofPart (.expr expr)⟩
instance : ToMessage TypeExpr := ⟨fun type => .ofPart (.typeExpr type)⟩
instance : ToMessage Name := ⟨fun name => .ofPart (.name name.text)⟩

/-- `msg!"{e} is a {found}; {expected} is expected"`: a message from a text with parts in it.
Each part is what `toMessage` makes of the term. -/
syntax:max "msg!" interpolatedStr(term) : term

macro_rules
  | `(msg! $text) => do
    text.expandInterpolatedStr (← `(Zkc.Frontend.Message)) (← `(Zkc.Frontend.toMessage))

/-- How the parts that name something of a program are shown. -/
structure Renderer where
  type : ClosedType → String
  value : StaticValue → String
  «instance» : InstanceId → String
  instantiation : DeclarationId → Array StaticValue → String
  declaration : DeclarationId → String

namespace Renderer

mutual
  /-- A closed type without the names of a program: a row by its name in the vocabulary, a
  declared type by the number of its instance. -/
  partial def plainType : ClosedType → String
    | .bool => "bool"
    | .nat => "nat"
    | .rational => "rational"
    | .index bound => s!"index<{bound}>"
    | .nonzero field => s!"nonzero<{plainType field}>"
    | .seq element (some size) => s!"[{plainType element}; {size}]"
    | .seq element none => s!"[{plainType element}]"
    | .tuple components names =>
      let parts := (components.zip names).map fun (component, name) =>
        match name with
        | some name => s!"{name}: {plainType component}"
        | none => plainType component
      s!"({", ".intercalate parts.toList})"
    | .nominal row arguments =>
      if arguments.isEmpty then row
      else s!"{row}<{", ".intercalate (arguments.toList.map plainValue)}>"
    | .record id => s!"record#{id}"
    | .variant id => s!"variant#{id}"
    | .specification id => s!"spec#{id}"
    | .opaque «module» member arguments _ =>
      let base := s!"module#{«module»}::{member}"
      if arguments.isEmpty then base
      else s!"{base}<{", ".intercalate (arguments.toList.map plainValue)}>"

  partial def plainValue : StaticValue → String
    | .type type => plainType type
    | .natural value => toString value
    | .module id => s!"module#{id}"
end

/-- The renderer that knows no program: for a message shown before one exists, and for the
printed form of a typed tree. -/
def plain : Renderer where
  type := plainType
  value := plainValue
  «instance» := fun id => s!"instance#{id}"
  instantiation := fun declaration arguments =>
    if arguments.isEmpty then s!"declaration#{declaration}"
    else s!"declaration#{declaration}<{", ".intercalate (arguments.toList.map plainValue)}>"
  declaration := fun id => s!"declaration#{id}"

end Renderer

namespace Message

def exprText (expr : Expr) : String := Layout.flatten (Printer.atoms (Printer.expr expr))

def typeExprText (type : TypeExpr) : String :=
  Layout.flatten (Printer.atoms (Printer.typeExpr type))

/-- A piece of the program between backquotes, or bare inside `code`. -/
def quote (quoted : Bool) (text : String) : String := if quoted then s!"`{text}`" else text

mutual
  /-- One part as text. `quoted` says whether a piece of the program is shown between
  backquotes: it is, except inside `code`. -/
  partial def renderPart (renderer : Renderer) (quoted : Bool) : MessagePart → String
    | .text text => text
    | .source text => quote quoted text
    | .expr expr => quote quoted (exprText expr)
    | .typeExpr type => quote quoted (typeExprText type)
    | .type type => quote quoted (renderer.type type)
    | .value value => quote quoted (renderer.value value)
    | .number value => toString value
    | .name name => quote quoted name
    | .instance id => quote quoted (renderer.instance id)
    | .instantiation declaration arguments =>
      quote quoted (renderer.instantiation declaration arguments)
    | .declaration id => quote quoted (renderer.declaration id)
    | .roles names => ", ".intercalate names.toList
    | .code inner => quote quoted (renderWith renderer false inner)

  partial def renderWith (renderer : Renderer) (quoted : Bool) (message : Message) : String :=
    message.toParts.foldl (init := "") fun text part => text ++ renderPart renderer quoted part
end

/-- The message as text. -/
def render (renderer : Renderer) (message : Message) : String := renderWith renderer true message

end Message

end Zkc.Frontend
