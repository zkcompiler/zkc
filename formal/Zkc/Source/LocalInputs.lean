import Zkc.Source.InputBinding
import Zkc.Source.Program

/-! Role-local resolution of declared inputs and captures.

The world supplies only currently available values. Hidden provider state is
separate and cannot be named by this resolver. Source interpretation and the
execution handler must be fixed independently of that hidden state; this module
does not inspect arbitrary host-language closures or authenticate input origins.
-/

set_option autoImplicit false

namespace Zkc.Source.LocalInputs

variable {Ty : Type} {Value : Ty → Type} {Hidden : Type}

abbrev Store (Value : Ty → Type) := String → (ty : Ty) → Option (Value ty)

structure World (Value : Ty → Type) (Hidden : Type) where
  shared : Store Value
  privateInputs : String → Store Value
  hidden : Hidden

def SameView (role : String) (left right : World Value Hidden) : Prop :=
  left.shared = right.shared ∧ left.privateInputs role = right.privateInputs role

def read (role : String) (declaration : InputDeclaration Ty) (world : World Value Hidden) :
    Except BindingError (Value declaration.type) := do
  let store ← match declaration.access with
    | .shared => pure world.shared
    | .privateTo owner =>
        if owner = role then pure (world.privateInputs role) else .error (.wrongRole declaration.name)
  match store declaration.name declaration.type with
  | some value => .ok value
  | none => .error (.missingInput declaration.name)

theorem read_agrees (role : String) (declaration : InputDeclaration Ty)
    (left right : World Value Hidden) (same : SameView role left right) :
    read role declaration left = read role declaration right := by
  cases access : declaration.access <;> simp only [read, access, same.1, same.2]

def collect (role : String) (world : World Value Hidden) :
    List (InputDeclaration Ty) → Except BindingError (List (SuppliedInput Value))
  | [] => .ok []
  | declaration :: tail => do
      let value ← read role declaration world
      let rest ← collect role world tail
      return ⟨declaration.name, declaration.type, value⟩ :: rest

theorem collect_agrees (role : String) (declarations : List (InputDeclaration Ty))
    (left right : World Value Hidden) (same : SameView role left right) :
    collect role left declarations = collect role right declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration tail ih =>
    simp only [collect, read_agrees role declaration left right same, ih]

def bind [DecidableEq Ty] (role : String) (declarations : List (InputDeclaration Ty))
    (world : World Value Hidden) : Except BindingError (Values Value (declarations.map (·.type))) := do
  let supplied ← collect role world declarations
  bindInputs role declarations supplied

theorem bind_agrees [DecidableEq Ty] (role : String) (declarations : List (InputDeclaration Ty))
    (left right : World Value Hidden) (same : SameView role left right) :
    bind role declarations left = bind role declarations right := by
  simp only [bind, collect_agrees role declarations left right same]

variable {language : Language} [DecidableEq language.Ty] {I : PIR.Signature} {S E : Type}

def run (meaning : Interpretation language I) (handler : PIR.Handler I S E)
    (role : String) (declarations : List (InputDeclaration language.Ty)) {ty : language.Ty}
    (source : Program language (declarations.map (·.type)) ty)
    (world : World meaning.Value Hidden) (state : S) :
    Except BindingError (PIR.Execution S E (meaning.Value ty)) := do
  let values ← bind role declarations world
  return (source.denote meaning values.get).run handler state

/-- Equal available views give equal binding failures or complete executions of
the actual same source. Both arguments and immutable captures use this resolver. -/
theorem run_agrees (meaning : Interpretation language I) (handler : PIR.Handler I S E)
    (role : String) (declarations : List (InputDeclaration language.Ty)) {ty : language.Ty}
    (source : Program language (declarations.map (·.type)) ty)
    (left right : World meaning.Value Hidden) (state : S) (same : SameView role left right) :
    run meaning handler role declarations source left state =
      run meaning handler role declarations source right state := by
  simp only [run, bind_agrees role declarations left right same]

end Zkc.Source.LocalInputs
