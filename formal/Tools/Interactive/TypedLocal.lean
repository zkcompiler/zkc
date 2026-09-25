import Tools.Interactive.Admission
import Tools.Interactive.Explicit
import Zkc.Source.ResultBundle

/-! Reify admitted explicit-binding local source into the maintained typed region.

Signatures are resolved independently from semantic bindings. The source's
operation sites, static identities and ordered ports survive reification; native
symbols, selected layouts and conversion instructions are not the reference body.
Straight-line bodies reify to a stored typed region. Local control retains the
independently admitted instruction tree; the reference adapter instantiates
`FiniteControl` typed branches and finite iterations after reading runtime values.
This executable elaborator is not itself covered by an adequacy theorem.
-/

set_option autoImplicit false

namespace Tools.Interactive.TypedLocal
open Zkc.Source

structure Request where
  site : Name
  contract : String
  arguments : List String
  attributes : List String
  signature : Bindings.Signature
  resolved : Bindings.resolve false ⟨"", contract, arguments, ""⟩ = .ok signature

abbrev signature : ResultBundle.Signature where
  Ty := Bindings.ValueType
  Op := Request
  arguments request := request.signature.inputs
  results request := request.signature.outputs
  condition := ⟨"bool", "", ""⟩

abbrev language := ResultBundle.language signature

/-- Store typed references directly so adding a binder shares existing variable
paths. Rebuilding de Bruijn paths from numeric indices at every use is quadratic
even for a sequence of guards on one input. Bundles have no source name. -/
private structure Named (Γ : List language.Ty) where
  name : Name
  ty : Bindings.ValueType
  value : Var Γ [ty]

private abbrev Names (Γ : List language.Ty) := List (Named Γ)

private def read {Γ : List language.Ty} (names : Names Γ) (name : Name)
    (ty : Bindings.ValueType) : Result (Var Γ [ty]) := do
  let some binding := names.find? (fun binding => binding.name == name) | throw s!"unbound:{name}"
  if same : binding.ty = ty then return same ▸ binding.value
  else throw "typed-local-operand-type"

private def arguments {Γ : List language.Ty} (names : Names Γ) :
    (types : List Bindings.ValueType) → List Name →
    Result (Operands Γ (types.map List.singleton))
  | [], [] => .ok .nil
  | ty :: types, name :: rest => do
      return .cons (← read names name ty) (← arguments names types rest)
  | _, _ => .error "typed-local-operand-arity"

private def namedResults (Γ : List language.Ty) : (types : List Bindings.ValueType) →
    List Name → Result (Names (types.map List.singleton ++ Γ))
  | [], [] => .ok []
  | ty :: types, name :: rest => do
      let tail ← namedResults Γ types rest
      return ⟨name, ty, .here⟩ :: tail.map fun binding =>
        ⟨binding.name, binding.ty, .there binding.value⟩
  | _, _ => .error "typed-local-result-arity"

private def retain {Γ : List language.Ty} (outputs : List Bindings.ValueType)
    (names : Names Γ) : Names (outputs.map List.singleton ++ outputs :: Γ) :=
  names.map fun binding =>
    ⟨binding.name, binding.ty,
      (Var.there (head := outputs) binding.value).weakenPrefix (outputs.map List.singleton)⟩

/-- Resolve a logical request independently of the selected physical kernel. -/
def resolveRequest (bindings : List OperationBinding) (site name : Name)
    (attrs : List String) : Result Request := do
  let binding ← lookup name (bindings.map fun binding => (binding.name, binding))
  Bindings.attributes false binding.contract attrs (binding.arguments.headD Bindings.fr)
  -- Source formation already checked any fixed implementation. The mathematical
  -- request retains only the semantic contract and static identities.
  let logical := OperationBinding.mk "" binding.contract binding.arguments ""
  match resolved : Bindings.resolve false logical with
  | .error code => throw code
  | .ok signature => return ⟨site, binding.contract, binding.arguments, attrs, signature, resolved⟩

private def body (bindings : List OperationBinding) (results : List Bindings.ValueType) :
    (code : List Instruction) → (Γ : List language.Ty) → Names Γ →
    Result (Region language Γ results)
  | [.ret values], _, names => do
      let inputs ← arguments names results values
      return .letOp (.pack results) inputs (.ret .here)
  | .op site name attrs inputs outputs :: rest, Γ, names => do
      let op ← resolveRequest bindings site name attrs
      let inputs ← arguments names op.signature.inputs inputs
      ensure (outputs.length == op.signature.outputs.length) "typed-local-result-arity"
      ensure (unique outputs && outputs.all (fun n => !(names.any fun p => p.name == n)))
        "typed-local-rebinding"
      let nextNames ← namedResults (op.signature.outputs :: Γ) op.signature.outputs outputs
      let nextNames := nextNames ++ retain op.signature.outputs names
      let next ← body bindings results rest
        (op.signature.outputs.map List.singleton ++ op.signature.outputs :: Γ) nextNames
      return ResultBundle.invoke op inputs next
  | _, _, _ => .error "typed-local-terminal"

structure Function where
  name : Name
  origin : Option Explicit.Origin
  arguments : List (Name × Bindings.ValueType)
  results : List Bindings.ValueType
  /-- Present for straight-line source; structured source is instantiated at runtime. -/
  code : Option (Region language ((arguments.map Prod.snd).map List.singleton) results)
  structured : List Instruction
  bindings : List OperationBinding

/-- Formation checks, including affine use, run before typed reification. -/
def elaborate (bindings : List OperationBinding) (function : Explicit.Function) : Result Function := do
  ensure (unique (bindings.map OperationBinding.name)) "duplicate-symbol"
  admitFunctionWith (environmentSignature (.explicit bindings) "logical") function.code
  let args ← function.code.arguments.mapM fun (name, ty) => do
    return (name, ← Bindings.valueType false ty)
  let results ← function.code.results.mapM (Bindings.valueType false)
  let some instructions := function.code.body | throw "external-function"
  let names ← namedResults [] (args.map Prod.snd) (args.map Prod.fst)
  let names : Names ((args.map Prod.snd).map List.singleton) := by
    simpa only [List.append_nil] using names
  let structured := hasLocalControl instructions
  let code ← if structured then pure none else some <$> body bindings results instructions ((args.map Prod.snd).map List.singleton) names
  return ⟨function.code.name, function.origin, args, results, code, instructions, bindings⟩

end Tools.Interactive.TypedLocal
