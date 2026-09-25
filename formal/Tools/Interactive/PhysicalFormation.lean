import Tools.Interactive.Admission

/-! Independent formation of selected physical locals. Diagonal values are
immutable, depth-one local data: every use must be a matching contraction's
values operand. This establishes formation, not allocator correspondence. -/

set_option autoImplicit false

namespace Tools.Interactive.PhysicalFormation

private def diagonal (ty : Ty) : Bool :=
  ty.endsWith "@arkworks.fr-diagonal/1" || ty.endsWith "@dalek.ristretto-diagonal/1"

def checkBody (bindings : List OperationBinding) : Nat → List Instruction → Result Unit
  | 0, _ => .error "body-depth-limit"
  | depth + 1, body => do
      let mut views : List (Name × String) := []
      let mut used : List Name := []
      for instruction in body do
        match instruction with
        | .op _ key _ inputs outputs =>
            let binding ← lookup key (bindings.map fun b => (b.name, b))
            for (input, index) in inputs.zipIdx do
              if let some (_, consumer) := views.find? (fun v => v.1 == input) then
                ensure (index == 1 && binding.implementation == consumer) "diagonal-use"
                used := input :: used
            let signature ← Bindings.resolve true binding
            for (name, ty) in outputs.zip signature.outputs do
              if diagonal ty.spelling then
                let consumer ← match binding.implementation with
                  | "arkworks-diagonal/vector.mul" => pure "arkworks-diagonal/vector.dot"
                  | "dalek-diagonal/curve.scale_each" => pure "dalek-diagonal/curve.msm"
                  | _ => throw "diagonal-producer"
                views := (name, consumer) :: views
        | .release _ => pure () -- Safety already checked against the full body above.
        | .variant _ _ _ payload _ =>
            ensure (!(payload.any fun n => views.any (fun v => v.1 == n))) "diagonal-escape"
        | .localMatch _ input captures arms _ =>
            ensure (!((input :: captures).any fun n => views.any (fun v => v.1 == n))) "diagonal-escape"
            for arm in arms do checkBody bindings depth arm.2.2
        | .stop .. => pure ()
        | .conditional _ _ captures yes no _ =>
            ensure (!(captures.any fun n => views.any (fun v => v.1 == n))) "diagonal-escape"
            checkBody bindings depth yes
            checkBody bindings depth no
        | .forLoop _ _ _ _ carried captures nested _ =>
            ensure (!((captures ++ carried.map Prod.snd).any fun n => views.any (fun v => v.1 == n))) "diagonal-escape"
            checkBody bindings depth nested
        | .ret values | .yield values =>
            ensure (!(values.any fun n => views.any (fun v => v.1 == n))) "diagonal-escape"
        | _ => throw "invalid-function-body"
      ensure (views.all fun v => used.contains v.1) "diagonal-unused"

def check (bindings : List OperationBinding) (function : Function) : Result Unit := do
  admitFunctionWith (environmentSignature (.explicit bindings) "physical") function true true
  ensure (!(function.arguments.any fun p => diagonal p.2) &&
    !(function.results.any diagonal)) "diagonal-boundary"
  let some body := function.body | throw "external-function"
  checkBody bindings limits.depth body

end Tools.Interactive.PhysicalFormation
