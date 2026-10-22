module

public import Zkc.Source.Structured.ProtocolScopes
public import Zkc.Source.Structured.ProtocolOperations
public import Zkc.Source.Structured.Algebra
public import Zkc.Source.Finite

@[expose] public section

namespace Zkc.Source.Structured

namespace Repeat

variable {F G : Type} {I : PIR.Signature}

/-- The concrete callback transition used by `denoteRepeat`. -/
abbrev step (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (state : Values (Component (assignment F G)) spec.state) (index : Nat) :=
  (body (.cons (some index)
    ((maskValues self (context.mapScopes spec.stateScopes) state).append captures))).bind
      (fun results => .done (maskValues self (context.mapScopes spec.stateScopes) results))

end Repeat

/-- Retained repeat uses the existing finite process fold. The bound is tested
before constructing its range, so even unrepresentably large natural counts
refuse immediately. Optional captures remain immutable and are demanded only
by reached callback operations. The context and root participant never change. -/
def denoteRepeat {F G : Type} {I : PIR.Signature}
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (count : Option Nat)
    (state : Values (Component (assignment F G)) spec.state)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state)) :
    PIR.Process I (Values (Component (assignment F G)) spec.state) :=
  if (spec.roles.map context.roles).contains self then
    match count with
    | none => .halt .incomplete
    | some count =>
      if count ≤ spec.maximum then
        let mask := maskValues self (context.mapScopes spec.stateScopes)
        Finite.execute (.elements (List.range count))
          (Repeat.step spec context self captures body) (mask state)
      else .halt .refused
  else .done (Values.absent (assignment F G) spec.state)

/-- Every operation interpretation commutes with repeat, including partial or
interacting callbacks and all count failures. Site erasure is one instance. -/
theorem denoteRepeat_interpret {F G : Type} {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (count : Option Nat)
    (state : Values (Component (assignment F G)) spec.state)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state)) :
    (denoteRepeat spec context self count state captures body).interpret operations =
      denoteRepeat spec context self count state captures
        (fun args => (body args).interpret operations) := by
  unfold denoteRepeat
  split
  · cases count with
    | none => rfl
    | some count =>
      dsimp only
      split
      · simp only [Finite.interpret_execute, Repeat.step, PIR.Process.interpret_bind, PIR.Process.interpret]
      · rfl
  · rfl

end Zkc.Source.Structured
