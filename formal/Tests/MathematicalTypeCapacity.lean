import Tests.MathematicalSubjectAdmission
import Tests.MathematicalProtocol
import Tests.MathematicalTypeExpansion
import Tests.Checks

/-! Expanded type size counts repeated children even when storage is shared.
The tests exercise constructor boundaries, intrinsic formation, and serialized
whole-subject admission. Payload costs and total work have separate obligations.
-/

set_option autoImplicit false
namespace Tests.MathematicalTypeCapacity
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (Ty number publicPort privatePort)

def doubled : Nat → Ty
  | 0 => number
  | n + 1 => let child := doubled n; .product [child, child]

def unary : Nat → Ty
  | 0 => number
  | n + 1 => .product [unary n]

def tupleGraph (doubling wrappers : Nat) (project : Bool := true) : Graph.Raw MathematicalGraph.Op :=
  let finish := if project then
      (List.range (doubling + wrappers)).foldr (fun _ rest => .project 0 0 rest) (.outputs [0])
    else .outputs [0]
  let wrapped := (List.range wrappers).foldr (fun _ rest => .tuple [0] rest) finish
  (List.range doubling).foldr (fun _ rest => .tuple [0, 0] rest) wrapped

def tupleSubject (doubling wrappers : Nat) : Raw.Subject :=
  let port : Raw.Port := ⟨[⟨0⟩], MathematicalDeclarations.booleanUse⟩
  let nodes := List.replicate doubling (.tuple [⟨0⟩, ⟨0⟩]) ++
    List.replicate wrappers (.tuple [⟨0⟩]) ++ List.replicate (doubling + wrappers) (.project ⟨0⟩ 0)
  MathematicalClosedInstances.subject
    [{ MathematicalClosedInstances.leaf with
      arguments := [port]
      results := [port]
      body := .mk [.pure ⟨[⟨0⟩], nodes, [⟨0⟩]⟩] (.ret [⟨0⟩]) }]

def parametricTemplates (wrappers : Nat) : List Raw.TypeTemplate :=
  [⟨0, .fin (.literal 2)⟩, ⟨1, .vector ⟨⟨0⟩, []⟩ (.parameter 0)⟩] ++
  (List.range wrappers).map (fun i => ⟨1, .product [⟨⟨i + 1⟩, [.parameter 0]⟩]⟩)

def doublingTemplates (count : Nat) : List Raw.TypeTemplate :=
  [⟨0, .fin (.literal 2)⟩] ++ (List.range count).map
    (fun i => ⟨0, .product [⟨⟨i⟩, []⟩, ⟨⟨i⟩, []⟩]⟩)

/-- Isolate structural formation from the separate default work allowance.
The full consumer still has to reconcile its costs with native memoization. -/
def templateFormation (types : List Raw.TypeTemplate) (budget : Nat) : Except TypeAdmission.Error Unit :=
  (do
    let _ ← TypeAdmission.declarations MathematicalTypes.emptyMeaning (fun _ => false) types
    pure ()).run' budget

def serializedResource (source : Raw.Subject) : Except String Bool := do
  let bytes ← Tools.Mathematical.Codec.encode (← Tools.Mathematical.SchemaEncoding.encode source)
  let source ← Tools.Mathematical.Schema.decode (← Tools.Mathematical.Codec.decode bytes)
  return match (SubjectAdmission.admit MathematicalDeclarations.contracts source).run' 1000000 with
    | .error (.template (.definition (.body (.protocol (.graph .resource))))) => true
    | _ => false

def size (type : Ty) : Option TypeSize := (Data.capacity.measure type).map (fun certificate => (Data.capacity.measurement certificate).size)

def doubledCertificate : (depth : Nat) → Option (Data.capacity.Measured (doubled depth))
  | 0 => Data.capacity.measure number
  | depth + 1 => do
      let child ← doubledCertificate depth
      Data.capacity.measureProduct (.cons child (.cons child .nil))

/-- Constructed products retain their input certificates. Disabling boundary
measurement catches a projection implementation that discards this reuse. -/
def projectCertified : Bool :=
  let parent : Ty := doubled 15
  match doubledCertificate 15 with
  | none => false
  | some certificate =>
    let cachedOnly : Graph.Capacity MathematicalGraph.algebra :=
      { Data.capacity with measure := fun _ => none }
    let raw : Graph.Raw MathematicalGraph.Op :=
      (List.range 128).foldr (fun i next => .project i 0 next) (.outputs [0])
    (Graph.decodeMeasured [0] cachedOnly (fun _ => true) 65 [⟨[0], parent⟩]
      (.cons certificate .nil) raw).isOk

def graphRefuses {algebra : Graph.Algebra} [DecidableEq algebra.Ty]
    {parties : List Nat} {Γ raw} (result : Except Graph.Error (Graph.Decoded parties algebra Γ raw)) : Bool :=
  match result with | .error .resource => true | _ => false

def protocolRefuses {vocabulary : Protocol.Vocabulary} {parties : List Nat} {caps scope Γ results start raw}
    (result : Except Protocol.Error (Protocol.Formed parties vocabulary caps scope Γ results start raw)) : Bool :=
  match result with | .error .resource => true | _ => false

-- Cached measurements certify the actual type, rather than an independent
-- unchecked estimate. These implications hold for every returned certificate.
example (type : Ty) (measured : Data.capacity.Measured type) :
    type.nodes ≤ FormationLimits.typeNodes ∧ type.height ≤ FormationLimits.typeDepth + 1 := by
  let measurement := Data.capacity.measurement measured
  simpa [TypeSize.Within, measurement.nodes_eq, measurement.height_eq, Data.capacity] using measurement.within

example (type : Ty) (view : CertifiedProductView Data.Shape.product Data.capacity.Certificate type) :
    type = .product view.types := view.sound

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds projectCertified "repeated projection reuses child certificates without a boundary walk"
  checks.holds (size (.product []) == some ⟨1, 1⟩) "empty product counts its root"
  checks.holds (size (doubled 15) == some ⟨65535, 16⟩) "shared binary children count repeatedly"
  checks.holds (size (.product [doubled 15]) == some ⟨65536, 17⟩) "exact expanded node boundary"
  checks.holds (size (.product [.product [doubled 15]]) == none) "one node beyond boundary refuses"
  checks.holds (size (doubled 16) == none) "compact doubling refuses before unbounded measurement"
  checks.holds (size (unary 64) == some ⟨65, 65⟩) "root depth zero permits height 65"
  checks.holds (size (unary 65) == none) "height 66 refuses"
  checks.holds (size (.vector number 1000000000) == some ⟨2, 2⟩) "vector count is not unrolled"
  checks.holds (MathematicalGraph.admit [publicPort] (tupleGraph 15 1)).isOk
    "cached tuple formation and proved projection at exact node boundary"
  checks.holds (graphRefuses (MathematicalGraph.admit [publicPort] (tupleGraph 16 0)))
    "derived doubled type refuses at construction"
  checks.holds (graphRefuses (MathematicalGraph.admit [publicPort] (tupleGraph 15 2 false)))
    "unused over-limit projection-free output still refuses"
  checks.holds (MathematicalGraph.admit [publicPort] (tupleGraph 0 64)).isOk
    "flat unary tuple chain obeys structural depth independently of graph nesting"
  checks.holds (graphRefuses (MathematicalGraph.admit [publicPort] (tupleGraph 0 65)))
    "derived tuple depth refuses before insertion"
  checks.holds (graphRefuses (MathematicalGraph.admit [publicPort (doubled 16)] (.outputs [])))
    "unused external context type is measured"
  checks.holds (match Graph.decode (algebra := MathematicalGraph.algebra) [0, 1] Data.capacity
    MathematicalGraph.countValid 0 [publicPort (doubled 16)] (.outputs []) with
    | .error .depth => true | _ => false) "exhausted graph depth refuses before context measurement"
  let oversizedResult : Graph.Algebra := { MathematicalGraph.algebra with result := fun _ => doubled 16 }
  checks.holds (graphRefuses (Graph.decode (algebra := oversizedResult) [0, 1] Data.capacity
    MathematicalGraph.countValid 65 [] (.operation .zero [] (.outputs []))))
    "operation result measured before insertion even when unused"
  let oversizedInput : Graph.Algebra := { MathematicalGraph.algebra with arguments := fun _ => [doubled 16] }
  checks.holds (graphRefuses (Graph.decode (algebra := oversizedInput) [0, 1] Data.capacity
    MathematicalGraph.countValid 65 [publicPort] (.operation .add [0] (.outputs []))))
    "operation input measured before type comparison"
  let full := .product [doubled 15]
  checks.holds (graphRefuses (MathematicalGraph.admit [publicPort full]
    (.map 0 [0] (.outputs [1]) (.outputs []))))
    "zero map still refuses over-limit vector type"
  checks.holds (protocolRefuses (Protocol.form (vocabulary := MathematicalProtocol.vocabulary)
    [0, 1] [] [] Data.capacity MathematicalGraph.countValid 65 [] [privatePort (doubled 16)] 0 (.ret [])))
    "protocol result type measured before return arity check"
  checks.holds (match Protocol.form (vocabulary := MathematicalProtocol.vocabulary)
    [0, 1] [] [] Data.capacity MathematicalGraph.countValid 0 [] [privatePort (doubled 16)] 0 (.ret []) with
    | .error .depth => true | _ => false) "exhausted body depth refuses before result measurement"
  checks.holds (protocolRefuses (Protocol.form (vocabulary := MathematicalProtocol.vocabulary)
    [0, 1] [] [] Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0
    (.message 0 ⟨doubled 16, ()⟩ 0 1 0 (.ret []))))
    "message type measured before operand equality"
  checks.holds (protocolRefuses (Protocol.form (vocabulary := MathematicalProtocol.vocabulary)
    [0, 1] [] [] Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0
    (.repeat 0 0 [privatePort (doubled 16)] [0] [] (.ret [0]) (.ret []))))
    "zero repeat carried type measured before equality"
  let oversizedIndex : Graph.Algebra := { MathematicalGraph.algebra with index := fun _ => doubled 16 }
  checks.holds (graphRefuses (Graph.decode (algebra := oversizedIndex) [0, 1] Data.capacity
    MathematicalGraph.countValid 65 [] (.map 0 [] (.outputs []) (.outputs []))))
    "map index type measured even for zero count"
  checks.holds (graphRefuses (Graph.decode (algebra := oversizedIndex) [0, 1] Data.capacity
    MathematicalGraph.countValid 65 [] (.fold 0 [] [] (.outputs []) (.outputs []))))
    "fold index type measured even for zero count"
  let oversizedCondition : Protocol.Vocabulary := { MathematicalProtocol.vocabulary with condition := doubled 16 }
  checks.holds (protocolRefuses (Protocol.form (vocabulary := oversizedCondition) [0, 1] [] []
    Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0 (.guard 0 0 0 (.ret []))))
    "guard condition measured before reference equality"
  let localInput : Protocol.Vocabulary := { MathematicalProtocol.vocabulary with localArguments := fun _ => [doubled 16] }
  checks.holds (protocolRefuses (Protocol.form (vocabulary := localInput) [0, 1] MathematicalProtocol.capabilities []
    Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0 (.local 0 0 .shared [0, 1] [0] (.ret []))))
    "local argument measured before reference equality"
  let localOutput : Protocol.Vocabulary := { MathematicalProtocol.vocabulary with localResult := fun _ => doubled 16 }
  checks.holds (protocolRefuses (Protocol.form (vocabulary := localOutput) [0, 1] MathematicalProtocol.capabilities []
    Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0 (.local 0 0 .shared [0, 1] [0] (.ret []))))
    "unused local result measured before insertion"
  let serviceInput : Protocol.Vocabulary := { MathematicalProtocol.vocabulary with serviceArguments := fun _ => [doubled 16] }
  checks.holds (protocolRefuses (Protocol.form (vocabulary := serviceInput) [0, 1] MathematicalProtocol.capabilities []
    Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0 (.query 0 0 0 [0] (.ret []))))
    "query argument measured before reference equality"
  let serviceOutput : Protocol.Vocabulary := { MathematicalProtocol.vocabulary with serviceResult := fun _ => doubled 16 }
  checks.holds (protocolRefuses (Protocol.form (vocabulary := serviceOutput) [0, 1] MathematicalProtocol.capabilities []
    Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0 (.query 0 0 0 [0] (.ret []))))
    "unused query result measured before insertion"
  let argument : Protocol.Signature Nat MathematicalProtocol.vocabulary := ⟨[0], [], [privatePort (doubled 16)], []⟩
  checks.holds (protocolRefuses (Protocol.form (vocabulary := MathematicalProtocol.vocabulary) [0, 1] [] [argument]
    Data.capacity MathematicalGraph.countValid 65 [privatePort] [] 0 (.invoke 0 0 [] [0] (.ret []))))
    "callee argument measured before call binding equality"
  let result : Protocol.Signature Nat MathematicalProtocol.vocabulary := ⟨[0], [], [], [privatePort (doubled 16)]⟩
  checks.holds (protocolRefuses (Protocol.form (vocabulary := MathematicalProtocol.vocabulary) [0, 1] [] [result]
    Data.capacity MathematicalGraph.countValid 65 [] [] 0 (.invoke 0 0 [] [] (.ret []))))
    "unused callee result measured before insertion"
  checks.holds (MathematicalTypeExpansion.closed (parametricTemplates 63) ⟨⟨64⟩, [.literal 5]⟩).isOk
    "closed parametric template chain reaches exact structural height"
  checks.holds (!(MathematicalTypeExpansion.closed (parametricTemplates 64) ⟨⟨0⟩, []⟩).isOk)
    "unused parametric template above structural height refuses"
  checks.holds (templateFormation (doublingTemplates 15) 1000000).isOk
    "unused shared templates below the node limit form"
  checks.holds (templateFormation (doublingTemplates 15 ++ [⟨0, .product [⟨⟨15⟩, []⟩]⟩]) 4000000).isOk
    "exact template node boundary forms with an explicit larger work allowance"
  checks.holds (match templateFormation (doublingTemplates 16) 4000000 with
    | .error (.expansion .resource) => true | _ => false)
    "unused excessive expanded template refuses despite larger work allowance"
  checks.holds (MathematicalSubjectAdmission.accepts (tupleSubject 15 1))
    "serialized whole subject accepts exact derived node boundary"
  checks.holds ((serializedResource (tupleSubject 15 2)).toOption == some true)
    "serialized whole subject refuses one additional type node"
  checks.holds (MathematicalSubjectAdmission.accepts (tupleSubject 0 64))
    "serialized whole subject accepts exact structural depth"
  checks.holds ((serializedResource (tupleSubject 0 65)).toOption == some true)
    "serialized whole subject refuses excessive structural depth"
  checks.finish "mathematical structural type capacity"

#eval run
end Tests.MathematicalTypeCapacity
