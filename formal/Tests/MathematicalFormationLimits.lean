import Zkc.Source.Mathematical.DataBounds
import Tests.MathematicalSubjectAdmission
import Tests.MathematicalProtocolResolution

/-! Nesting is independent of sequence length. Direct formation tests reach
its depth boundary; serialized subjects additionally obey carrier-tree depth.
-/

set_option autoImplicit false
namespace Tests.MathematicalFormationLimits
open Zkc.Source.Mathematical

def maps : Nat → Raw.Region
  | 0 => ⟨[], [], []⟩
  | depth + 1 => ⟨[], [.map (.literal 0) (maps depth)], []⟩

def folds : Nat → Raw.Region
  | 0 => ⟨[], [], []⟩
  | depth + 1 => ⟨[], [.fold (.literal 0) [] (folds depth)], []⟩

def repeats (regionDepth : Nat) : Nat → Nat → Raw.Body
  | 0, _ => .mk [.pure (maps regionDepth)] (.ret [])
  | depth + 1, site => .mk
      [.repeat site (.literal 0) [] [] [] (repeats regionDepth depth (site + 1))] (.ret [])

def graph : Nat → Graph.Raw MathematicalGraph.Op
  | 0 => .outputs []
  | depth + 1 => .map 0 [] (graph depth) (.outputs [])

def program : Nat → Nat → Protocol.Raw Nat MathematicalProtocol.vocabulary
  | 0, _ => .ret []
  | depth + 1, site => .repeat site 0 [] [] [] (program depth (site + 1)) (.ret [])

def flat (siblings depth : Nat) : Raw.Subject := MathematicalClosedInstances.subject
  [{ MathematicalClosedInstances.leaf with body := (.mk
      (List.replicate siblings (.pure ⟨[], [], []⟩) ++ [.pure (maps depth)]) (.ret [])) }]

def admitBody (body : Raw.Body) := ProtocolResolution.admit MathematicalProtocolResolution.resolver
  [0, 1] [] [] Data.capacity MathematicalGraph.countValid [] [] body

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (MathematicalGraphResolution.admit [] (maps 32)).isOk
    "native region depth 64 permits 32 nested maps"
  checks.holds (match MathematicalGraphResolution.admit [] (maps 33) with
    | .error .depth => true | _ => false) "region depth 66 refuses with depth diagnostic"
  checks.holds (MathematicalGraphResolution.admit [] (folds 32)).isOk
    "fold region boundary agrees with map boundary"
  checks.holds (match MathematicalGraphResolution.admit [] (folds 33) with
    | .error .depth => true | _ => false) "fold refuses excess region depth"
  checks.holds (admitBody (repeats 0 32 0)).isOk
    "native body depth 64 permits 32 nested repeats"
  checks.holds (match admitBody (repeats 0 33 0) with
    | .error .depth => true | _ => false) "body depth 66 refuses with depth diagnostic"
  checks.holds (admitBody (repeats 32 32 0)).isOk
    "pure region depth starts independently at the deepest permitted body"
  checks.holds (match admitBody (repeats 33 32 0) with
    | .error (.graph .depth) => true | _ => false)
    "pure reset still refuses an independently excessive region"
  let atBoundary : Raw.Body := .mk
    (List.replicate 5000 (.pure ⟨[], [], []⟩) ++ [.pure (maps 32)]) (.ret [])
  checks.holds (admitBody atBoundary).isOk
    "5000 siblings preserve exact region boundary through intrinsic formation"
  let overBoundary : Raw.Body := .mk
    (List.replicate 5000 (.pure ⟨[], [], []⟩) ++ [.pure (maps 33)]) (.ret [])
  checks.holds (match admitBody overBoundary with
    | .error (.graph .depth) => true | _ => false)
    "late excessive region still reports depth"
  let growing : Raw.Region := ⟨[], List.replicate 5000 (.tuple []), []⟩
  checks.holds (MathematicalGraphResolution.admit [] growing).isOk
    "5000 output-producing nodes form a growing intrinsic context"
  checks.holds (Graph.decode (algebra := MathematicalGraph.algebra) [0, 1]
    Data.capacity MathematicalGraph.countValid 65 [] (graph 32)).isOk
    "intrinsic region boundary agrees with resolution"
  checks.holds (match Graph.decode (algebra := MathematicalGraph.algebra) [0, 1]
    Data.capacity MathematicalGraph.countValid 65 [] (graph 33) with
    | .error .depth => true | _ => false) "intrinsic region refuses excess depth"
  checks.holds (Protocol.form (vocabulary := MathematicalProtocol.vocabulary) [0, 1] [] []
    Data.capacity MathematicalGraph.countValid 65 [] [] 0 (program 32 0)).isOk
    "intrinsic body boundary agrees with resolution"
  checks.holds (match Protocol.form (vocabulary := MathematicalProtocol.vocabulary) [0, 1] [] []
    Data.capacity MathematicalGraph.countValid 65 [] [] 0 (program 33 0) with
    | .error .depth => true | _ => false) "intrinsic body refuses excess depth"
  checks.holds ((ClosedInstances.collectBody 65 (repeats 0 32 0)).run' 1000000).isOk
    "closed call collection preserves exact nesting allowance"
  checks.holds (match (ClosedInstances.collectBody 65 (repeats 0 33 0)).run' 1000000 with
    | .error .depth => true | _ => false) "closed call collection refuses excess body depth"
  let tooDeep := MathematicalClosedInstances.subject
    [{ MathematicalClosedInstances.leaf with body := repeats 0 33 0 }]
  checks.holds (match (SubjectAdmission.admit MathematicalDeclarations.contracts tooDeep).run' 1000000 with
    | .error (.template .depth) => true | _ => false)
    "symbolic call collection refuses excess depth before body formation"
  checks.holds (MathematicalSubjectAdmission.accepts (flat 5000 0))
    "serialized 5000 flat siblings pass all symbolic and closed formation phases"
  checks.holds (MathematicalSubjectAdmission.accepts (flat 4070 12))
    "late nested graph retains the same depth allowance as an early graph"
  checks.finish "mathematical formation depth"

#eval run
end Tests.MathematicalFormationLimits
