import Zkc.Core.Lower
import Zkc.Core.Admission
import Zkc.Core.Package

/-! The lowering of a named program.

- A named program of every shape is lowered and admitted: a `compute` at several roles, a
  choice on a condition and on a variant, a loop with carried and collected values, an
  application under a role map that is not the identity, a block, a join. Its sites are
  numbered in the order of the body, each with its key, and its block has its program point.
- A named program whose shape is not that of its operations is refused, with the tag of the
  instruction: an instruction that names more or fewer results than its operation has, a name
  bound twice, a role map without a role for a holder of the callee.
- A name read at a role that holds no copy of it is refused, with the tag.
-/

set_option autoImplicit false

open Zkc.Core Zkc.Core.Named

namespace LoweringTests

def emptyPackage : Named.Package :=
  { types := [], records := [], variants := [⟨[.nat, .tuple []]⟩], operations := [], functions := [],
    protocols := [], functionNames := [], protocolNames := [], roleNames := [] }

def cmp (tag : Nat) (roles : List Nat) (results : List ValueName) (step : Named.LocalOp) :
    ProtocolInstruction :=
  .mk tag [] (.compute roles [.mk tag results step])

def site (event : Nat) (name : String) : Named.Site := ⟨⟨event, "", []⟩, name⟩

/-- Callee: roles A=0, B=1; input `n` agreed, output `m` agreed, `m = n + n` at both. -/
def callee : Named.Protocol :=
  { specificationOnly := false, roles := 2
    inputs := [⟨.nat, [0, 1]⟩], outputs := [⟨.nat, [0, 1]⟩]
    body := .mk [0] [cmp 1 [0, 1] [1] (.builtin .natAdd [0, 0])] (.ret [1]) }

/-- Roles P=0, V=1, W=2. Names: 0 x @{P,V}, 1 c @{P,V}, 2 v @{P,V} (a variant). -/
def mainProtocol : Named.Protocol :=
  { specificationOnly := false, roles := 3
    inputs := [⟨.nat, [0, 1]⟩, ⟨.bool, [0, 1]⟩, ⟨.variant 0 [], [0, 1]⟩]
    outputs := [⟨.nat, [0, 1]⟩, ⟨.nat, [2]⟩, ⟨.nat, [0, 1]⟩]
    body := .mk [0, 1, 2]
      [ -- guard x < 10 at P and V
        cmp 100 [0, 1] [10] (.literal (.nat 10)),
        cmp 101 [0, 1] [11] (.builtin .natLess [0, 10]),
        cmp 102 [0, 1] [] (.guard .reject 11),
        cmp 103 [0, 1] [12] (.builtin .natAdd [0, 0]),
        .mk 104 [13] (.exchange 0 2 (site 104 "y") 12),
        .mk 105 [14] (.choose [0, 1] 1 .condition [⟨.nat, [0, 1]⟩]
          [.mk [] [cmp 106 [0, 1] [15] (.builtin .natAdd [12, 12])] (.ret [15]),
           .mk [] [cmp 107 [0, 1] [16] (.literal (.nat 0))] (.ret [16])]),
        .mk 108 [17] (.choose [0, 1] 2 (.alternative 0 []) [⟨.nat, [0, 1]⟩]
          [.mk [18] [cmp 109 [0, 1] [19] (.builtin .natAdd [18, 14])] (.ret [19]),
           .mk [20] [cmp 110 [0, 1] [21] (.literal (.nat 1))] (.ret [21])]),
        .mk 111 [22, 23] (.repeat [0, 1] (.runtime 0) [(17, [0, 1])] [⟨.nat, [0, 1]⟩]
          (.mk [24, 25]
            [cmp 112 [0, 1] [26] (.builtin .natAdd [25, 24])]
            (.ret [26, 26]))),
        .mk 114 [28] (.apply 0 [1, 0] (site 114 "call") [23]),
        .mk 115 [29] (.block ⟨115, [0]⟩ [⟨.nat, [2]⟩]
          (.mk [] [cmp 116 [2] [30] (.builtin .natAdd [13, 13])] (.ret [30]))),
        cmp 117 [0] [31] (.literal (.nat 3)),
        cmp 118 [1] [32] (.literal (.nat 3)),
        .mk 119 [33] (.join [(31, 0), (32, 1)])]
      (.ret [33, 29, 28]) }

def lawPackage : Named.Package :=
  { emptyPackage with
    protocols := [callee, mainProtocol], protocolNames := ["callee", "main"],
    roleNames := [["A", "B"], ["P", "V", "W"]] }


/-- The tag of the defect that the lowering finds, when it finds one. -/
def defectTag (package : Named.Package) : Option Tag :=
  match lower package with
  | .ok _ => none
  | .error (_, defect) => some defect.tag

/-- Whether a named package is lowered and admitted with the keys of its sites. -/
def admitted (package : Named.Package) : Bool :=
  match lower package with
  | .error _ => false
  | .ok lowered =>
    match admit (fillMaxima lowered.package) { keys := some lowered.keys } with
    | .ok _ => true
    | .error _ => false

#guard admitted lawPackage

-- the sites of the main protocol in the order of its body, and the point of its block
#guard (lower lawPackage).toOption.map (·.keys.map fun keys => keys.map (·.event)) = some [[], [104, 114]]
#guard (lower lawPackage).toOption.map (·.points.map fun points => points.map (·.2.loop)) = some [[], [115]]

-- a `compute` at two roles is one instruction per role, each with the tag and its role
#guard (lower lawPackage).toOption.map
    (fun lowered => (lowered.protocolOrigins.getD 1 []).filterMap fun origin =>
      if origin.tag == 103 then some origin.role else none) = some [some 0, some 1]

/-- A literal named with two results; the second name is read. -/
def twoNames : Named.Function :=
  { specificationOnly := false, inputs := [], outputs := [.nat]
    body := some (.mk [] [.mk 1 [0, 1] (.literal (.nat 5)), .mk 2 [2] (.literal (.nat 6))] (.ret [1])) }


/-- An application named with fewer results than the callee has: the names after it shift. -/
def twoOut : Named.Protocol :=
  { specificationOnly := false, roles := 1, inputs := [], outputs := [⟨.nat, [0]⟩, ⟨.nat, [0]⟩]
    body := .mk []
      [cmp 1 [0] [0] (.literal (.nat 1)), cmp 2 [0] [1] (.literal (.nat 2))]
      (.ret [0, 1]) }

def shortApply : Named.Protocol :=
  { specificationOnly := false, roles := 1, inputs := [], outputs := [⟨.nat, [0]⟩]
    body := .mk []
      [.mk 1 [0] (.apply 0 [0] (site 1 "call") []),
       cmp 2 [0] [1] (.literal (.nat 7))]
      (.ret [1]) }


/-- A name bound twice. -/
def rebound : Named.Function :=
  { specificationOnly := false, inputs := [.nat], outputs := [.nat]
    body := some (.mk [0] [.mk 1 [0] (.literal (.nat 6))] (.ret [0])) }


/-- A name used at a role that does not hold it, inside a choose arm. -/
def notHeld : Named.Protocol :=
  { specificationOnly := false, roles := 2, inputs := [⟨.nat, [0]⟩, ⟨.bool, [0, 1]⟩], outputs := []
    body := .mk [0, 1]
      [.mk 1 [] (.choose [0, 1] 1 .condition []
        [.mk [] [cmp 2 [1] [2] (.builtin .natAdd [0, 0])] (.ret []),
         .mk [] [] (.ret [])])]
      (.ret []) }


#guard defectTag { emptyPackage with functions := [twoNames], functionNames := ["twoNames"] } = some 1
#guard defectTag { emptyPackage with protocols := [twoOut, shortApply]
                                     protocolNames := ["twoOut", "short"], roleNames := [["P"], ["P"]] } = some 1
#guard defectTag { emptyPackage with functions := [rebound], functionNames := ["rebound"] } = some 1
#guard defectTag { emptyPackage with protocols := [notHeld], protocolNames := ["notHeld"]
                                     roleNames := [["P", "V"]] } = some 2

/-- A role map shorter than the callee's roles. -/
def shortMap : Named.Protocol :=
  { specificationOnly := false, roles := 2, inputs := [⟨.nat, [0, 1]⟩], outputs := [⟨.nat, [0, 1]⟩]
    body := .mk [0] [.mk 7 [1] (.apply 0 [0] (site 7 "call") [0])] (.ret [1]) }

#guard defectTag { emptyPackage with protocols := [callee, shortMap]
                                     protocolNames := ["callee", "short"], roleNames := [["A", "B"], ["P", "V"]] } = some 7

/-- An arm of a condition that names an input of its own. -/
def armInput : Named.Function :=
  { specificationOnly := false, inputs := [.bool], outputs := [.nat]
    body := some (.mk [0]
      [.mk 3 [1] (.conditional 0 [.nat]
        (.mk [2] [.mk 4 [3] (.literal (.nat 1))] (.ret [3]))
        (.mk [] [.mk 5 [4] (.literal (.nat 0))] (.ret [4])))]
      (.ret [1])) }

#guard defectTag { emptyPackage with functions := [armInput], functionNames := ["armInput"] } = some 3

end LoweringTests
