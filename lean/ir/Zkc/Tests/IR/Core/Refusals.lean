import Zkc.Tools.IR.Core.Import

/-! Refusals of the `zkc.core/0` importer and of the kernel.

Each control imports an ill-formed package and checks the cause of the refusal.
Malformed or unsupported input and dangling references have no term and are refused
by the importer. Every other rule is refused twice: by the importer, with its own
message, and, with `kernel_only`, by the kernel alone. The importer then reports
what the kernel decided: `typing`, with the kernel's own account of the ill-typed
application, or `residual condition` with the name that the kernel evaluates
`Definition.violation` to. A refusal leaves the environment unchanged: each control
checks that the refused command added no declaration, also when an earlier
definition of the package was accepted. -/

namespace Zkc.Tests.Core.Refusals

open Lean Elab Command in
/-- Elaborate a command that must fail with one error containing every `expected`
fragment; keep nothing it adds. Resource exhaustion is not a refusal. -/
elab "expect_core_refusal " expected:str+ " in " command:command : command => do
  let saved ← get
  modify fun state => { state with messages := {} }
  elabCommand command
  let messages := (← get).messages.toList
  let declarations (env : Environment) : Nat := env.constants.map₂.foldl (fun count _ _ => count + 1) 0
  let added := declarations (← getEnv) - declarations saved.env
  set saved
  unless added == 0 do
    throwError "the refused command left {added} declarations in the environment"
  let errors ← messages.filterMapM fun message => do
    if message.severity == .error then return some (← message.data.toString) else return none
  let fragments := expected.toList.map (·.getString)
  if errors.isEmpty then
    throwError "expected a refusal: {fragments}"
  for limit in ["maximum number of heartbeats", "deterministic timeout", "maximum recursion depth",
      "deep recursion"] do
    if errors.any (fun text => (text.splitOn limit).length > 1) then
      throwError "resource exhaustion is not a refusal: {errors}"
  unless errors.any (fun text => fragments.all fun fragment => (text.splitOn fragment).length > 1) do
    throwError "wrong refusal: expected {fragments}, got {errors}"

/-! The accepted baseline: role 0 doubles a field element and sends it to role 1. -/

import_core baseline from r#"["zkc.core/0", [["original", [["field", [["domain", "scalar"]]]], [],
  [["law.uniform", [["type", ["nominal", 0]]], "sampling", [], [["nominal", 0]]],
   ["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
  [["protocol", 0, 2, [[["nominal", 0], 0], ["index", 1]], [[["nominal", 0], 1]], [],
    [[["at", 0, ["op", 1, [0, 0]]], ["exchange", 0, 1, 0, 2]], [3]]]]]], [], [], [], []]"#

/-! ## Malformed and unsupported input: refused by the importer -/

expect_core_refusal "malformed JSON" in
import_core malformed from r#"["zkc.core/0", [["original""#

expect_core_refusal "unknown stage batched" in
import_core batched from r#"["zkc.core/0", [["batched", [], [], [], []]], [], [], [], []]"#

expect_core_refusal "unknown format" in
import_core format from r#"["zkc.core/1", [["original", [], [], [], []]], [], [], [], []]"#

expect_core_refusal "oracle rows are not supported" in
import_core oracles from
  r#"["zkc.core/0", [["original", [], [["index", "index", ["sent"]]], [], []]],
  [], [], [], []]"#

expect_core_refusal "match is not supported" in
import_core matching from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 0, ["bool"], [], [[["match", 0, [], []]], []]]]]], [], [], [], []]"#

expect_core_refusal "oracle_read is not supported" in
import_core reading from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[["oracle_read", 0, 0, []]], []]]]]], [], [], [], []]"#

/-! The shape of catalogue rows, static arguments and the names table. -/

expect_core_refusal "domain: expected a string, found 5" in
import_core staticShape from r#"["zkc.core/0", [["original", [["field", [["domain", 5]]]], [],
  [],
  []]], [], [], [], []]"#

expect_core_refusal "malformed static argument [\"size\",5]" in
import_core staticKind from r#"["zkc.core/0", [["original", [], [],
  [["index.constant", [["size", 5]], "pure", [], ["index"]]],
  []]], [], [], [], []]"#

expect_core_refusal "static arguments: expected an array" in
import_core staticList from r#"["zkc.core/0", [["original", [["field", "scalar"]], [],
  [],
  []]], [], [], [], []]"#

expect_core_refusal "uses a character other than letters, digits and . _ - /" in
import_core catalogueName from r#"["zkc.core/0", [["original", [], [],
  [["index add", [], "pure", ["index", "index"], ["index"]]],
  []]], [], [], [], []]"#

expect_core_refusal "dangling reference: nominal type row 1" in
import_core laterType from
  r#"["zkc.core/0", [["original", [["vector", [["type", ["nominal", 1]]]], ["field", [["domain", "scalar"]]]], [],
  [],
  []]], [], [], [], []]"#

expect_core_refusal "operation rows 0 and 1 have one catalogue identity, index.constant(nat 1)" in
import_core sameIdentity from r#"["zkc.core/0", [["original", [], [],
  [["index.constant", [["nat", 1]], "pure", [], ["index"]],
   ["index.constant", [["nat", 1]], "pure", [], ["index"]]],
  []]], [], [], [], []]"#

expect_core_refusal "a sampling law has exactly one output, found 2" in
import_core lawOutputs from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index", "index"]]],
  []]], [], [], [], []]"#

expect_core_refusal "expected no table or three tables" in
import_core oneNameTable from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[], []]]]]], [], [], [], [["only"]]]"#

expect_core_refusal "definition names: 2 entries for 1 definitions" in
import_core definitionNames from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[], []]]]]], [], [], [], [["one", "two"], [[]], [[]]]]"#

expect_core_refusal "role names: 2 names for the 1 roles of definition 0" in
import_core roleNames from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[], []]]]]], [], [], [], [["one"], [["left", "right"]], [[]]]]"#

expect_core_refusal "site names: 2 names for 1 sites" in
import_core siteNames from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [], [[["exchange", 0, 1, 0, 0]], []]]]]], [], [], [], [["one"], [[]], [["first", "second"]]]]"#

expect_core_refusal "two definitions would be named twin" in
import_core sameName from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 0, [], [], [[], []]], ["function", 0, [], [], [[], []]]]]], [], [], [], [["twin", "twin"], [[], []], [[], []]]]"#

expect_core_refusal "the definition name row is reserved" in
import_core reservedName from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 0, [], [], [[], []]]]]], [], [], [], [["row"], [[]], [[]]]]"#

/-! Constructs without a term: a guard cannot name the reserved reason, a role
performs no `stop`, and an agreement names a port. -/

expect_core_refusal "a guard names an authored reason; incomplete is reserved" in
import_core guardReason from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["bool", 0]], [], [], [[["at", 0, ["guard", "incomplete", 0]]], []]]]]], [], [], [], []]"#

expect_core_refusal "a guard names an authored reason; incomplete is reserved" in
import_core functionGuardReason from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 0, ["bool"], [], [[["guard", "incomplete", 0]], []]]]]], [], [], [], []]"#

expect_core_refusal "stop is not an operation that a role performs" in
import_core roleStop from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[["at", 0, ["stop", "reject"]]], []]]]]], [], [], [], []]"#

expect_core_refusal "an agreement names at least one port" in
import_core emptyAgreement from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 1]], [], [[0, []]], [[], []]]]]], [], [], [], []]"#

/-! ## Dangling references: no term exists -/

expect_core_refusal "dangling reference: value 7" in
import_core danglingValue from
  r#"["zkc.core/0", [["original", [["field", [["domain", "scalar"]]]], [],
  [["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
  [["protocol", 0, 2, [[["nominal", 0], 0]], [[["nominal", 0], 1]], [],
    [[["exchange", 0, 1, 0, 7]], [1]]]]]], [], [], [], []]"#

expect_core_refusal "dangling reference: definition 3" in
import_core danglingDefinition from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[], []]],
   ["protocol", 0, 1, [], [], [], [[["apply", 3, [0], 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "dangling reference: operation row 4" in
import_core danglingRow from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 0, [], [], [[["op", 4, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "dangling reference: nominal type row 2" in
import_core danglingType from
  r#"["zkc.core/0", [["original", [["field", [["domain", "scalar"]]]], [],
  [],
  [["function", 0, [["nominal", 2]], [], [[], []]]]]], [], [], [], []]"#

expect_core_refusal "dangling reference: port 5" in
import_core danglingPort from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 1]], [], [[0, [0, 5]]], [[], []]]]]], [], [], [], []]"#

/-! ## Typing: refused by the importer, and by the kernel's type checker alone -/

-- Role 1 computes with a value that role 0 holds: the operands do not have the
-- located types that the operation requires.
expect_core_refusal "wrong holder: operand 0 (value 0) is held by role 0, expected role 1" in
import_core holder from r#"["zkc.core/0", [["original", [["field", [["domain", "scalar"]]]], [],
  [["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
  [["protocol", 0, 2, [[["nominal", 0], 0], ["index", 1]], [[["nominal", 0], 1]], [],
    [[["at", 1, ["op", 0, [0, 0]]]], [2]]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "application type mismatch" "Region.letOp"
    "ProtocolOp.at 1 (" "Operands" in
import_core holderKernel with kernel_only from
  r#"["zkc.core/0", [["original", [["field", [["domain", "scalar"]]]], [],
  [["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
  [["protocol", 0, 2, [[["nominal", 0], 0], ["index", 1]], [[["nominal", 0], 1]], [],
    [[["at", 1, ["op", 0, [0, 0]]]], [2]]]]]], [], [], [], []]"#

expect_core_refusal "wrong type: operand 1 (value 1) has type index, expected nominal(0)" in
import_core type from r#"["zkc.core/0", [["original", [["field", [["domain", "scalar"]]]], [],
  [["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
  [["protocol", 0, 1, [[["nominal", 0], 0], ["index", 0]], [[["nominal", 0], 0]], [],
    [[["at", 0, ["op", 0, [0, 1]]]], [2]]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "application type mismatch" "Region.letOp"
    "ProtocolOp.at 0 (" "Operands" in
import_core typeKernel with kernel_only from
  r#"["zkc.core/0", [["original", [["field", [["domain", "scalar"]]]], [],
  [["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
  [["protocol", 0, 1, [[["nominal", 0], 0], ["index", 0]], [[["nominal", 0], 0]], [],
    [[["at", 0, ["op", 0, [0, 1]]]], [2]]]]]], [], [], [], []]"#

-- A deployed protocol applies a specification-only protocol.
expect_core_refusal "uses the specification-only definition 0" in
import_core specification from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 1, 1, [], [], [], [[], []]],
   ["protocol", 0, 1, [], [], [], [[["apply", 0, [0], 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "ProtocolOp.apply" "(true && true) = false" in
import_core specificationKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 1, 1, [], [], [], [[], []]],
   ["protocol", 0, 1, [], [], [], [[["apply", 0, [0], 0, []]], []]]]]], [], [], [], []]"#

-- A deployed function calls a specification-only function.
expect_core_refusal "uses the specification-only definition 0" in
import_core specificationCall from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 1, [], [], [[], []]],
   ["function", 0, [], [], [[["call", 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "LocalOp.call" "(true && true) = false" in
import_core specificationCallKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 1, [], [], [[], []]],
   ["function", 0, [], [], [[["call", 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "is a sampling law, not an operation" in
import_core samplingOperation from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["function", 0, [], ["index"], [[["op", 0, []]], [0]]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "OperationKind.sampling.computes = true" in
import_core samplingOperationKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["function", 0, [], ["index"], [[["op", 0, []]], [0]]]]]], [], [], [], []]"#

expect_core_refusal "is pure, not a sampling law" in
import_core pureLaw from r#"["zkc.core/0", [["original", [], [],
  [["index.constant", [["nat", 1]], "pure", [], ["index"]]],
  [["protocol", 0, 2, [], [], [], [[["draw", 0, [1], 0, 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "ProtocolOp.draw" "OperationKind.pure }" in
import_core pureLawKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [["index.constant", [["nat", 1]], "pure", [], ["index"]]],
  [["protocol", 0, 2, [], [], [], [[["draw", 0, [1], 0, 0, []]], []]]]]], [], [], [], []]"#

-- A branch whose output is held by a role that is not a participant. The kernel
-- refuses the typed proof that participants hold the outputs.
expect_core_refusal
    "a value that enters or leaves a repeat or branch is held by a role that is not a participant" in
import_core branchOutput from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["index", 1]], [["index", 1]], [],
    [[["branch", [[0, 0]], [1], [[], [0]], [[], [0]]]], [2]]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "Located.heldBy [0]" in
import_core branchOutputKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["index", 1]], [["index", 1]], [],
    [[["branch", [[0, 0]], [1], [[], [0]], [[], [0]]]], [2]]]]]], [], [], [], []]"#

-- An agreement over ports of two types.
expect_core_refusal "wrong type: an agreement names ports of types bool and index" in
import_core agreementType from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["index", 1]], [], [[0, [0, 1]]], [[], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "typing" "Copy [" in
import_core agreementTypeKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["index", 1]], [], [[0, [0, 1]]], [[], []]]]]], [], [], [], []]"#

/-! ## Residual conditions: refused by the importer, and decided by the kernel

The importer and the kernel evaluate the same condition lists of the model; the
kernel's verdict is the name of the violated condition. -/

/-! Roles. -/

expect_core_refusal "a protocol has no role" in
import_core noRole from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 0, [], [], [], [[], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition noRole" "a protocol has no role" in
import_core noRoleKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 0, [], [], [], [[], []]]]]], [], [], [], []]"#

-- The receiver of an exchange is not a role.
expect_core_refusal "a role is not below the role count" in
import_core range from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [], [[["exchange", 0, 2, 0, 0]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleOutOfRange"
    "a role is not below the role count" in
import_core rangeKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [], [[["exchange", 0, 2, 0, 0]], []]]]]], [], [], [], []]"#

-- The holder of a port is not a role.
expect_core_refusal "a role is not below the role count" in
import_core portRange from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["index", 1]], [], [], [[], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleOutOfRange"
    "a role is not below the role count" in
import_core portRangeKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["index", 1]], [], [], [[], []]]]]], [], [], [], []]"#

-- An entry of a role map is not a role.
expect_core_refusal "a role is not below the role count" in
import_core roleMapRange from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[], []]],
   ["protocol", 0, 2, [], [], [], [[["apply", 0, [2], 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleOutOfRange"
    "a role is not below the role count" in
import_core roleMapRangeKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[], []]],
   ["protocol", 0, 2, [], [], [], [[["apply", 0, [2], 0, []]], []]]]]], [], [], [], []]"#

/-! Participants. -/

expect_core_refusal "a repeat or branch has no participant" in
import_core noParticipant from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[["repeat", [], 4, [], [], [[], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition noParticipant"
    "a repeat or branch has no participant" in
import_core noParticipantKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[["repeat", [], 4, [], [], [[], []]]], []]]]]], [], [], [], []]"#

-- A repeat lists role 0 twice, with two counts.
expect_core_refusal "a repeat or branch lists a participant twice" in
import_core repeatedParticipant from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["index", 0], ["index", 0]], [], [],
    [[["repeat", [[0, 0], [0, 1]], 4, [], [], [[], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition repeatedParticipant"
    "a repeat or branch lists a participant twice" in
import_core repeatedParticipantKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["index", 0], ["index", 0]], [], [],
    [[["repeat", [[0, 0], [0, 1]], 4, [], [], [[], []]]], []]]]]], [], [], [], []]"#

-- A branch lists role 0 twice, with two conditions.
expect_core_refusal "a repeat or branch lists a participant twice" in
import_core repeatedBranchParticipant from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["bool", 0], ["bool", 0]], [], [],
    [[["branch", [[0, 0], [0, 1]], [], [[], []], [[], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition repeatedParticipant"
    "a repeat or branch lists a participant twice" in
import_core repeatedBranchParticipantKernel with kernel_only from
  r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["bool", 0], ["bool", 0]], [], [],
    [[["branch", [[0, 0], [0, 1]], [], [[], []], [[], []]]], []]]]]], [], [], [], []]"#

-- The owner of a draw inside a repeat is not a participant.
expect_core_refusal
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core coverage from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 2, [["index", 1]], [], [],
    [[["repeat", [[1, 0]], 4, [], [], [[["draw", 0, [1], 0, 0, []]], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleOutsideParticipants"
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core coverageKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 2, [["index", 1]], [], [],
    [[["repeat", [[1, 0]], 4, [], [], [[["draw", 0, [1], 0, 0, []]], []]]], []]]]]], [], [], [], []]"#

-- A receiver of a draw inside a repeat is not a participant.
expect_core_refusal
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core receiverCoverage from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["repeat", [[0, 0]], 4, [], [], [[["draw", 0, [1], 0, 0, []]], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleOutsideParticipants"
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core receiverCoverageKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["repeat", [[0, 0]], 4, [], [], [[["draw", 0, [1], 0, 0, []]], []]]], []]]]]], [], [], [], []]"#

-- The receiver of an exchange inside a branch is not a participant.
expect_core_refusal
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core exchangeCoverage from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["index", 0]], [], [],
    [[["branch", [[0, 0]], [1], [[["exchange", 0, 1, 0, 0]], []], [[], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleOutsideParticipants"
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core exchangeCoverageKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["index", 0]], [], [],
    [[["branch", [[0, 0]], [1], [[["exchange", 0, 1, 0, 0]], []], [[], []]]], []]]]]], [], [], [], []]"#

-- An entry of a role map inside a repeat is not a participant.
expect_core_refusal
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core applyCoverage from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [], [], [], [[], []]],
   ["protocol", 0, 2, [["index", 0]], [], [],
    [[["repeat", [[0, 0]], 4, [], [], [[["apply", 0, [0, 1], 0, []]], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleOutsideParticipants"
    "an operation inside a repeat or branch names a role that is not a participant" in
import_core applyCoverageKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [], [], [], [[], []]],
   ["protocol", 0, 2, [["index", 0]], [], [],
    [[["repeat", [[0, 0]], 4, [], [], [[["apply", 0, [0, 1], 0, []]], []]]], []]]]]], [], [], [], []]"#

-- A carried value of a repeat is held by a role that is not a participant.
expect_core_refusal
    "a value that enters or leaves a repeat or branch is held by a role that is not a participant" in
import_core carriedCoverage from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 1]], [], [],
    [[["repeat", [[0, 0]], 4, [1], [], [[], [0]]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition valueOutsideParticipants"
    "a value that enters or leaves a repeat or branch is held by a role that is not a participant" in
import_core carriedCoverageKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 1]], [], [],
    [[["repeat", [[0, 0]], 4, [1], [], [[], [0]]]], []]]]]], [], [], [], []]"#

/-! Exchanges, draws and role maps. -/

expect_core_refusal "the sender of an exchange is its receiver" in
import_core selfExchange from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [], [[["exchange", 0, 0, 0, 0]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition exchangeToSelf"
    "the sender of an exchange is its receiver" in
import_core selfExchangeKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [], [[["exchange", 0, 0, 0, 0]], []]]]]], [], [], [], []]"#

expect_core_refusal "the receivers of a draw do not increase strictly" in
import_core receiversDecrease from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 3, [], [], [], [[["draw", 0, [2, 1], 0, 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition receiversNotIncreasing"
    "the receivers of a draw do not increase strictly" in
import_core receiversDecreaseKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 3, [], [], [], [[["draw", 0, [2, 1], 0, 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the receivers of a draw do not increase strictly" in
import_core receiversRepeat from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 3, [], [], [], [[["draw", 0, [1, 1], 0, 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition receiversNotIncreasing"
    "the receivers of a draw do not increase strictly" in
import_core receiversRepeatKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 3, [], [], [], [[["draw", 0, [1, 1], 0, 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the owner of a draw is one of its receivers" in
import_core ownerReceives from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 2, [], [], [], [[["draw", 0, [0, 1], 0, 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition ownerReceives"
    "the owner of a draw is one of its receivers" in
import_core ownerReceivesKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [["law.uniform_below", [["nat", 4]], "sampling", [], ["index"]]],
  [["protocol", 0, 2, [], [], [], [[["draw", 0, [0, 1], 0, 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "a role map does not have one entry per formal role" in
import_core roleMapLength from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [], [], [], [[], []]],
   ["protocol", 0, 2, [], [], [], [[["apply", 0, [0], 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleMapLength"
    "a role map does not have one entry per formal role" in
import_core roleMapLengthKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [], [], [], [[], []]],
   ["protocol", 0, 2, [], [], [], [[["apply", 0, [0], 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "a role map sends two formal roles to one role" in
import_core injective from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [], [], [], [[], []]],
   ["protocol", 0, 2, [], [], [], [[["apply", 0, [0, 0], 0, []]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition roleMapNotInjective"
    "a role map sends two formal roles to one role" in
import_core injectiveKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [], [], [], [[], []]],
   ["protocol", 0, 2, [], [], [], [[["apply", 0, [0, 0], 0, []]], []]]]]], [], [], [], []]"#

/-! Sites: `0 … k−1`, each once, in whatever regions and branch arms they occur. -/

expect_core_refusal "two operations of a definition share a site" in
import_core sites from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["exchange", 0, 1, 0, 0], ["exchange", 0, 1, 0, 0]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition repeatedSite"
    "two operations of a definition share a site" in
import_core sitesKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["exchange", 0, 1, 0, 0], ["exchange", 0, 1, 0, 0]], []]]]]], [], [], [], []]"#

-- A site of a nested region is a site of the enclosing one.
expect_core_refusal "two operations of a definition share a site" in
import_core nestedSites from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 1]], [], [],
    [[["exchange", 0, 1, 0, 0],
      ["repeat", [[0, 0], [1, 1]], 4, [], [0], [[["exchange", 0, 1, 0, 0]], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition repeatedSite"
    "two operations of a definition share a site" in
import_core nestedSitesKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 1]], [], [],
    [[["exchange", 0, 1, 0, 0],
      ["repeat", [[0, 0], [1, 1]], 4, [], [0], [[["exchange", 0, 1, 0, 0]], []]]], []]]]]], [], [], [], []]"#

-- The two arms of a branch use one site.
expect_core_refusal "two operations of a definition share a site" in
import_core armSites from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["bool", 1], ["index", 0]], [], [],
    [[["branch", [[0, 0], [1, 1]], [2],
       [[["exchange", 0, 1, 0, 0]], []], [[["exchange", 0, 1, 0, 0]], []]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition repeatedSite"
    "two operations of a definition share a site" in
import_core armSitesKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["bool", 0], ["bool", 1], ["index", 0]], [], [],
    [[["branch", [[0, 0], [1, 1]], [2],
       [[["exchange", 0, 1, 0, 0]], []], [[["exchange", 0, 1, 0, 0]], []]]], []]]]]], [], [], [], []]"#

-- Sites 0 and 2 of two: site 1 is missing.
expect_core_refusal "the sites of a definition are not numbered from 0 without gaps" in
import_core siteGap from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["exchange", 0, 1, 0, 0], ["exchange", 0, 1, 2, 0]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition siteGap"
    "the sites of a definition are not numbered from 0 without gaps" in
import_core siteGapKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["exchange", 0, 1, 0, 0], ["exchange", 0, 1, 2, 0]], []]]]]], [], [], [], []]"#

-- A large site number is refused by comparison; no numeral of that size is built.
expect_core_refusal "the sites of a definition are not numbered from 0 without gaps" in
import_core largeSite from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["exchange", 0, 1, 1073741824, 0], ["exchange", 0, 1, 0, 0]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition siteGap"
    "the sites of a definition are not numbered from 0 without gaps" in
import_core largeSiteKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0]], [], [],
    [[["exchange", 0, 1, 1073741824, 0], ["exchange", 0, 1, 0, 0]], []]]]]], [], [], [], []]"#

/-! Stops. -/

expect_core_refusal "a protocol region contains a stop" in
import_core protocolStop from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[["stop", "reject"]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition protocolStop"
    "a protocol region contains a stop" in
import_core protocolStopKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [], [], [], [[["stop", "reject"]], []]]]]], [], [], [], []]"#

expect_core_refusal "a stop names the reserved reason incomplete" in
import_core incomplete from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 0, [], [], [[["stop", "incomplete"]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition reservedReason"
    "a stop names the reserved reason incomplete" in
import_core incompleteKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["function", 0, [], [], [[["stop", "incomplete"]], []]]]]], [], [], [], []]"#

-- A `stop` with the reserved reason in a local region that a role performs.
expect_core_refusal "a stop names the reserved reason incomplete" in
import_core nestedIncomplete from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["bool", 0]], [], [],
    [[["at", 0, ["if", 0, [], [[["stop", "incomplete"]], []], [[], []]]]], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition reservedReason"
    "a stop names the reserved reason incomplete" in
import_core nestedIncompleteKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 1, [["bool", 0]], [], [],
    [[["at", 0, ["if", 0, [], [[["stop", "incomplete"]], []], [[], []]]]], []]]]]], [], [], [], []]"#

/-! Agreements. -/

-- Two copies held by role 0.
expect_core_refusal "two copies of an agreement have one holder" in
import_core agreementHolders from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 0]], [], [[0, [0, 1]]], [[], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition agreementHolders"
    "two copies of an agreement have one holder" in
import_core agreementHoldersKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 0], ["index", 0]], [], [[0, [0, 1]]], [[], []]]]]], [], [], [], []]"#

-- Input 0 is named by two agreements.
expect_core_refusal "the agreements of a signature name a port twice" in
import_core agreementPorts from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 3, [["index", 0], ["index", 1], ["index", 2]], [],
    [[0, [0, 1]], [0, [0, 2]]], [[], []]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition agreementPorts"
    "the agreements of a signature name a port twice" in
import_core agreementPortsKernel with kernel_only from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 3, [["index", 0], ["index", 1], ["index", 2]], [],
    [[0, [0, 1]], [0, [0, 2]]], [[], []]]]]], [], [], [], []]"#

-- Two output copies held by role 1.
expect_core_refusal "two copies of an agreement have one holder" in
import_core outputAgreementHolders from r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 1], ["index", 1]], [["index", 1], ["index", 1]], [[1, [0, 1]]],
    [[], [0, 1]]]]]], [], [], [], []]"#

expect_core_refusal "the kernel refused" "residual condition agreementHolders"
    "two copies of an agreement have one holder" in
import_core outputAgreementHoldersKernel with kernel_only from
  r#"["zkc.core/0", [["original", [], [],
  [],
  [["protocol", 0, 2, [["index", 1], ["index", 1]], [["index", 1], ["index", 1]], [[1, [0, 1]]],
    [[], [0, 1]]]]]], [], [], [], []]"#


/-! ## Accepted neighbours of the refused packages -/

-- Distinct participants, dense sites across a nested region and the arms of a
-- branch, an agreement with different holders, and a stop with an authored reason.
import_core accepted from r#"["zkc.core/0", [["original", [], [], [],
  [["function", 0, ["bool"], [], [[["if", 0, [], [[["stop", "reject"]], []], [[], []]]], []]],
   ["protocol", 0, 2, [["bool", 0], ["bool", 1], ["index", 0], ["index", 1]], [],
    [[0, [0, 1]], [0, [2, 3]]],
    [[["exchange", 0, 1, 2, 2],
      ["branch", [[0, 0], [1, 1]], [2],
       [[["exchange", 0, 1, 0, 0]], []], [[["exchange", 0, 1, 1, 0]], []]],
      ["repeat", [[0, 2], [1, 3]], 4, [], [2], [[["exchange", 0, 1, 3, 0]], []]]], []]]]]],
  [], [], [], []]"#

-- The accepted packages are in the environment with their generated declarations.
open Lean in
run_cmd do
  for name in [`baseline.catalogue, `baseline.operations, `baseline.row.«field.add(domain scalar)»,
      `baseline.definition0.definition, `baseline.definition0.wellFormed, `baseline.definition0,
      `baseline.definition0.table, `accepted.definition1] do
    unless (← getEnv).contains name do throwError "an accepted declaration is missing: {name}"

end Zkc.Tests.Core.Refusals
