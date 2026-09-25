# Writing protocols

The `.pir` language describes local algorithms, participant interactions and
reusable protocol libraries. It elaborates into common PIR, where interaction,
resource and operation checks apply independently. Source conveniences such as
nominal records and static components are checked before that boundary.

Start with the [first-run walkthrough](../getting-started.md). Then read the
[source reference](reference.md) beside a maintained
[protocol example](../../examples/protocols/README.md).

| Task | Read |
|---|---|
| Declare roles, local algorithms, messages, challenges and protocol calls | [Source reference](reference.md) |
| Group values and place computation at participants | [Products, local blocks and outputs](values.md) |
| Use records, checked constructors, operators and requirement bundles | [Data forms](data.md) |
| Keep domains and implementations selectable | [Generic definitions](generics.md) and [protocol families](families.md) |
| Specify and implement a reusable component interface | [Checked interfaces and components](components.md) |
| Split libraries and clients into files | [Projects, imports and visibility](projects.md) |
| Consume a compiled circuit or trace relation | [Compiled relations](relations.md) |
| Supply runtime inputs and setup selections | [Local host input format](../runtime/inputs.md) |
| Select an interactive, noninteractive or transcript construction | [Construction notation](reference.md#construction-descriptor) and [construction/execution](../compiler/artifact-execution.md) |

An author controls the mathematical domains and contracts required by a
definition. A backend implementation must satisfy the selected operation
contracts; changing a kernel is different from changing the field or proof
construction. The compiler does not infer cryptographic assumptions from a
function name or a successful type check.

For the meaning beneath the syntax, use the [semantic guides](../guides/README.md).
For retained source analysis, elaboration and lowering APIs, use the
[frontend implementation](../compiler/frontend.md). Current supported routes
and limitations are recorded in [status](../status.md).
