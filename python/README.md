# Python SDK

Install with `python3 -m pip install ./python`. The installed `zkc` executable
owns compilation, admission and execution; this package is a process adapter.

```python
from zkc import Client

project = Client("examples/projects/fibonacci/zkc.toml")
signature = project.inspect("GenerateTrace").require_success().value
result = project.run({"initial_x": "0", "initial_y": "1"}, entry="GenerateTrace")
trace = result.require_success().value
```

Arguments and results follow `zkc inspect` and `zkc prepare`. `run` arguments and
`prove`/`verify` public or witness inputs accept either a mapping or a JSON file
path. Pass a file path for wire-file references or prover-key material: the Host
resolves references relative to that document with its normal confinement checks.
Mappings are written to temporary documents and are intended for inline values. Pass native wire
values in that schema. `Client.prove` returns exact candidate proof bytes;
`Client.verify` takes those bytes and independently supplied public inputs.
`Execution.report` retains native diagnostics on success or failure. Failed
execution publishes no source value. A source `Rejected` result is ordinary data.

Use `Client(package=path, sha256=trusted_pin)` for pinned deployment. Services,
setup authority and limits use the same explicit options as the CLI. Calls start
fresh processes; the Rust SDK also supports retaining admitted Hosts for reuse.
