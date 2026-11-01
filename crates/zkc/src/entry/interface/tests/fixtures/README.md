# Interface consumer fixtures

`fri-interface.json` is actual compiler output from the maintained FRI project,
including its seven retained Protocols, Commit/Query state schemas, exact
placement/component maps and required common-input inventories. The producer
checks the independently parsed original and source correspondence before
publishing it. This is a native interface receipt, not FRI proof execution or
formal coverage. Private state fields remain private in the emitted schema.

Regenerate from the repository root after rebuilding `zkc-compile`:

```sh
python3 - <<'PYTHON'
import subprocess
import sys
from pathlib import Path
sys.path.insert(0, 'common/tests/support')
from project import project_arguments
command = ['build/compiler/zkc-compile', 'language-interface',
           '--source-format=zkc', '--entry=example::Proof',
           *project_arguments(Path('examples/projects/fri/zkc.toml'))]
result = subprocess.run(command, check=True, capture_output=True)
Path('crates/zkc/src/entry/interface/tests/fixtures/fri-interface.json').write_bytes(result.stdout)
PYTHON
```

Current SHA-256: `41063ffc2b19712871ee41b94b0b12e893dd90494e01f157b9fb6871f1eca757`.
This digest covers the exact retained fixture; its embedded original and
compiler identities bind different inputs and are not source proofs.

`recursive-interface.json` is an independently authored current-schema positive
specimen for shared reader integration. It has nested ordered role substitution,
two distinct holders, one receiver, an ordinary verifier-local child, and a
private zero-storage child. The Rust reader checks its exact component coordinates
and the mutation tests use the same schema. The C++ owner must pair it with an
admitted native candidate and run the independent reader; that integration is a
separate outstanding gate. Its nominal digest placeholders bind fixture names,
not an authenticated source declaration.

The recursive specimen explicitly retains `common_input_requirements: []`
for every Protocol. This establishes strict SDK schema consumption, not newly
derived source coverage or fresh compiler/native pairing.
