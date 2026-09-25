#!/usr/bin/env python3
"""Time retained caller requirements against the actual physical candidate."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

# Arguments deliberately match claim-check-lowering, including physical options.
(
    compiler,
    source,
    contract,
    certificate,
    descriptor,
    construction,
    physical,
    *options,
) = sys.argv[1:]
paths = [compiler, source, contract, certificate, descriptor, construction, physical]
paths += [o.split("=", 1)[1] for o in options if o.startswith("--implementations=")]


def pins():
    return {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths}


before = pins()
start = time.perf_counter()
result = subprocess.run(
    [
        compiler,
        "claim-check-lowering",
        source,
        contract,
        certificate,
        descriptor,
        construction,
        physical,
        *options,
    ],
    capture_output=True,
    text=True,
    check=False,
)
seconds = time.perf_counter() - start
assert before == pins(), (
    "claim authority or measured candidate changed during admission"
)
print(
    json.dumps(
        dict(
            admitted=result.returncode == 0,
            seconds=seconds,
            sources_sha256=before,
            diagnostic=(result.stdout + result.stderr).strip(),
            scope="retained caller contract and actual selected candidate; trusted pipeline recomputation",
        )
    )
)
raise SystemExit(0 if result.returncode == 0 else 1)
