#!/usr/bin/env python3
"""Time the native application's existing public matrix admission independently."""

import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "execution"))
from verify import check_public_bundle  # noqa: E402

start = time.perf_counter()
run = Path(sys.argv[1])
check_public_bundle(run / "public", run / "public/validator.json")
elapsed = time.perf_counter() - start
repository = Path(__file__).resolve().parents[2]
# Pin actual Python dependencies, including dynamically loaded emitters.
sources = set()
for module in tuple(sys.modules.values()):
    filename = getattr(module, "__file__", None)
    if filename:
        path = Path(filename).resolve()
        if path.suffix == ".py" and path.is_relative_to(repository):
            sources.add(path)
print(
    json.dumps(
        dict(
            admitted=True,
            seconds=elapsed,
            sources_sha256={
                str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(sources)
            },
            scope="existing public matrix/statement/config admission; frozen artifact, no new claim construction",
        )
    )
)
