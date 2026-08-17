#!/usr/bin/env python3
"""Point a derivation request at a freshly sealed artifact.

A request pins the artifact it judges, so re-sealing the same protocol
under a different authored event needs the request re-targeted rather
than a second request checked in beside the first. The identity is read
from the artifact directory, where sealing names each file for its own
content.
"""

import json
import sys
from pathlib import Path

request = json.loads(Path(sys.argv[1]).read_text())
sealed = sorted(Path(sys.argv[2]).glob("*.mlirbc"))
if len(sealed) != 1:
    raise SystemExit(f"expected one sealed artifact, found {len(sealed)}")
old = request["derivation"]["target"]["subject"]["artifact_id"]
Path(sys.argv[3]).write_text(json.dumps(request).replace(old, sealed[0].stem))
