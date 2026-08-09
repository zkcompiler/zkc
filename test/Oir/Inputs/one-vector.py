#!/usr/bin/env python3
"""Emit a one-vector file binding the artifact's single statement label.

The artifact identity and citation are read out of the endpoint rather than
written down, so this fixture survives a re-mint untouched.
"""

import json
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
artifact = re.search(r'oir\.artifact "[^"]*" id "([0-9a-f]{64})"', text)
source = re.search(r'source "(sha256:[0-9a-f]{64})"', text)
if not (artifact and source):
    raise SystemExit("artifact id or source citation not found")
# An endpoint with no public statement prints no `statement_labels` at all,
# which is a bindingless vector rather than a malformed artifact.
labels = re.search(r'statement_labels = \[([^\]]*)\]', text)
names = re.findall(r'"([^"]+)"', labels.group(1)) if labels else []
if len(names) > 1:
    raise SystemExit(f"expected at most one statement label, found {names}")
statement = {names[0]: sys.argv[2]} if names else {}
json.dump({"artifact_id": artifact.group(1), "source": source.group(1),
           "vectors": [{"challenges": [], "expect": "accept", "name": "probe",
                        "proof": "", "statement": statement}]},
          sys.stdout)
