"""Exclusive report directories: readable labels, exact identities, no deletion."""

from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile


def new_directory(root, identity, label=None):
    """A new directory under `root` for `identity`, never an existing one.

    The name is a readable label, cut to its most specific end, and a digest of
    the exact identity. `label` replaces the identity as the readable part when
    the identity spells more than a reader needs, such as an absolute path.
    """
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    readable = identity if label is None else label
    label = re.sub(r"[^a-zA-Z0-9.-]+", "-", str(readable)).strip("-.")[-64:] or "case"
    digest = hashlib.sha256(str(identity).encode()).hexdigest()[:12]
    return Path(tempfile.mkdtemp(prefix=f"{label}-{digest}-", dir=root))


@contextmanager
def run_report(root, scope, argv):
    """Retain each run's lifecycle and restore the caller's report selection."""
    output = new_directory(Path(root) / "runs", scope)
    previous = os.environ.get("ZKC_REPORTS_DIR")
    os.environ["ZKC_REPORTS_DIR"] = str(output)
    print(f"Reports: {output}", flush=True)
    record = {"scope": scope, "argv": list(argv), "status": "running",
              "started_utc": datetime.now(timezone.utc).isoformat()}
    manifest = output / "run.json"
    try:
        manifest.write_text(json.dumps(record, indent=2) + "\n")
        yield output
        record["status"] = "pass"
    except BaseException as error:
        record["status"] = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        record["error"] = str(error)
        raise
    finally:
        try:
            record["finished_utc"] = datetime.now(timezone.utc).isoformat()
            manifest.write_text(json.dumps(record, indent=2) + "\n")
        finally:
            if previous is None:
                os.environ.pop("ZKC_REPORTS_DIR", None)
            else:
                os.environ["ZKC_REPORTS_DIR"] = previous
