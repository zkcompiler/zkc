"""Exclusive report directories: readable labels, exact identities, no deletion."""

import hashlib
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
