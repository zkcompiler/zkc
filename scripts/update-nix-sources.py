#!/usr/bin/env python3
"""Hash the revisions already selected by the owning dependency manifests.

This updates Nix transport hashes only. It never chooses a newer revision or
changes a Lake/Cargo/npm lockfile. Run from the repository root in the
maintenance shell; review the resulting JSON diff before building.
"""

import argparse
import concurrent.futures
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

FORMAT = "canonical-git-v1"
NORMALIZER = Path(__file__).resolve().parents[1] / "nix/normalize-git-source.sh"


def fetch(package):
    result = subprocess.run([
        "nix-prefetch-git", "--quiet", "--url", package["url"],
        "--rev", package["rev"], "--leave-dotGit", "--no-deepClone",
    ], check=True, text=True, stdout=subprocess.PIPE)
    data = json.loads(result.stdout)
    with tempfile.TemporaryDirectory(prefix="zkc-git-source-") as directory:
        source = Path(directory) / "source"
        shutil.copytree(data["path"], source, symlinks=True)
        subprocess.run(["chmod", "-R", "u+w", source], check=True)
        subprocess.run(["bash", NORMALIZER, source, package["rev"]], check=True)
        digest = subprocess.check_output(["nix", "hash", "path", source], text=True).strip()
    return package["rev"], {"url": package["url"], "hash": digest, "format": FORMAT}


def update(path, packages, refresh):
    previous = json.loads(path.read_text()) if path.exists() else {}
    result = {p["rev"]: previous[p["rev"]] for p in packages
              if not refresh and previous.get(p["rev"], {}).get("url") == p["url"]
              and previous[p["rev"]].get("format") == FORMAT}
    missing = [p for p in packages if p["rev"] not in result]
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as executor:
        result.update(executor.map(fetch, missing))
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"{path}: {len(result)} source pins ({len(missing)} fetched)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--refresh", action="store_true", help="recompute existing hashes too")
    args = parser.parse_args()
    root = args.root
    packages = {}
    for name in ("formal/lake-manifest.json", "formal/integrations/arklib/lake-manifest.json"):
        for package in json.loads((root / name).read_text())["packages"]:
            if package["type"] == "git":
                packages[package["rev"]] = package
    update(root / "nix/lake-sources.json", list(packages.values()), args.refresh)
    groth16 = json.loads((root / "tests/groth16/SOURCE_PINS.json").read_text())
    llzk = json.loads((root / "compiler/adapters/llzk/pins.json").read_text())
    external = [{"url": groth16[name]["repository"], "rev": groth16[name]["commit"]}
                for name in ("circom", "circomlib")]
    external.extend({"url": llzk[name]["url"], "rev": llzk[name]["revision"]}
                    for name in ("llzk-current", "llzk-circom-locked"))
    update(root / "nix/external-sources.json", external, args.refresh)


if __name__ == "__main__":
    main()
