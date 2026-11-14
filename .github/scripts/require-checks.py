"""Require every job that the final CI job needs to succeed, also after a failure or cancellation."""

import json
import os
import sys


def failures(needs):
    if not needs:
        return ["No jobs to require"]
    return [f"{name}: {job.get('result', 'missing')}; success required"
            for name, job in sorted(needs.items()) if job.get("result") != "success"]


def main():
    errors = failures(json.loads(os.environ["CI_NEEDS"]))
    for error in errors:
        print(f"::error::{error}")
    if errors:
        return 1
    print("Every required job succeeded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
