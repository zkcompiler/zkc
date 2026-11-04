"""Require successful selected CI jobs, including after failure or cancellation."""

import json
import os
import sys


def failures(needs, event, scope):
    if event in {"pull_request", "push"}:
        expected = {"quick", "native"}
    elif event == "workflow_dispatch":
        scopes = {
            "quick": {"quick"},
            "main": {"main"},
            "optional": {"optional"},
            "fresh": {"fresh"},
            "cache": {"main"},
            "all": {"quick", "main", "optional", "fresh"},
        }
        if scope not in scopes:
            return [f"Unknown workflow scope: {scope!r}"]
        expected = scopes[scope]
    else:
        return [f"Unsupported workflow event: {event!r}"]
    errors = []
    for name in sorted(expected):
        result = needs.get(name, {}).get("result", "missing")
        if result != "success":
            errors.append(f"{name}: {result}; success required")
    for name, job in needs.items():
        if name not in expected and job.get("result") not in {"skipped", "success"}:
            errors.append(f"{name}: unexpected {job.get('result', 'missing')}")
    return errors


def main():
    errors = failures(json.loads(os.environ["CI_NEEDS"]),
                      os.environ["CI_EVENT"], os.environ.get("CI_SCOPE", ""))
    for error in errors:
        print(f"::error::{error}")
    if errors:
        return 1
    print("All required jobs for this event and scope succeeded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
