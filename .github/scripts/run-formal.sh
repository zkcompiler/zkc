#!/usr/bin/env bash
# Run inside the verified CI service with the pinned Nix tools on PATH.
set -euo pipefail
toolchain=$(cat lean/formal/lean-toolchain)
cmp lean/compiler/lean-toolchain lean/formal/lean-toolchain
export ELAN_HOME="$RUNNER_TEMP/zkc-elan"
export XDG_CACHE_HOME="$RUNNER_TEMP/zkc-cache"
export LEAN_NUM_THREADS=4
export MATHLIB_NO_CACHE_ON_UPDATE=1
elan run --install "$toolchain" lean --version
lean_bin=$(cd lean/formal && elan which lean)
export PATH="${lean_bin%/*}:$PATH"

# Obtain just the Mathlib imports of the public proof roots on a cold run.
# Lake still builds/checks the project itself in this checkout.
case " $* " in
  *" test-formal "*|*" test-written-charge "*)
    (
      cd lean/formal
      imports="$RUNNER_TEMP/formal-imports"
      lake -q query +Zkc.Formal:transImports +Zkc.Tools.Formal.DrawCharge:transImports > "$imports"
      mapfile -t modules < <(awk '/^Mathlib\./' "$imports" | sort -u)
      (( ${#modules[@]} > 0 ))
      missing=()
      for module in "${modules[@]}"; do
        if [[ ! -f ".lake/packages/mathlib/.lake/build/lib/lean/${module//./\/}.olean" ]]; then
          missing+=("$module")
        fi
      done
      if (( ${#missing[@]} )); then
        lake exe cache get "${missing[@]}"
      fi
    )
    ;;
esac
just "$@"
