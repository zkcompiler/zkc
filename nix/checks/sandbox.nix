{ runCommand, python3 }:
runCommand "zkc-sandbox-check" { nativeBuildInputs = [ python3 ]; } ''
  python3 - <<'PY'
  from pathlib import Path
  import socket

  assert not Path("/tmp/zkc-sandbox-ambient").exists(), "ambient host file is visible"
  interfaces = {name for _, name in socket.if_nameindex()}
  assert interfaces <= {"lo"}, f"host network interfaces are visible: {interfaces}"
  PY
  mkdir -p "$out"
  printf '%s\n' '{"filesystem_isolated":true,"network_isolated":true}' > "$out/result.json"
''
