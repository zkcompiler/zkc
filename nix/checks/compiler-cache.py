"""Exercise real cache hits and source/header/flag invalidation in the CI sandbox."""

from collections import Counter
import os
from pathlib import Path
import subprocess
import tempfile
import uuid


def main():
    temporary = Path(os.environ["TMPDIR"])
    stats = temporary / "ccache-stats.log"
    compiler = os.environ["CXX"]
    cookie = uuid.uuid4().hex
    with tempfile.TemporaryDirectory(dir=temporary) as directory:
        root = Path(directory)
        source, header, obj, binary = (root / p for p in ("main.cpp", "value.h", "main.o", "main"))
        original = ('#include <cstdio>\n#include "value.h"\n'
                    '#ifndef OFFSET\n#define OFFSET 0\n#endif\n'
                    '#ifndef WRAPPER_VALUE\n#define WRAPPER_VALUE 0\n#endif\n'
                    f'int main() {{ std::printf("{cookie}:%d", VALUE + OFFSET + WRAPPER_VALUE); }}\n')
        source.write_text(original)
        header.write_text("#define VALUE 1\n")

        def counters():
            return Counter(stats.read_text().splitlines()) if stats.exists() else Counter()

        def compile_case(name, expected, hit=False, offset=0, extra_env=None):
            before = counters()
            obj.unlink(missing_ok=True)
            env = os.environ | (extra_env or {})
            subprocess.run([compiler, "-std=c++17", "-O2", f"-DOFFSET={offset}",
                            "-c", str(source), "-o", str(obj)], env=env, check=True)
            delta = counters() - before
            hits = delta["direct_cache_hit"] + delta["preprocessed_cache_hit"]
            assert bool(hits) == hit, (name, delta)
            assert delta["cache_miss"] == (0 if hit else 1), (name, delta)
            subprocess.run([compiler, str(obj), "-o", str(binary)], check=True)
            assert subprocess.check_output([binary], text=True) == f"{cookie}:{expected}", name
            print(f"{name}: passed ({'hit' if hit else 'miss'})", flush=True)

        compile_case("initial compilation", 1)
        compile_case("unchanged input", 1, hit=True)
        header.write_text("#define VALUE 2\n")
        compile_case("changed header", 2)
        source.write_text(original.replace("VALUE + OFFSET", "VALUE + OFFSET + 1"))
        compile_case("changed source", 3)
        compile_case("changed compiler flag", 6, offset=3)
        source.write_text(original)
        header.write_text("#define VALUE 1\n")
        # Flags added inside the Nix wrapper must reach ccache's input hash.
        variable = "NIX_CFLAGS_COMPILE_x86_64_unknown_linux_gnu"
        compile_case("changed Nix wrapper flag", 8,
                     extra_env={variable: os.environ.get(variable, "") + " -DWRAPPER_VALUE=7"})
        compile_case("restored input", 1, hit=True)
        source.write_text("#error invalidation control\n")
        obj.unlink()
        invalid = subprocess.run([compiler, "-c", str(source), "-o", str(obj)], capture_output=True)
        assert invalid.returncode != 0 and not obj.exists(), "invalid source reused an old object"
        print("invalid source: rejected; 8 cache controls passed", flush=True)


if __name__ == "__main__":
    main()
