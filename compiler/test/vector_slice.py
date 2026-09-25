"""Dynamic slicing stays typed, generic and visible through physical planning."""

import json
from pathlib import Path
from cases import case
from commands import Commands
from tools import compiler, records

fields = ["bls12-381.fr", "bn254.fr", "ristretto255.scalar", "koala-bear", "koala-bear.ext8-binomial3"]
commands = Commands(records())
directory = commands.directory
source = Path(directory) / "slice.pir"
for field in fields:
    with case(f"vector slice over {field}"):
        source.write_text('''module {
          fn Slice<F: domain Field>(a: Vector<F::Element>, start: index, length: index)
              -> Vector<F::Element> requires (Field(F)) {
            let result = vector::slice::<F>(a, start, length);
            return result;
          }
          configure Concrete = Slice(F = FIELD);
          protocol Main {
            roles (P);
            inputs (P a: Vector<"FIELD"::Element>, P start: index, P length: index);
            outputs (P Vector<"FIELD"::Element>);
            local P: let sliced = Concrete(a, start, length);
            return sliced;
          }
          instance concrete: Main { roles (P = P); }
          entry main = concrete;
        }'''.replace("FIELD", field))
        printed = commands.run([compiler, "protocol-compile", source])
        physical = json.loads(printed)
        assert "vector.slice" in printed and field in printed
        assert physical[0] == "zkc.participants/1"
        source.write_text(source.read_text().replace("a, start, length", "a, a, length"))
        # A field vector where an index belongs is a source type error.
        commands.run([compiler, "protocol-compile", source], refuses="source-type-mismatch")
print(f"{commands.save()} generic vector slice compilation controls passed")
