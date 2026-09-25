"""Explicit dense public MSM identity; mathematical admission is not a role grant."""
import json
from pathlib import Path
from commands import Commands
from tools import records

source = '''module {
  bind msm = curve::msm(ristretto255.group);
  fn Fold(w: Vector<"ristretto255.scalar"::Element>, p: Vector<"ristretto255.group"::Element>)
      -> ("ristretto255.group"::Element) {
    [multiply] let q = msm(w, p);
    return (q);
  }
  protocol Computation {
    roles (P, V);
    inputs (V w: Vector<"ristretto255.scalar"::Element>, V p: Vector<"ristretto255.group"::Element>);
    outputs (V "ristretto255.group"::Element);
    local [fold] V: let q = Fold(w, p);
    return (q);
  }
  instance root: Computation { roles (P = P, V = V); }
  entry main = root;
}'''

directory = records()
commands = Commands(directory)
run = commands.source
selection = Path(directory) / 'selection.json'
selection.write_text(json.dumps([['msm', 'dalek-vartime/curve.msm']]))
plain = json.loads(run('protocol-compile', source))
public = json.loads(run('protocol-compile', source, '--implementations='+str(selection)))
assert plain[1][0][3] == 'dalek/curve.msm'
assert public[1][0][3] == 'dalek-vartime/curve.msm'
public[1][0][3] = plain[1][0][3]
assert public == plain  # Only the installed physical implementation changes.
run('protocol-compile', source.replace('ristretto255.group','bls12-381.g1').replace('ristretto255.scalar','bls12-381.fr'), '--implementations='+str(selection), refuses='binding-implementation')
logical = json.loads(run('protocol-source', source))
logical[1][0][1] = 'curve.scale_each'
logical[1][0][3] = 'dalek-vartime/curve.msm'
run('protocol-source', json.dumps(logical), refuses='binding-implementation')
print(f'public MSM: {commands.save()} compiler controls passed')
