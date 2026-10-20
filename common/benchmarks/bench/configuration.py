"""Implementation-setting adapters shared by candidate scheduling and evidence."""
from .io import require

# Default, non-default CLI flag; semantic/security choices are not candidates.
SETTINGS = {
    'simplify': (True, '--no-simplify'),
    'finite-bulk': (True, '--no-finite-bulk'),
    'release-storage': (False, '--release-storage'),
    'fuse-vector-reductions': (False, '--fuse-vector-reductions'),
    'fuse-collect-fold': (False, '--fuse-collect-fold'),
    'calculation-batching': (True, '--no-calculation-batching'),
}


def flags(values):
    require(isinstance(values, dict) and values.keys() == SETTINGS.keys()
            and all(type(v) is bool for v in values.values()), 'invalid configuration settings')
    return [flag for name, (default, flag) in SETTINGS.items() if values[name] != default]


def validate_published(options, configuration):
    if configuration is None:
        return
    require(isinstance(options, dict) and options == {k.replace('-', '_'):v
            for k,v in configuration['values'].items()},
            'published policy differs from candidate settings (check the workload root build settings)')
