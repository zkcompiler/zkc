"""Implementation-setting adapters shared by candidate scheduling and evidence."""
from .io import require
from .oracle_policy import OraclePolicy, validate_selection

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


def validate_candidate(configuration):
    require(isinstance(configuration, dict)
            and set(configuration) == {'profile', 'values', 'origins', 'oracle_realization'},
            'invalid build configuration')
    require(isinstance(configuration['profile'], str) and configuration['profile'], 'invalid configuration profile')
    flags(configuration['values'])
    require(configuration['oracle_realization'] == OraclePolicy().selection(),
            'benchmark optimization profiles must leave oracle realization at the default; workloads select authentication')
    require(isinstance(configuration['origins'], dict)
            and configuration['origins'].keys() == SETTINGS.keys() | {'oracle-realization'}
            and all(isinstance(v, str) and v for v in configuration['origins'].values()),
            'invalid configuration origins')


def validate_published(options, configuration, oracle_policy=OraclePolicy(), *, compiler_options=None):
    names = {k.replace('-', '_') for k in SETTINGS}
    require(isinstance(options, dict) and options.keys() == names | {'oracle_realization'}
            and all(type(options[k]) is bool for k in names), 'invalid published compiler options')
    validate_selection(options, oracle_policy)
    if compiler_options is not None:
        require(isinstance(compiler_options, list)
                and all(option in {flag for _, flag in SETTINGS.values()} for option in compiler_options),
                'invalid generated compiler options')
        require({k: options[k] for k in names} == {name.replace('-', '_'):
                (not default if flag in compiler_options else default)
                for name, (default, flag) in SETTINGS.items()},
                'published optimization options differ from the generated workload request')
    if configuration is None:
        return
    validate_candidate(configuration)
    require({k: options[k] for k in names} == {k.replace('-', '_'):v
            for k,v in configuration['values'].items()},
            'published policy differs from candidate settings (check the workload root build settings)')
