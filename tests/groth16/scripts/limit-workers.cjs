// Resource limit only; does not modify any snarkjs or verifier source.
const os = require('node:os');
const cpus = os.cpus.bind(os);
os.cpus = () => cpus().slice(0, Number(process.env.FIXTURE_WORKERS || 4));
