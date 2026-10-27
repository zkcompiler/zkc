// One ordinary module/instance per dedicated Worker. No shared memory or pool.
import { installWorker } from './worker-runtime.mjs';
installWorker(self);
