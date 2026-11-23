/**
 * Collector for the unit suites that live in `atelier/tests/`.
 *
 * `vitest.config.ts` collects `src/**` only, so the three unit suites in
 * `atelier/tests/` are not picked up by the run on their own. This file
 * imports them so `npm run test:strict` actually executes them.
 *
 * If `include` in `vitest.config.ts` is ever widened to cover `tests/**`,
 * delete this file — otherwise the suites would be collected twice.
 */
import '../../tests/illustration.test';
import '../../tests/stats.test';
import '../../tests/scene.test';
