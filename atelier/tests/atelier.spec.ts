import { expect, test } from '@playwright/test';

/**
 * Smoke spec for the atelier app.
 *
 * The gallery lists every icon, renders both plates, shows the real ratchet
 * figures on the stats sheet, and mounts the scenes — with zero console
 * errors on load.
 */

const ICON_SLUGS = [
  'isolate',
  'pointer-tagging',
  'hidden-classes',
  'parser',
  'ignition',
  'old-space',
  'new-space',
  'ratchet',
] as const;

/**
 * Collects console errors AND warnings.
 *
 * React's key warnings and hydration mismatches surface as `console.warn`, not
 * `console.error`, so a handler that watches only for errors would pass while
 * the app was quietly misbehaving. Both are collected here, and the assertions
 * below require the array to be empty.
 */
function collectConsoleProblems(page: import('@playwright/test').Page): string[] {
  const problems: string[] = [];
  page.on('console', (message) => {
    if (message.type() === 'error' || message.type() === 'warning') {
      problems.push(`${message.type()}: ${message.text()}`);
    }
  });
  page.on('pageerror', (error) => {
    problems.push(`pageerror: ${error.message}`);
  });
  return problems;
}

/**
 * Messages that come from the environment rather than the application.
 *
 * The headless browser rasterises WebGL in software, and the driver reports
 * its own performance notes ("GPU stall due to ReadPixels"). Vite's dev-server
 * notices and the React DevTools banner are likewise informational. None of
 * them say anything about this code, and none of them should fail a build.
 */
const ENVIRONMENTAL = /GL Driver Message|GPU stall|\[vite\]|React DevTools/i;

function unexpectedProblems(problems: string[]): string[] {
  return problems.filter((problem) => !ENVIRONMENTAL.test(problem));
}

test('the atelier app boots with no console errors', async ({ page }) => {
  const problems = collectConsoleProblems(page);

  await page.goto('/');
  await expect(page.getByTestId('atelier-root')).toBeVisible();
  await expect(page.getByTestId('gallery-root')).toBeVisible();
  await page.waitForTimeout(500);

  expect(unexpectedProblems(problems)).toEqual([]);
});

test('the gallery nav renders every section', async ({ page }) => {
  await page.goto('/');

  const nav = page.getByTestId('gallery-nav');
  await expect(nav).toBeVisible();
  await expect(nav).toHaveAttribute('role', 'tablist');
  await expect(nav.getByRole('tab')).toHaveCount(4);

  // The board stylesheet uppercases the labels, so match case-insensitively.
  for (const name of [/icons/i, /plates/i, /stats/i, /scenes/i]) {
    await expect(nav.getByRole('tab', { name })).toBeVisible();
  }
});

test('the gallery lists every icon', async ({ page }) => {
  await page.goto('/');

  await expect(page.getByTestId('icon-sheet')).toBeVisible();
  for (const slug of ICON_SLUGS) {
    await expect(page.getByTestId(`icon-${slug}`)).toBeVisible();
  }

  // Every icon is shown twice: annotated and large, unannotated and small.
  await expect(page.locator('[data-testid="icon-sheet"] svg')).toHaveCount(
    ICON_SLUGS.length * 2,
  );
});

test('the plates render', async ({ page }) => {
  await page.goto('/');
  await page.getByRole('tab', { name: /plates/i }).click();

  await expect(page.getByTestId('plate-sheet')).toBeVisible();
  await expect(page.getByTestId('plate-v8-core')).toBeVisible();
  await expect(page.getByTestId('plate-kernel-renderer')).toBeVisible();
  await expect(page.getByTestId('plate-v8-core').locator('svg')).toBeVisible();
});

test('the stats sheet shows real values', async ({ page }) => {
  await page.goto('/');
  await page.getByRole('tab', { name: /stats/i }).click();

  const sheet = page.getByTestId('stats-sheet');
  await expect(sheet).toBeVisible();

  // The ratchet counter carries the trusted-item count the reports record.
  const counter = page.getByTestId('ratchet-counter');
  await expect(counter).toBeVisible();
  await expect(counter).toHaveAttribute('data-trusted', '0');
  await expect(counter).toHaveAttribute('data-settled', 'true');

  // Real figures, read from browser/ratchet.json and data/stats.json.
  await expect(sheet).toContainText('4,102');
  await expect(sheet).toContainText('2,354');

  // A field the reports do not carry reads "not recorded", never a zero.
  await expect(sheet).toContainText('not recorded');
});

test('the scenes mount', async ({ page }) => {
  const problems = collectConsoleProblems(page);

  await page.goto('/');
  await page.getByRole('tab', { name: /scenes/i }).click();

  await expect(page.getByTestId('scene-sheet')).toBeVisible();
  await expect(page.getByTestId('gc-heap-scene').first()).toBeVisible();
  await expect(page.getByTestId('pratt-parser-scene')).toBeVisible();
  await expect(page.getByTestId('tri-color-gc-scene')).toBeVisible();

  // Both step-through scenes expose their step metadata.
  await expect(page.getByTestId('stepper').first()).toHaveAttribute('data-step-count', /\d+/);

  // The WebGL scene starts without logging an error.
  await expect(page.getByTestId('gc-heap-status').first()).toContainText('BARRIER');
  expect(unexpectedProblems(problems)).toEqual([]);
});

test('the gallery stays clean across every tab', async ({ page }) => {
  const problems = collectConsoleProblems(page);

  await page.goto('/');
  for (const name of [/icons/i, /plates/i, /stats/i, /scenes/i]) {
    await page.getByRole('tab', { name }).click();
    await page.waitForTimeout(350);
  }

  // Environmental noise is filtered out; everything else — errors, warnings,
  // hydration mismatches, key warnings — must be silent.
  expect(unexpectedProblems(problems)).toEqual([]);
});
