import { expect, test } from '@playwright/test';

/**
 * Smoke spec for the atelier app.
 *
 * Phase A covers the shell only: the app boots cleanly and the gallery nav
 * renders. Assertions about the icons, plates, stats and scene components
 * arrive with Phase B, when the gallery mounts the sheets.
 */

test('the atelier app boots with no console errors', async ({ page }) => {
  const errors: string[] = [];
  page.on('console', (message) => {
    if (message.type() === 'error') errors.push(message.text());
  });
  page.on('pageerror', (error) => {
    errors.push(error.message);
  });

  await page.goto('/');
  await expect(page.getByTestId('atelier-root')).toBeVisible();
  await page.waitForTimeout(500);

  expect(errors).toEqual([]);
});

test('the gallery nav renders every section', async ({ page }) => {
  await page.goto('/');

  const nav = page.getByTestId('gallery-nav');
  await expect(nav).toBeVisible();
  await expect(nav).toHaveAttribute('role', 'tablist');

  const tabs = nav.getByRole('tab');
  await expect(tabs).toHaveCount(4);

  // The board stylesheet uppercases the labels, so match case-insensitively.
  for (const name of [/icons/i, /plates/i, /stats/i, /scenes/i]) {
    await expect(nav.getByRole('tab', { name })).toBeVisible();
  }
});
