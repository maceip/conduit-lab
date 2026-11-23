import { expect, test } from '@playwright/test';

/**
 * The reduced-motion path.
 *
 * `prefers-reduced-motion: reduce` must render the final state instantly,
 * with no intermediate animation. The counter settles on its first paint and
 * nothing on the board is left mid-animation.
 */
test.use({ reducedMotion: 'reduce' });

test('reduced motion renders the ratchet counter settled immediately', async ({ page }) => {
  await page.goto('/');
  await page.getByRole('tab', { name: /stats/i }).click();

  const counter = page.getByTestId('ratchet-counter');
  await expect(counter).toBeVisible();
  await expect(counter).toHaveAttribute('data-settled', 'true');
  await expect(counter).toHaveAttribute('data-trusted', '0');
});

test('reduced motion leaves nothing mid-animation', async ({ page }) => {
  await page.goto('/');
  await page.getByRole('tab', { name: /stats/i }).click();

  const moving = await page.evaluate(() => {
    const toSeconds = (value: string): number =>
      value
        .split(',')
        .map((part) => {
          const parsed = Number.parseFloat(part);
          if (!Number.isFinite(parsed)) return 0;
          return part.includes('ms') ? parsed / 1000 : parsed;
        })
        .reduce((longest, seconds) => Math.max(longest, seconds), 0);

    return Array.from(document.querySelectorAll('*')).filter((node) => {
      const style = getComputedStyle(node);
      const animation =
        style.animationName === 'none' ? 0 : toSeconds(style.animationDuration);
      const transition = toSeconds(style.transitionDuration);
      return animation > 0.05 || transition > 0.05;
    }).length;
  });

  expect(moving).toBe(0);
});

test('reduced motion settles the counted figures too', async ({ page }) => {
  await page.goto('/');
  await page.getByRole('tab', { name: /stats/i }).click();

  const settled = page.locator('[data-settled="true"]');
  await expect(settled.first()).toBeVisible();
  await expect(page.locator('[data-settled="false"]')).toHaveCount(0);
});
