import { expect, test } from '@playwright/test';
test('final visual check', async ({ page }) => {
  await page.setViewportSize({ width: 1440, height: 1000 });
  await page.goto('/');
  await page.waitForTimeout(700);
  await page.getByRole('tab', { name: /stats/i }).click();
  await page.waitForTimeout(900);
  await page.screenshot({ path: '/tmp/final-stats.png' });
  await page.getByRole('tab', { name: /scenes/i }).click();
  await expect(page.getByTestId('scene-sheet')).toBeVisible();
  await page.waitForTimeout(1800);
  await page.screenshot({ path: '/tmp/final-scenes.png' });
  expect(true).toBe(true);
});
