import { create } from 'zustand';
import { PALETTES, setPalette, type Theme } from './scene/ink';

/**
 * Paper (ink on cream), blueprint (cyanotype), or obsidian (CONDUIT dark plate).
 * Query parameter ?theme=dark|light|obsidian|paper|blueprint and postMessage
 * { type: 'conduit-theme', theme: 'dark' | 'light' } keep embedded plates synced.
 */

const KEY = 'gewu-theme';

function mapExternalTheme(raw: string | null): Theme | null {
  if (raw === 'dark' || raw === 'obsidian') return 'obsidian';
  if (raw === 'light' || raw === 'paper') return 'paper';
  if (raw === 'blueprint') return 'blueprint';
  return null;
}

function initial(): Theme {
  if (typeof window !== 'undefined') {
    const qp = mapExternalTheme(new URLSearchParams(window.location.search).get('theme'));
    if (qp) return qp;
    try {
      const saved = window.localStorage.getItem(KEY);
      if (saved === 'paper' || saved === 'blueprint' || saved === 'obsidian') return saved;
    } catch { /* private mode */ }
    return window.matchMedia?.('(prefers-color-scheme: dark)').matches ? 'obsidian' : 'paper';
  }
  return 'paper';
}

function apply(theme: Theme) {
  if (typeof document === 'undefined') return;
  document.documentElement.dataset.theme = theme;
  document.querySelector('meta[name="theme-color"]')?.setAttribute('content', PALETTES[theme].paper);
  setPalette(PALETTES[theme]);
}

export const useTheme = create<{ theme: Theme; set: (theme: Theme) => void }>((set) => ({
  theme: initial(),
  set: (theme) => {
    try { window.localStorage.setItem(KEY, theme); } catch { /* private mode */ }
    apply(theme);
    set({ theme });
  },
}));

apply(useTheme.getState().theme);

if (typeof window !== 'undefined') {
  window.addEventListener('message', (ev: MessageEvent) => {
    const data = ev.data as { type?: string; theme?: string } | null;
    if (data?.type === 'conduit-theme') {
      const next = mapExternalTheme(data.theme ?? null);
      if (next) useTheme.getState().set(next);
    }
  });
}
