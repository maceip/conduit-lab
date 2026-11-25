import React from 'react';

interface IconProps {
  size?: number;
  className?: string;
}

const base = (size: number, className?: string) => ({
  width: size,
  height: size,
  viewBox: '0 0 16 16',
  fill: 'none',
  stroke: 'currentColor',
  strokeWidth: 1.6,
  strokeLinecap: 'round' as const,
  strokeLinejoin: 'round' as const,
  'aria-hidden': true as const,
  className,
});

export const IconCheck: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M5.2 8.2 7.1 10.1 11 6.1" />
  </svg>
);

export const IconX: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M5.7 5.7 10.3 10.3M10.3 5.7 5.7 10.3" />
  </svg>
);

export const IconClock: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M8 4.7V8l2.4 1.5" />
  </svg>
);

export const IconShieldAlert: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M8 1.8 13.5 4v3.8c0 3.2-2.2 5.4-5.5 6.4C4.7 13.2 2.5 11 2.5 7.8V4L8 1.8Z" />
    <path d="M8 5.4v3.2M8 11.1h.01" />
  </svg>
);

export const IconCopy: React.FC<IconProps> = ({ size = 13, className }) => (
  <svg {...base(size, className)}>
    <rect x="5.5" y="5.5" width="8" height="8" rx="1.5" />
    <path d="M10.5 5.5V3.8A1.3 1.3 0 0 0 9.2 2.5H3.8A1.3 1.3 0 0 0 2.5 3.8v5.4a1.3 1.3 0 0 0 1.3 1.3h1.7" />
  </svg>
);

export const IconExternal: React.FC<IconProps> = ({ size = 12, className }) => (
  <svg {...base(size, className)}>
    <path d="M6.5 3.5H3.5a1 1 0 0 0-1 1v8a1 1 0 0 0 1 1h8a1 1 0 0 0 1-1v-3" />
    <path d="M9.2 2.5h4.3v4.3M13.5 2.5 7.5 8.5" />
  </svg>
);

export const IconChevron: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M6 4.2 10 8l-4 3.8" />
  </svg>
);

export const IconArrowDown: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M8 2.5v10.5M4.5 9.5 8 13l3.5-3.5" />
  </svg>
);

export const IconArrowRight: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M2.5 8h10.5M9.5 4.5 13 8l-3.5 3.5" />
  </svg>
);

export const IconGitHub: React.FC<IconProps> = ({ size = 16, className }) => (
  <svg
    width={size}
    height={size}
    viewBox="0 0 16 16"
    fill="currentColor"
    aria-hidden="true"
    className={className}
  >
    <path d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27s1.36.09 2 .27c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0 0 16 8c0-4.42-3.58-8-8-8Z" />
  </svg>
);

const CONDUIT_STENCIL_GLYPHS = [
  // C — semicircular arc with sheared terminals
  'M 46.5 0.0 H 131.2 L 121.9 18.4 H 46.5 C 29.5 18.4 18.3 31.2 18.3 50.0 C 18.3 68.8 29.5 81.6 46.5 81.6 H 121.9 L 131.2 100.0 H 46.5 C 18.2 100.0 0.0 80.5 0.0 50.0 C 0.0 19.5 18.2 0.0 46.5 0.0 Z',
  // Ø — stadium ring with optically crisp 45° stencil channels + stepped central laser spindle
  'M 254.4 2.6 L 239.6 16.4 H 170.5 C 160.8 16.4 155.1 22.2 155.1 31.5 V 68.5 C 155.1 76.4 158.4 81.4 163.6 83.4 L 150.6 96.0 C 142.4 90.5 138.65 81.4 138.65 69.5 V 30.5 C 138.65 11.8 149.8 0.0 168.5 0.0 H 244.8 C 248.6 0.0 251.8 0.9 254.4 2.6 Z M 262.4 6.0 C 270.4 11.6 274.45 20.2 274.45 30.5 V 69.5 C 274.45 88.2 263.3 100.0 244.6 100.0 H 168.5 C 164.6 100.0 161.1 99.2 158.2 97.9 L 172.0 83.6 H 242.6 C 252.3 83.6 258.1 77.8 258.1 68.5 V 31.5 C 258.1 23.5 254.9 18.4 249.4 16.6 Z M 237.8 15.8 L 241.6 15.8 L 173.8 84.0 L 169.8 84.0 Z M 226.8 25.8 L 234.4 25.8 L 191.2 69.2 L 183.6 69.2 Z',
  // N — isolated left pillar + crisp stencil gap + vertical-cut diagonal + right stem
  'M 290.2 0.0 H 309.8 V 100.0 H 290.2 Z M 314.8 1.8 L 396.35 71.6 V 0.0 H 416.1 V 100.0 H 395.6 L 314.8 31.2 Z',
  // D — continuous rounded-right loop with open left-stem stencil slot
  'M 433.2 0.0 H 520.5 C 539.2 0.0 550.2 11.8 550.2 30.5 V 69.5 C 550.2 88.2 539.2 100.0 520.5 100.0 H 433.2 V 43.8 H 451.85 V 81.2 H 518.0 C 526.6 81.2 531.45 76.2 531.45 67.6 V 32.4 C 531.45 23.8 526.6 18.4 518.0 18.4 H 451.85 V 25.2 H 433.2 Z',
  // U — twin vertical stems into flat-bottomed stadium arc
  'M 565.85 0.0 H 584.5 V 68.0 C 584.5 76.6 589.5 81.3 598.2 81.3 H 634.5 C 643.2 81.3 648.25 76.6 648.25 68.0 V 0.0 H 666.85 V 69.5 C 666.85 88.2 655.8 100.0 637.0 100.0 H 595.7 C 576.9 100.0 565.85 88.2 565.85 69.5 Z',
  // I — solid pillar
  'M 684.0 0.0 H 702.65 V 100.0 H 684.0 Z',
  // T — sheared top crossbar + centered stem
  'M 718.6 0.0 H 806.2 L 799.1 18.4 H 769.65 V 100.0 H 751.15 V 18.4 H 724.6 Z',
];

export const ConduitWordmark: React.FC<{ className?: string; testId?: string }> = ({
  className,
  testId = 'brand-conduit-wordmark',
}) => {
  const uid = React.useId().replace(/:/g, '');
  const gradId = `ch-wordmark-grad-${uid}`;
  const sheenId = `ch-wordmark-sheen-${uid}`;
  return (
    <svg
      viewBox="0 0 806.2 100"
      role="img"
      aria-label="CONDUIT"
      data-testid={testId}
      className={className ? `ch-brand-wordmark ${className}` : 'ch-brand-wordmark'}
    >
      <defs>
        <linearGradient id={gradId} x1="0%" y1="0%" x2="0%" y2="100%">
          <stop offset="0%" stopColor="var(--ch-wordmark-hi)" />
          <stop offset="46%" stopColor="var(--ch-wordmark-mid)" />
          <stop offset="100%" stopColor="var(--ch-wordmark-lo)" />
        </linearGradient>
        <linearGradient id={sheenId} x1="0%" y1="0%" x2="52%" y2="85%">
          <stop offset="0%" stopColor="var(--ch-wordmark-flare)" stopOpacity="0.34" />
          <stop offset="48%" stopColor="var(--ch-wordmark-flare)" stopOpacity="0.09" />
          <stop offset="100%" stopColor="var(--ch-wordmark-flare)" stopOpacity="0" />
        </linearGradient>
      </defs>
      <g fill={`url(#${gradId})`}>
        {CONDUIT_STENCIL_GLYPHS.map((d, i) => (
          <path key={i} d={d} />
        ))}
      </g>
      <g fill={`url(#${sheenId})`} aria-hidden="true">
        {CONDUIT_STENCIL_GLYPHS.map((d, i) => (
          <path key={i} d={d} />
        ))}
      </g>
    </svg>
  );
};
